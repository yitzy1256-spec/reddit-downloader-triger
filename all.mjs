import dotenv from "dotenv";
dotenv.config();

import Imap from "imap";
import { simpleParser } from "mailparser";
import nodemailer from "nodemailer";
import axios from "axios";
import { execFile } from "child_process";
import { promisify } from "util";
import * as fs from "fs";
import * as path from "path";
import { fileURLToPath } from "url";
import crypto from "crypto";
import limit from "p-limit";
import express from "express";
const app = express();

// This is the endpoint Cloudflare Worker will call
app.get("/run", async (req, res) => {
  console.log("Triggered at", new Date());

const execFileAsync = promisify(execFile);
const __dirname = path.dirname(fileURLToPath(import.meta.url));

// Configuration
const GMAIL_USER = process.env.GMAIL_USER;
const GMAIL_APP_PASSWORD = process.env.GMAIL_APP_PASSWORD;
const SMTP_USER = process.env.SMTP_USER || GMAIL_USER;
const SMTP_PASSWORD = process.env.SMTP_PASSWORD || GMAIL_APP_PASSWORD;

// Email size limit (20MB to be safe)
const EMAIL_SIZE_LIMIT = 25 * 1024 * 1024;

// Check interval (1 minute)
const CHECK_INTERVAL = 60000;

// Concurrent download limit
const CONCURRENT_DOWNLOADS = 3;
const downloadLimiter = limit(CONCURRENT_DOWNLOADS);

// Tracking file path
const TRACKING_FILE = path.join(__dirname, "reddit_tracker.json");
const TEMP_DIR = path.join(__dirname, ".temp");

// Automation state
let isProcessing = false;
let imapConnected = false;
let tempFilesCreated = [];

// User agents for rotation
const USER_AGENTS = [
  "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
  "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
  "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
  "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:123.0) Gecko/20100101 Firefox/123.0"
];

function getRandomUserAgent() {
  return USER_AGENTS[Math.floor(Math.random() * USER_AGENTS.length)];
}

// IMAP Configuration
const imap = new Imap({
  user: GMAIL_USER,
  password: GMAIL_APP_PASSWORD,
  host: "imap.gmail.com",
  port: 993,
  tls: true,
  tlsOptions: { rejectUnauthorized: false }
});

// Nodemailer Configuration
const transporter = nodemailer.createTransport({
  service: "gmail",
  auth: {
    user: SMTP_USER,
    pass: SMTP_PASSWORD
  }
});

// ==================== UTILITY FUNCTIONS ====================

function ensureTempDir() {
  if (!fs.existsSync(TEMP_DIR)) {
    fs.mkdirSync(TEMP_DIR, { recursive: true });
  }
}

function getTempFilePath(filename) {
  const filepath = path.join(TEMP_DIR, filename);
  tempFilesCreated.push(filepath);
  return filepath;
}

function cleanupFile(filepath) {
  try {
    if (filepath && fs.existsSync(filepath)) {
      fs.unlinkSync(filepath);
    }
  } catch (error) {
    console.error(`⚠️  Could not delete ${path.basename(filepath)}: ${error.message}`);
  }
}

function cleanupTempFiles() {
  console.log("🧹 Cleaning up temporary files...");
  
  // Get unique files
  const uniqueFiles = [...new Set(tempFilesCreated)];
  
  for (const file of uniqueFiles) {
    cleanupFile(file);
  }
  
  tempFilesCreated = [];

  // Try to remove temp directory if empty
  try {
    if (fs.existsSync(TEMP_DIR)) {
      const files = fs.readdirSync(TEMP_DIR);
      if (files.length === 0) {
        fs.rmdirSync(TEMP_DIR);
        console.log("✓ Temp directory removed");
      }
    }
  } catch (error) {
    // Directory not empty or other error - that's ok
  }
}

// ==================== TRACKING FUNCTIONS ====================

function initializeTracking() {
  if (!fs.existsSync(TRACKING_FILE)) {
    const trackingData = {
      subreddits: {},
      lastUpdated: new Date().toISOString()
    };
    fs.writeFileSync(TRACKING_FILE, JSON.stringify(trackingData, null, 2));
    console.log(`✓ Created tracking file: ${TRACKING_FILE}`);
  }
}

function loadTracking() {
  try {
    if (fs.existsSync(TRACKING_FILE)) {
      const data = fs.readFileSync(TRACKING_FILE, "utf-8");
      return JSON.parse(data);
    }
  } catch (error) {
    console.error("Error loading tracking file:", error.message);
  }
  return { subreddits: {}, lastUpdated: new Date().toISOString() };
}

function saveTracking(trackingData) {
  try {
    fs.writeFileSync(TRACKING_FILE, JSON.stringify(trackingData, null, 2));
  } catch (error) {
    console.error("Error saving tracking file:", error.message);
  }
}

function getSubredditTracking(subreddit) {
  const tracking = loadTracking();
  if (!tracking.subreddits[subreddit]) {
    tracking.subreddits[subreddit] = {
      sentPostIds: [],
      lastSentDate: null,
      totalSent: 0
    };
  }
  return tracking.subreddits[subreddit];
}

function hasBeenSent(subreddit, postId) {
  const tracking = getSubredditTracking(subreddit);
  return tracking.sentPostIds.includes(postId);
}

function extractPostIdFromLink(link) {
  const parts = link.split("/");
  const commentsIndex = parts.indexOf("comments");
  if (commentsIndex !== -1 && parts[commentsIndex + 1]) {
    return parts[commentsIndex + 1];
  }
  
  return crypto.createHash('md5').update(link).digest('hex').substring(0, 8);
}

function updateSubredditTracking(subreddit, postIds) {
  const tracking = loadTracking();
  
  if (!tracking.subreddits[subreddit]) {
    tracking.subreddits[subreddit] = {
      sentPostIds: [],
      lastSentDate: null,
      totalSent: 0
    };
  }

  const subTracking = tracking.subreddits[subreddit];
  
  const newIds = postIds.filter(id => !subTracking.sentPostIds.includes(id));
  subTracking.sentPostIds = [...subTracking.sentPostIds, ...newIds].slice(-1000);
  
  subTracking.lastSentDate = new Date().toISOString();
  subTracking.totalSent = (subTracking.totalSent || 0) + newIds.length;

  tracking.lastUpdated = new Date().toISOString();
  saveTracking(tracking);

  if (newIds.length > 0) {
    console.log(`✓ Updated tracking for r/${subreddit}: ${newIds.length} new post(s) sent (Total: ${subTracking.totalSent})`);
  }
}

// ==================== IMAP FUNCTIONS ====================

function openBoxAsync(boxName) {
  return new Promise((resolve, reject) => {
    imap.openBox(boxName, false, (err, box) => {
      if (err) reject(err);
      else resolve(box);
    });
  });
}

function closeBoxAsync() {
  return new Promise((resolve, reject) => {
    imap.closeBox(false, (err) => {
      if (err) reject(err);
      else resolve();
    });
  });
}

function searchAsync(criteria) {
  return new Promise((resolve, reject) => {
    imap.search(criteria, (err, results) => {
      if (err) reject(err);
      else resolve(results || []);
    });
  });
}

async function checkRedditLabel() {
  try {
    await openBoxAsync("Reddit");

    try {
      const results = await searchAsync(["ALL"]);

      if (results.length === 0) {
        console.log("No emails in Reddit label");
        return;
      }

      console.log(`Found ${results.length} emails to process`);

      const f = imap.fetch(results, { bodies: "" });

      let messageCount = 0;
      let processedCount = 0;
      const messagePromises = [];
      const idsToDelete = [];

      f.on("message", (msg, seqno) => {
        messageCount++;
        const promise = new Promise((msgResolve) => {
          let messageUid = null;

          msg.on("attributes", (attrs) => {
            messageUid = attrs.uid;
          });

          msg.on("body", async (stream) => {
            try {
              const parsed = await simpleParser(stream);
              const deleteUid = await processMessage(parsed, messageUid);
              if (deleteUid !== null) {
                idsToDelete.push(deleteUid);
              }
              processedCount++;
            } catch (error) {
              console.error("Error processing message:", error.message);
            }
            msgResolve();
          });

          msg.on("error", (err) => {
            console.error("Message error:", err.message);
            msgResolve();
          });
        });
        messagePromises.push(promise);
      });

      f.on("error", (err) => {
        console.error("Fetch error:", err);
        throw err;
      });

      await new Promise((resolve, reject) => {
        f.on("end", () => resolve());
        f.on("error", reject);
      });

      await Promise.all(messagePromises);
      console.log(`Processed ${processedCount}/${messageCount} messages successfully`);

      // ✅ Call deleteEmailsAsync BEFORE closing the mailbox
      if (idsToDelete.length > 0) {
        await deleteEmailsAsync(idsToDelete);
      }

    } finally {
      await closeBoxAsync();
      console.log("✓ Mailbox closed");
    }
  } catch (error) {
    console.error("Error in checkRedditLabel:", error.message);
    try {
      await closeBoxAsync();
    } catch (e) {
      // ignore
    }
  }
}

async function deleteEmailsAsync(ids) {
  return new Promise((resolve, reject) => {
    if (!ids || ids.length === 0) {
      console.log("✓ No emails to delete");
      resolve();
      return;
    }

    console.log(`\n🗑️  Moving ${ids.length} email(s) to trash...`);
    console.log(`UIDs to delete: ${ids.join(", ")}`);

    // ✅ FIX: Format UIDs as comma-separated string
    const idString = ids.join(",");

    // Step 1: Copy to Trash
    imap.copy(idString, "[Gmail]/Trash", (copyErr) => {
      if (copyErr) {
        console.error("❌ Copy failed:", copyErr.message);
        reject(copyErr);
        return;
      }

      console.log(`✓ Step 1/2: Copied to [Gmail]/Trash`);

      // Step 2: Mark as Deleted
      imap.addFlags(idString, "\\Deleted", (flagErr) => {
        if (flagErr) {
          console.error("❌ Flag failed:", flagErr.message);
          reject(flagErr);
          return;
        }

        console.log(`✓ Step 2/2: Marked as deleted`);
        console.log(`✓ ${ids.length} email(s) removed from Reddit label`);
        resolve();
      });
    });
  });
}

function sanitizeFilename(filename) {
  return filename
    .replace(/[^a-zA-Z0-9\s\-_]/g, "")
    .replace(/\s+/g, "_")
    .substring(0, 200);
}

async function processMessage(parsed, messageUid) {
  try {
    const body = parsed.text || "";
    console.log("Processing email with body:", body.substring(0, 100));

    let subreddit = null;
    let mediaTypeFilter = null;
    let postCount = 1;

    let match = body.match(/r\/([A-Za-z0-9_]+)\s*(mp4|png|jpg|jpeg|gif)?\s*(\d+)?/i);
    if (match) {
      subreddit = match[1];
      mediaTypeFilter = match[2] ? match[2].toLowerCase() : null;
      postCount = match[3] ? Math.min(parseInt(match[3]), 10) : 1;
    } else {
      match = body.match(/([A-Za-z0-9_]+)\s*(mp4|png|jpg|jpeg|gif)?\s*(\d+)?/i);
      if (match) {
        subreddit = match[1];
        mediaTypeFilter = match[2] ? match[2].toLowerCase() : null;
        postCount = match[3] ? Math.min(parseInt(match[3]), 10) : 1;
      }
    }

    if (!subreddit) {
      console.log("No subreddit found in email");
      return messageUid;
    }

    console.log(`Found subreddit: ${subreddit}`);
    if (mediaTypeFilter) {
      console.log(`Media type filter: ${mediaTypeFilter}`);
    }
    console.log(`Requesting ${postCount} new post(s)`);

    const posts = await findLatestPostsRSS(subreddit, mediaTypeFilter, postCount * 10);

    if (!posts || posts.length === 0) {
      const filterMsg = mediaTypeFilter ? ` with type ${mediaTypeFilter}` : "";
      console.log("✗ No media found in r/" + subreddit + filterMsg);
      return messageUid;
    }

    console.log(`✓ Found ${posts.length} post(s) in RSS feed`);

    const attachments = [];
    const sentPostIds = [];
    let newPostsFound = 0;
    
    for (let i = 0; i < posts.length && newPostsFound < postCount; i++) {
      const post = posts[i];
      
      if (hasBeenSent(subreddit, post.id)) {
        console.log(`⊘ Skipping already sent post: ${post.title}`);
        continue;
      }

      console.log(`\nProcessing new post ${newPostsFound + 1}/${postCount}: ${post.title}`);

      const attachment = await downloadLimiter(() => downloadAndPreparePost(post));
      if (attachment) {
        attachments.push(attachment);
        sentPostIds.push(post.id);
        newPostsFound++;
      }
    }

    if (attachments.length === 0) {
      console.log("✗ Failed to download any new posts");
      return messageUid;
    }

    console.log(`\n✓ Successfully prepared ${attachments.length} new attachment(s)`);

    await sendEmailsWithAttachments(subreddit, attachments);

    updateSubredditTracking(subreddit, sentPostIds);

    return messageUid;
  } catch (error) {
    console.error("Error in processMessage:", error.message);
    return messageUid;
  }
}

// ==================== RSS & POST FUNCTIONS ====================

async function findLatestPostsRSS(subreddit, mediaTypeFilter = null, count = 1) {
  try {
    const url = `https://www.reddit.com/r/${subreddit}/new/.rss`;

    const response = await axios.get(url, {
      headers: {
        "User-Agent": getRandomUserAgent()
      },
      timeout: 10000
    });

    const xml = response.data;
    const posts = [];
    const entryRegex = /<entry>([\s\S]*?)<\/entry>/g;
    let entryMatch;

    while ((entryMatch = entryRegex.exec(xml)) !== null) {
      const entry = entryMatch[1];

      const titleMatch = entry.match(/<title>([^<]+)<\/title>/);
      const publishedMatch = entry.match(/<published>([^<]+)<\/published>/);
      const linkMatch = entry.match(/<link href="([^"]+)"/);

      if (!titleMatch) continue;

      const title = titleMatch[1]
        .replace(/&amp;/g, "&")
        .replace(/&lt;/g, "<")
        .replace(/&gt;/g, ">")
        .replace(/&quot;/g, '"')
        .replace(/&#39;/g, "'");

      const releaseDate = publishedMatch
        ? formatDate(publishedMatch[1])
        : "Unknown";

      const postLink = linkMatch ? linkMatch[1] : "";
      const postId = extractPostIdFromLink(postLink);

      const vredditMatch = entry.match(/https:\/\/v\.redd\.it\/[A-Za-z0-9]+/);
      const pngMatch = entry.match(/https:\/\/[^\s<]+\.png/i);
      const jpgMatch = entry.match(/https:\/\/[^\s<]+\.jpg/i);
      const jpegMatch = entry.match(/https:\/\/[^\s<]+\.jpeg/i);
      const gifMatch = entry.match(/https:\/\/[^\s<]+\.gif/i);

      let post = null;

      if (mediaTypeFilter === "mp4") {
        if (vredditMatch) {
          post = {
            url: vredditMatch[0],
            title: title,
            mediaType: "video",
            releaseDate: releaseDate,
            id: postId
          };
        }
      } else if (mediaTypeFilter === "png") {
        if (pngMatch) {
          post = {
            url: pngMatch[0],
            title: title,
            mediaType: "png",
            releaseDate: releaseDate,
            id: postId
          };
        }
      } else if (mediaTypeFilter === "jpg") {
        if (jpgMatch) {
          post = {
            url: jpgMatch[0],
            title: title,
            mediaType: "jpg",
            releaseDate: releaseDate,
            id: postId
          };
        }
      } else if (mediaTypeFilter === "jpeg") {
        if (jpegMatch) {
          post = {
            url: jpegMatch[0],
            title: title,
            mediaType: "jpeg",
            releaseDate: releaseDate,
            id: postId
          };
        }
      } else if (mediaTypeFilter === "gif") {
        if (gifMatch) {
          post = {
            url: gifMatch[0],
            title: title,
            mediaType: "gif",
            releaseDate: releaseDate,
            id: postId
          };
        }
      } else {
        if (vredditMatch) {
          post = {
            url: vredditMatch[0],
            title: title,
            mediaType: "video",
            releaseDate: releaseDate,
            id: postId
          };
        } else if (pngMatch) {
          post = {
            url: pngMatch[0],
            title: title,
            mediaType: "png",
            releaseDate: releaseDate,
            id: postId
          };
        } else if (jpgMatch) {
          post = {
            url: jpgMatch[0],
            title: title,
            mediaType: "jpg",
            releaseDate: releaseDate,
            id: postId
          };
        } else if (jpegMatch) {
          post = {
            url: jpegMatch[0],
            title: title,
            mediaType: "jpeg",
            releaseDate: releaseDate,
            id: postId
          };
        } else if (gifMatch) {
          post = {
            url: gifMatch[0],
            title: title,
            mediaType: "gif",
            releaseDate: releaseDate,
            id: postId
          };
        }
      }

      if (post) {
        posts.push(post);
      }
    }

    return posts.length > 0 ? posts : null;
  } catch (error) {
    console.error("Error fetching RSS:", error.message);
    return null;
  }
}

function formatDate(dateString) {
  try {
    const dateObj = new Date(dateString);
    return dateObj.toLocaleString("en-US", {
      year: "numeric",
      month: "long",
      day: "numeric",
      hour: "2-digit",
      minute: "2-digit",
      second: "2-digit",
      timeZoneName: "short"
    });
  } catch (e) {
    return dateString;
  }
}

// ==================== VIDEO FUNCTIONS ====================

async function getDashPlaylist(id) {
  try {
    const url = `https://v.redd.it/${id}/DASHPlaylist.mpd`;

    const response = await axios.get(url, {
      headers: {
        "User-Agent": getRandomUserAgent(),
        "Accept": "application/xml,text/xml,*/*;q=0.9",
        "Accept-Language": "en-US,en;q=0.9",
        "Cache-Control": "no-cache",
        "Pragma": "no-cache"
      },
      timeout: 10000
    });

    return response.data;
  } catch (error) {
    console.error("Error fetching DASH playlist:", error.message);
    return null;
  }
}

function getBestVideo(xml, id) {
  try {
    const regex = /<Representation[^>]*mimeType="video\/mp4"[^>]*>[\s\S]*?<BaseURL>([^<]+)<\/BaseURL>/g;
    const matches = [];
    let match;

    while ((match = regex.exec(xml)) !== null) {
      matches.push({ file: match[1] });
    }

    if (matches.length === 0) {
      return null;
    }

    const best = matches[matches.length - 1];
    return `https://v.redd.it/${id}/${best.file}`;
  } catch (error) {
    console.error("Error parsing video streams:", error.message);
    return null;
  }
}

function getAudio(xml, id) {
  try {
    const match = xml.match(/<Representation[^>]*mimeType="audio\/mp4"[\s\S]*?<BaseURL>([^<]+)<\/BaseURL>/);

    if (!match) {
      return null;
    }

    const audioFile = match[1];
    return `https://v.redd.it/${id}/${audioFile}`;
  } catch (error) {
    console.error("Error parsing audio stream:", error.message);
    return null;
  }
}

// ==================== DOWNLOAD FUNCTIONS ====================

async function downloadAndPreparePost(post) {
  const tempFilesToClean = [];
  
  try {
    const { url, title, mediaType, releaseDate } = post;

    if (mediaType === "video") {
      if (!url.includes("v.redd.it")) {
        console.log("✗ Not a v.redd.it video");
        return null;
      }

      const id = url.split("/")[3];
      const dash = await getDashPlaylist(id);

      if (!dash) {
        console.log("✗ No DASH playlist found");
        return null;
      }

      const videoUrl = getBestVideo(dash, id);
      const audioUrl = getAudio(dash, id);

      if (!videoUrl) {
        console.log("✗ No video stream found");
        return null;
      }

      let mp4Blob = null;

      if (videoUrl && audioUrl) {
        console.log("  → Downloading video and audio...");
        const videoFile = await downloadFile(videoUrl, `video_${Date.now()}.mp4`);
        const audioFile = await downloadFile(audioUrl, `audio_${Date.now()}.m4a`);

        if (videoFile && audioFile) {
          tempFilesToClean.push(videoFile);
          tempFilesToClean.push(audioFile);

          console.log("  → Merging with FFmpeg...");
          const outputFile = getTempFilePath(`merged_${Date.now()}.mp4`);
          
          try {
            await mergeVideoAudio(videoFile, audioFile, outputFile);

            // ✅ KEY FIX: Wait for file to be fully written
            await new Promise(r => setTimeout(r, 500));

            const blob = fs.readFileSync(outputFile);
            
            if (blob.length === 0) {
              console.log("✗ Merged file is empty");
              return null;
            }

            mp4Blob = {
              data: blob,
              contentType: "video/mp4",
              filename: sanitizeFilename(title) + ".mp4",
              releaseDate: releaseDate,
              title: title
            };
          } catch (mergeError) {
            console.error("✗ Failed to merge video and audio:", mergeError.message);
            return null;
          } finally {
            // Clean up temp files after reading
            cleanupFile(videoFile);
            cleanupFile(audioFile);
            cleanupFile(outputFile);
          }
        }
      } else if (videoUrl) {
        console.log("  → Downloading video only (no audio)...");
        const videoFile = await downloadFile(videoUrl, `video_${Date.now()}.mp4`);
        if (videoFile) {
          tempFilesToClean.push(videoFile);
          
          const blob = fs.readFileSync(videoFile);
          
          if (blob.length === 0) {
            console.log("✗ Video file is empty");
            return null;
          }

          mp4Blob = {
            data: blob,
            contentType: "video/mp4",
            filename: sanitizeFilename(title) + ".mp4",
            releaseDate: releaseDate,
            title: title
          };

          cleanupFile(videoFile);
        }
      }

      return mp4Blob;
    } else if (["image", "png", "jpg", "jpeg", "gif"].includes(mediaType)) {
      console.log("  → Downloading image...");

      const imageFile = await downloadFileWithValidation(url, mediaType);

      if (imageFile && imageFile.blob) {
        const contentTypeMap = {
          png: "image/png",
          jpg: "image/jpeg",
          jpeg: "image/jpeg",
          gif: "image/gif",
          image: "image/jpeg"
        };

        return {
          data: imageFile.blob,
          contentType: imageFile.contentType || contentTypeMap[mediaType] || "image/jpeg",
          filename: sanitizeFilename(title) + "." + (imageFile.extension || mediaType),
          releaseDate: releaseDate,
          title: title
        };
      }
    }

    return null;
  } catch (error) {
    console.error("Error downloading post:", error.message);
    return null;
  } finally {
    // Final cleanup pass
    tempFilesToClean.forEach(cleanupFile);
  }
}

async function downloadFile(url, filename) {
  try {
    const response = await axios.get(url, {
      responseType: "arraybuffer",
      headers: {
        "User-Agent": getRandomUserAgent(),
        "Referer": "https://www.reddit.com/",
        "Cache-Control": "no-cache",
        "Pragma": "no-cache"
      },
      timeout: 60000,
      maxRedirects: 10
    });

    if (response.status !== 200) {
      console.log(`✗ Download failed (HTTP ${response.status})`);
      return null;
    }

    if (!response.data || response.data.length === 0) {
      console.log(`✗ Download returned empty data`);
      return null;
    }

    const filepath = getTempFilePath(filename);
    fs.writeFileSync(filepath, response.data);

    const sizeInMB = (response.data.length / 1024 / 1024).toFixed(2);
    console.log(`  → Downloaded ${filename} (${sizeInMB} MB)`);

    return filepath;
  } catch (error) {
    console.error(`✗ Error downloading ${filename}: ${error.message}`);
    return null;
  }
}

async function downloadFileWithValidation(url, expectedType) {
  try {
    const response = await axios.get(url, {
      responseType: "arraybuffer",
      headers: {
        "User-Agent": getRandomUserAgent(),
        "Referer": "https://www.reddit.com/",
        "Accept": "image/avif,image/webp,image/apng,image/*,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.9",
        "Accept-Encoding": "gzip, deflate",
        "Cache-Control": "no-cache",
        "Pragma": "no-cache",
        "DNT": "1",
        "Connection": "keep-alive",
        "Upgrade-Insecure-Requests": "1"
      },
      timeout: 60000,
      maxRedirects: 10
    });

    if (response.status === 403) {
      console.log(`⚠️  Image blocked by host (HTTP 403) - skipping`);
      return null;
    }

    if (response.status === 304) {
      console.log(`⚠️  Image not modified (HTTP 304) - skipping`);
      return null;
    }

    if (response.status !== 200) {
      console.log(`✗ Failed to download (HTTP ${response.status})`);
      return null;
    }

    if (!response.data || response.data.length === 0) {
      console.log(`✗ Download returned empty data`);
      return null;
    }

    const contentType = response.headers["content-type"];
    if (!contentType || !contentType.toLowerCase().includes("image")) {
      console.log(`✗ Invalid content-type: ${contentType}`);
      return null;
    }

    let extension = expectedType;
    if (contentType.includes("jpeg")) {
      extension = "jpg";
    } else if (contentType.includes("png")) {
      extension = "png";
    } else if (contentType.includes("gif")) {
      extension = "gif";
    } else if (contentType.includes("webp")) {
      extension = "webp";
    }

    const fileSize = response.data.length;
    console.log(`  → Downloaded image (${(fileSize / 1024 / 1024).toFixed(2)} MB)`);

    if (fileSize > EMAIL_SIZE_LIMIT) {
      console.log(`✗ Image exceeds size limit`);
      return null;
    }

    return {
      blob: Buffer.from(response.data),
      contentType: contentType.split(";")[0],
      extension: extension
    };
  } catch (error) {
    console.error(`✗ Error downloading image: ${error.message}`);
    return null;
  }
}

async function mergeVideoAudio(videoFile, audioFile, outputFile) {
  try {
    await execFileAsync("ffmpeg", [
      "-i", videoFile,
      "-i", audioFile,
      "-c:v", "copy",
      "-c:a", "copy",
      "-y",
      outputFile
    ]);
  } catch (error) {
    console.error("Error merging video and audio:", error.message);
    throw error;
  }
}

// ==================== EMAIL FUNCTIONS ====================

function buildEmailBody(batch, emailIndex, totalEmails, totalAttachments) {
  let body = `📦 Reddit Media Package\n`;
  body += `━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n`;

  if (totalEmails > 1) {
    body += `📧 Email ${emailIndex + 1} of ${totalEmails}\n`;
    body += `📊 Total Attachments: ${totalAttachments}\n\n`;
  }

  body += `📋 Contents:\n`;
  body += `━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n`;

  batch.forEach((att, index) => {
    const sizeInMB = (att.data.length / 1024 / 1024).toFixed(2);
    const mediaType = att.contentType.includes("video") ? "🎬 VIDEO" : "🖼️  IMAGE";

    body += `${index + 1}. ${mediaType}\n`;
    body += `   📄 Name: ${att.filename}\n`;
    body += `   📏 Size: ${sizeInMB} MB\n`;
    body += `   📅 Released: ${att.releaseDate}\n`;
    body += `   📝 Title: ${att.title}\n\n`;
  });

  body += `━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n`;
  body += `✅ Ready to view!\n`;

  return body;
}

function validateEmailSubject(subject) {
  // SMTP line length limit is 998 characters
  if (subject.length > 998) {
    return subject.substring(0, 990) + "...";
  }
  return subject;
}

async function sendEmailsWithAttachments(subreddit, allAttachments) {
  const emailBatches = [];
  let currentBatch = [];
  let currentSize = 0;

  for (const attachment of allAttachments) {
    const attachmentSize = attachment.data.length;

    if (currentSize + attachmentSize > EMAIL_SIZE_LIMIT && currentBatch.length > 0) {
      emailBatches.push(currentBatch);
      currentBatch = [];
      currentSize = 0;
    }

    currentBatch.push(attachment);
    currentSize += attachmentSize;
  }

  if (currentBatch.length > 0) {
    emailBatches.push(currentBatch);
  }

  console.log(`\nSending ${emailBatches.length} email(s) with ${allAttachments.length} attachment(s) total`);

  for (let emailIndex = 0; emailIndex < emailBatches.length; emailIndex++) {
    const batch = emailBatches[emailIndex];
    const attachmentsList = batch.map((att) => ({
      filename: att.filename,
      content: att.data,
      contentType: att.contentType || "application/octet-stream"
    }));

    let emailSubject = emailBatches.length > 1
      ? `Latest media from r/${subreddit} (Part ${emailIndex + 1}/${emailBatches.length})`
      : `Latest media from r/${subreddit}`;

    emailSubject = validateEmailSubject(emailSubject);
    const emailBody = buildEmailBody(batch, emailIndex, emailBatches.length, allAttachments.length);

    try {
      const mailOptions = {
        from: SMTP_USER,
        to: SMTP_USER,
        subject: emailSubject,
        text: emailBody,
        attachments: attachmentsList
      };

      await transporter.sendMail(mailOptions);
      console.log(`✓ Email ${emailIndex + 1}/${emailBatches.length} sent successfully with ${batch.length} attachment(s)`);
    } catch (error) {
      console.error(`✗ Error sending email ${emailIndex + 1}:`, error.message);
    }
  }
}

// ==================== AUTOMATION FUNCTIONS ====================

async function processRedditLabel() {
  if (isProcessing) {
    console.log(`[${new Date().toLocaleTimeString()}] ⏳ Check already in progress, skipping...`);
    return;
  }

  isProcessing = true;
  const timestamp = new Date().toLocaleTimeString();
  console.log(`\n[${timestamp}] 🔍 Starting Reddit label check...`);

  try {
    await checkRedditLabel();
    console.log(`[${new Date().toLocaleTimeString()}] ✓ Reddit label check completed`);
  } catch (error) {
    console.error(`[${new Date().toLocaleTimeString()}] ✗ Error during check:`, error.message);
  } finally {
    isProcessing = false;
  }
}

function startAutomatedChecks() {
  console.log(`\n📅 Automated checking enabled (every ${CHECK_INTERVAL / 1000} seconds)`);
  console.log(`⏰ Next checks will run at regular intervals\n`);

  processRedditLabel();

  setInterval(processRedditLabel, CHECK_INTERVAL);
}

// ==================== MAIN ====================

async function main() {
  if (!GMAIL_USER || !GMAIL_APP_PASSWORD) {
    console.error(
      "Error: GMAIL_USER and GMAIL_APP_PASSWORD environment variables must be set"
    );
    process.exit(1);
  }

  ensureTempDir();
  initializeTracking();
  console.log(`Tracking file: ${TRACKING_FILE}`);
  console.log(`Temp directory: ${TEMP_DIR}`);

  console.log(`Starting Reddit Media Downloader for ${GMAIL_USER}`);
  console.log("=========================================");

  return new Promise((resolve, reject) => {
    imap.on("ready", () => {
      imapConnected = true;
      console.log("✓ IMAP connected\n");
      startAutomatedChecks();
    });

    imap.on("error", (err) => {
      console.error("✗ IMAP error:", err.message);
      reject(err);
    });

    imap.on("end", () => {
      imapConnected = false;
      console.log("✓ IMAP connection closed");
      resolve();
    });

    imap.connect();
  });
}

process.on("SIGINT", () => {
  console.log("\n\n🛑 Shutting down gracefully...");
  cleanupTempFiles();
  
  if (imapConnected) {
    imap.closeBox(false, () => {
      imap.end();
    });
  } else {
    process.exit(0);
  }
});

main()
  .then(() => {
    console.log("=========================================");
    console.log("✓ Script completed");
  })
  .catch((err) => {
    console.error("=========================================");
    console.error("✗ Fatal error:", err.message);
    process.exit(1);
  });
});

// Start the server
app.listen(3000, () => console.log("Server running on port 3000"));