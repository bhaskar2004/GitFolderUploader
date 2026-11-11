/**
 * Folder to GitHub — High-Performance Precision Git Engine
 * Designed for Massive Repositories (50,000+ files), 60fps Virtual Scrolling,
 * In-Browser Secret Scanning, Git SHA-1 Diffing, and Resilient API Uploads.
 */

const $ = s => document.querySelector(s);
const $$ = s => document.querySelectorAll(s);
const API = 'https://api.github.com';

// Limits & constants
const MAX_FILE_SIZE = 50 * 1024 * 1024;     // 50MB warning threshold
const HARD_LIMIT = 100 * 1024 * 1024;       // 100MB GitHub limit
const INLINE_MAX = 512 * 1024;              // 512KB: text files up to 512KB inline directly into the Git tree for ultra-fast single-batch upload
const BIG_FILE_THRESHOLD = 8 * 1024 * 1024; // 8MB: upload sequentially
const TREE_MAX_CHARS = 2.5 * 1024 * 1024;   // 2.5MB per tree chunk (GitHub limit is 10MB)
const TREE_MAX_ENTRIES = 400;               // Up to 400 entries per tree chunk
const ROW_HEIGHT = 38;                      // Fixed row height in px for 60fps virtual scroller

// Clutter & secret filter patterns
const DEFAULT_SKIP_REGEX = /(^|\/)(node_modules|__MACOSX|\.next|\.nuxt|dist|build|out|\.venv|venv|\.cache)(\/|$)|(^|\/)(\.DS_Store|Thumbs\.db|desktop\.ini|\.env(\.(?!example$|sample$)[^/]*)?|id_rsa|id_ed25519|.*\.pem|.*\.key|.*\.pfx|.*\.pkcs12)$/i;
const GITDIR_REGEX = /(^|\/)\.git(\/|$)/i;

// Secret detection patterns
const SECRET_PATTERNS = [
  { name: 'AWS Access Key', regex: /(?:^|[^A-Z0-9])(AKIA[0-9A-Z]{16})(?:[^A-Z0-9]|$)/ },
  { name: 'GitHub Personal Access Token', regex: /(?:^|[^A-Za-z0-9_])(gh[pousr]_[A-Za-z0-9_]{36,}|github_pat_[A-Za-z0-9_]{82})(?:[^A-Za-z0-9_]|$)/ },
  { name: 'Private Key Block', regex: /-----BEGIN (?:RSA |EC |DSA |OPENSSH )?PRIVATE KEY-----/ },
  { name: 'OpenAI / Anthropic API Key', regex: /(?:^|[^A-Za-z0-9_-])(sk-[A-Za-z0-9]{20,T3BlbkFJ[A-Za-z0-9]{20,}|sk-proj-[A-Za-z0-9_-]{40,}|sk-ant-[A-Za-z0-9_-]{40,})(?:[^A-Za-z0-9_-]|$)/ },
  { name: 'Slack Token / Webhook', regex: /(xox[baprs]-[0-9]{10,13}-[0-9]{10,13}[a-zA-Z0-9-]*|https:\/\/hooks\.slack\.com\/services\/T[0-9A-Z]{8}\/B[0-9A-Z]{8}\/[0-9A-Za-z]{24})/ },
  { name: 'Stripe Secret Key', regex: /(sk_live_[0-9a-zA-Z]{24,})/ },
  { name: 'Google API Key', regex: /(AIza[0-9A-Za-z\\-_]{35})/ }
];

// Binary extensions to skip when scanning text or secrets
const BINARY_EXTS = new Set([
  'png','jpg','jpeg','gif','ico','webp','svg','pdf','zip','tar','gz','tgz','7z','rar',
  'exe','dll','dylib','so','woff','woff2','ttf','eot','mp4','mp3','mov','avi','wav',
  'bin','dat','iso','dmg','class','jar','pyc','o','obj','node'
]);

// Application state
const files = new Map();           // source path -> File object
let token = '', me = '', currentRepoData = null, busy = false, cancelled = false;
let abortCtrl = null, rowMap = new Map(), defaults = {}, currentView = 'flat';
let uploadStartTime = 0;
let soundEnabled = true;

// Caches for high-load optimization
const secretCache = new Map();     // cacheKey -> array of secret hits
const sha1Cache = new Map();       // cacheKey -> sha1 hex string
let remoteTreeMap = new Map();     // path -> remote sha
let fileGitShaMap = new Map();     // repoPath -> sha1
let fileSecretsMap = new Map();    // path -> array of secret names
let gitignoreRules = [];           // array of parsed rules
let activeDiffFilter = 'all';      // all, new, mod, same, secret
let currentFilteredList = [];      // cached array of filtered manifest items

// Audio synthesis context
let audioCtx = null;

/* ---------- Utilities ---------- */
const sleep = ms => new Promise(r => setTimeout(r, ms));
const fmt = n => {
  if (n < 1024) return n + ' B';
  if (n < 1024 * 1024) return (n / 1024).toFixed(1) + ' KB';
  if (n < 1024 * 1024 * 1024) return (n / (1024 * 1024)).toFixed(1) + ' MB';
  return (n / (1024 * 1024 * 1024)).toFixed(2) + ' GB';
};

const enc = encodeURIComponent;
const escapeHTML = str => (str || '').replace(/[&<>'"]/g, tag => ({
  '&': '&amp;', '<': '&lt;', '>': '&gt;', "'": '&#39;', '"': '&quot;'
}[tag] || tag));

const getExt = path => {
  const name = path.split('/').pop();
  const idx = name.lastIndexOf('.');
  return idx > 0 ? name.slice(idx + 1).toLowerCase() : '';
};

// Safe text decoder (UTF-8)
const textDecoder = new TextDecoder('utf-8', { fatal: true });
function asText(buf) {
  try {
    return textDecoder.decode(buf);
  } catch (err) {
    return null;
  }
}

// Convert ArrayBuffer or Blob to Base64 efficiently
function toBase64(blob) {
  return new Promise((resolve, reject) => {
    const reader = new FileReader();
    reader.onload = () => {
      const dataUrl = reader.result;
      const base64 = dataUrl.slice(dataUrl.indexOf(',') + 1);
      resolve(base64);
    };
    reader.onerror = reject;
    reader.readAsDataURL(blob);
  });
}

// User interaction tracking to strictly respect browser AudioContext autoplay policy
let userInteracted = false;
function markInteracted() {
  userInteracted = true;
  if (audioCtx && audioCtx.state === 'suspended') {
    audioCtx.resume().catch(() => {});
  }
}
['click', 'keydown', 'pointerdown', 'touchstart'].forEach(evt => {
  document.addEventListener(evt, markInteracted, { capture: true, passive: true });
});

// Tactical Cyber Audio Synthesizer (Pops, Mechanical Thuds, Railgun Arms, Alerts)
function playSound(type) {
  if (!soundEnabled || !userInteracted) return;
  try {
    const Ctx = window.AudioContext || window.webkitAudioContext;
    if (!Ctx) return;
    if (!audioCtx) audioCtx = new Ctx();
    if (audioCtx.state === 'suspended') {
      audioCtx.resume().catch(() => {});
      return;
    }

    const now = audioCtx.currentTime;

    if (type === 'pop') {
      // Crisp tactical mechanical shutter / high-tech click
      const osc = audioCtx.createOscillator();
      const gain = audioCtx.createGain();
      osc.type = 'triangle';
      osc.frequency.setValueAtTime(1400, now);
      osc.frequency.exponentialRampToValueAtTime(320, now + 0.04);
      gain.gain.setValueAtTime(0.12, now);
      gain.gain.exponentialRampToValueAtTime(0.001, now + 0.04);
      osc.connect(gain);
      gain.connect(audioCtx.destination);
      osc.start(now);
      osc.stop(now + 0.04);
    } else if (type === 'thud') {
      // Deep sub-bass hydraulic impact for payload staging
      const osc = audioCtx.createOscillator();
      const gain = audioCtx.createGain();
      osc.type = 'sine';
      osc.frequency.setValueAtTime(95, now);
      osc.frequency.exponentialRampToValueAtTime(32, now + 0.16);
      gain.gain.setValueAtTime(0.24, now);
      gain.gain.exponentialRampToValueAtTime(0.001, now + 0.16);
      osc.connect(gain);
      gain.connect(audioCtx.destination);
      osc.start(now);
      osc.stop(now + 0.16);
    } else if (type === 'arm') {
      // Power-up ascending railgun frequency ramp
      const osc = audioCtx.createOscillator();
      const gain = audioCtx.createGain();
      osc.type = 'sawtooth';
      osc.frequency.setValueAtTime(90, now);
      osc.frequency.exponentialRampToValueAtTime(620, now + 0.24);
      gain.gain.setValueAtTime(0.08, now);
      gain.gain.linearRampToValueAtTime(0.16, now + 0.18);
      gain.gain.exponentialRampToValueAtTime(0.001, now + 0.26);
      osc.connect(gain);
      gain.connect(audioCtx.destination);
      osc.start(now);
      osc.stop(now + 0.26);
    } else if (type === 'success') {
      // Dual-voice cinematic cyberpunk chord
      const osc1 = audioCtx.createOscillator();
      const osc2 = audioCtx.createOscillator();
      const gain = audioCtx.createGain();
      osc1.type = 'triangle';
      osc2.type = 'sine';
      osc1.frequency.setValueAtTime(440, now); // A4
      osc2.frequency.setValueAtTime(660, now); // E5 (Perfect 5th)
      gain.gain.setValueAtTime(0.18, now);
      gain.gain.exponentialRampToValueAtTime(0.001, now + 0.42);
      osc1.connect(gain);
      osc2.connect(gain);
      gain.connect(audioCtx.destination);
      osc1.start(now);
      osc2.start(now);
      osc1.stop(now + 0.42);
      osc2.stop(now + 0.42);
    } else if (type === 'warn') {
      // Dissonant dual-oscillator breach klaxon
      const osc1 = audioCtx.createOscillator();
      const osc2 = audioCtx.createOscillator();
      const gain = audioCtx.createGain();
      osc1.type = 'sawtooth';
      osc2.type = 'sawtooth';
      osc1.frequency.setValueAtTime(240, now);
      osc2.frequency.setValueAtTime(248, now); // 8Hz beating frequency
      gain.gain.setValueAtTime(0.18, now);
      gain.gain.exponentialRampToValueAtTime(0.001, now + 0.28);
      osc1.connect(gain);
      osc2.connect(gain);
      gain.connect(audioCtx.destination);
      osc1.start(now);
      osc2.start(now);
      osc1.stop(now + 0.28);
      osc2.stop(now + 0.28);
    }
  } catch(e) {}
}

// Local storage helper
const store = {
  get: k => { try { return localStorage.getItem(k); } catch(e) { return null; } },
  set: (k, v) => { try { localStorage.setItem(k, v); } catch(e) {} },
  del: k => { try { localStorage.removeItem(k); } catch(e) {} }
};

// Pure JS SHA-1 fallback for environments where crypto.subtle is restricted (e.g. file:// origins)
function sha1Fallback(buffer) {
  const bytes = new Uint8Array(buffer);
  const n = bytes.length;
  const words = [];
  for (let i = 0; i < n; i++) {
    words[i >> 2] |= bytes[i] << (24 - (i % 4) * 8);
  }
  words[n >> 2] |= 0x80 << (24 - (n % 4) * 8);
  words[(((n + 8) >> 6) << 4) + 15] = n * 8;

  let H0 = 0x67452301, H1 = 0xefcdab89, H2 = 0x98badcfe, H3 = 0x10325476, H4 = 0xc3d2e1f0;
  const W = new Int32Array(80);

  for (let i = 0; i < words.length; i += 16) {
    for (let t = 0; t < 16; t++) W[t] = words[i + t] | 0;
    for (let t = 16; t < 80; t++) {
      const v = W[t - 3] ^ W[t - 8] ^ W[t - 14] ^ W[t - 16];
      W[t] = (v << 1) | (v >>> 31);
    }
    let a = H0, b = H1, c = H2, d = H3, e = H4;
    for (let t = 0; t < 80; t++) {
      let f, k;
      if (t < 20) { f = (b & c) | ((~b) & d); k = 0x5a827999; }
      else if (t < 40) { f = b ^ c ^ d; k = 0x6ed9eba1; }
      else if (t < 60) { f = (b & c) | (b & d) | (c & d); k = 0x8f1bbcdc; }
      else { f = b ^ c ^ d; k = 0xca62c1d6; }
      const temp = (((a << 5) | (a >>> 27)) + f + e + k + W[t]) | 0;
      e = d; d = c; c = (b << 30) | (b >>> 2); b = a; a = temp;
    }
    H0 = (H0 + a) | 0; H1 = (H1 + b) | 0; H2 = (H2 + c) | 0; H3 = (H3 + d) | 0; H4 = (H4 + e) | 0;
  }
  return [H0, H1, H2, H3, H4].map(h => (h >>> 0).toString(16).padStart(8, '0')).join('');
}

/* ---------- Git Blob SHA-1 Calculation ---------- */
async function computeGitBlobSha(file) {
  const cacheKey = `${file.name}:${file.size}:${file.lastModified}`;
  if (sha1Cache.has(cacheKey)) return sha1Cache.get(cacheKey);

  try {
    const arrayBuffer = await file.arrayBuffer();
    const headerStr = `blob ${arrayBuffer.byteLength}\0`;
    const headerBytes = new TextEncoder().encode(headerStr);
    const combined = new Uint8Array(headerBytes.length + arrayBuffer.byteLength);
    combined.set(headerBytes, 0);
    combined.set(new Uint8Array(arrayBuffer), headerBytes.length);

    let sha = '';
    if (window.crypto && window.crypto.subtle && window.crypto.subtle.digest) {
      try {
        const hashBuffer = await crypto.subtle.digest('SHA-1', combined);
        const hashArray = Array.from(new Uint8Array(hashBuffer));
        sha = hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
      } catch (subtleErr) {
        sha = sha1Fallback(combined);
      }
    } else {
      sha = sha1Fallback(combined);
    }

    sha1Cache.set(cacheKey, sha);
    return sha;
  } catch (err) {
    return null;
  }
}

/* ---------- Real .gitignore Parser ---------- */
function parseGitignore(content) {
  const lines = content.split('\n');
  const rules = [];
  for (let rawLine of lines) {
    const line = rawLine.trim();
    if (!line || line.startsWith('#')) continue;

    let pattern = line;
    let isNegated = false;
    if (pattern.startsWith('!')) {
      isNegated = true;
      pattern = pattern.slice(1);
    }

    let regexStr = pattern
      .replace(/[.+^${}()|[\]\\]/g, '\\$&')
      .replace(/\*\*/g, '___GLOBSTAR___')
      .replace(/\*/g, '[^/]*')
      .replace(/\?/g, '[^/]')
      .replace(/___GLOBSTAR___/g, '.*');

    if (pattern.endsWith('/')) {
      regexStr = `(^|/)${regexStr}`;
    } else {
      regexStr = `(^|/)${regexStr}($|/)`;
    }

    try {
      rules.push({ regex: new RegExp(regexStr, 'i'), negated: isNegated });
    } catch(e) {}
  }
  return rules;
}

function matchesGitignore(path) {
  if (!gitignoreRules.length || !$('#applyGitignore')?.checked) return false;
  let ignored = false;
  for (const rule of gitignoreRules) {
    if (rule.regex.test(path)) {
      ignored = !rule.negated;
    }
  }
  return ignored;
}

/* ---------- Secret Scanner Engine (Optimized for Huge Repos) ---------- */
function scanTextForSecrets(text) {
  const found = [];
  for (const pattern of SECRET_PATTERNS) {
    const match = text.match(pattern.regex);
    if (match) {
      found.push({
        type: pattern.name,
        preview: match[1] ? match[1].slice(0, 4) + '••••' + match[1].slice(-4) : '••••'
      });
    }
  }
  return found;
}

async function scanAllStagedSecrets(stagedItems) {
  let totalSecrets = 0;
  fileSecretsMap.clear();

  // Scan in small background batches to never block the main thread
  for (let i = 0; i < stagedItems.length; i++) {
    const item = stagedItems[i];
    const ext = getExt(item.path);

    // Skip known binary extensions
    if (BINARY_EXTS.has(ext)) continue;

    const cacheKey = `${item.path}:${item.file.size}:${item.file.lastModified}`;
    if (secretCache.has(cacheKey)) {
      const cached = secretCache.get(cacheKey);
      if (cached.length) {
        fileSecretsMap.set(item.path, cached);
        totalSecrets += cached.length;
      }
      continue;
    }

    // Read only first 64KB for secret scanning (secrets are in configs/headers)
    if (item.file.size > 0) {
      try {
        const slice = item.file.slice(0, 65536);
        const text = asText(await slice.arrayBuffer());
        if (text !== null) {
          const hits = scanTextForSecrets(text);
          secretCache.set(cacheKey, hits);
          if (hits.length) {
            fileSecretsMap.set(item.path, hits);
            totalSecrets += hits.length;
          }
        } else {
          secretCache.set(cacheKey, []);
        }
      } catch(e) {
        secretCache.set(cacheKey, []);
      }
    }

    // Yield every 25 files to preserve 60fps interaction
    if (i % 25 === 0) await sleep(0);
  }

  return totalSecrets;
}

/* ---------- Theme, Sound & Shortcuts Controls ---------- */
const themeToggle = $('#themeToggle');
const themeIcon = $('#themeIcon');
const themeLabel = $('#themeLabel');
const soundToggle = $('#soundToggle');

function updateThemeUI(theme) {
  if (theme === 'dark') {
    themeIcon.innerHTML = '<path d="M12 3a6 6 0 0 0 9 9 9 9 0 1 1-9-9Z"/>';
    themeLabel.textContent = 'Dark';
  } else if (theme === 'light') {
    themeIcon.innerHTML = '<circle cx="12" cy="12" r="4"/><path d="M12 2v2"/><path d="M12 20v2"/><path d="m4.93 4.93 1.41 1.41"/><path d="m17.66 17.66 1.41 1.41"/><path d="M2 12h2"/><path d="M20 12h2"/><path d="m6.34 17.66-1.41 1.41"/><path d="m19.07 4.93-1.41 1.41"/>';
    themeLabel.textContent = 'Light';
  } else {
    themeIcon.innerHTML = '<rect width="18" height="14" x="3" y="3" rx="2"/><line x1="8" y1="21" x2="16" y2="21"/><line x1="12" y1="17" x2="12" y2="21"/>';
    themeLabel.textContent = 'Auto';
  }
}

function initTheme() {
  const saved = store.get('f2g.theme') || 'auto';
  updateThemeUI(saved);
  themeToggle?.addEventListener('click', () => {
    const cur = document.documentElement.getAttribute('data-theme') || (store.get('f2g.theme') || 'auto');
    const order = ['auto', 'dark', 'light'];
    const next = order[(order.indexOf(cur) + 1) % order.length];
    if (next === 'auto') {
      document.documentElement.removeAttribute('data-theme');
      store.del('f2g.theme');
      $('meta[name="color-scheme"]').content = 'light dark';
    } else {
      document.documentElement.setAttribute('data-theme', next);
      store.set('f2g.theme', next);
      $('meta[name="color-scheme"]').content = next;
    }
    updateThemeUI(next);
    playSound('pop');
  });
}

function initSound() {
  soundEnabled = store.get('f2g.sound') !== 'muted';
  updateSoundUI();
  if (soundToggle) {
    soundToggle.addEventListener('click', () => {
      soundEnabled = !soundEnabled;
      store.set('f2g.sound', soundEnabled ? 'on' : 'muted');
      updateSoundUI();
      if (soundEnabled) playSound('pop');
    });
  }
}

function updateSoundUI() {
  if (!soundToggle) return;
  soundToggle.innerHTML = soundEnabled 
    ? '<svg class="icon icon-sm" viewBox="0 0 24 24"><polygon points="11 5 6 9 2 9 2 15 6 15 11 19 11 5"/><path d="M15.54 8.46a5 5 0 0 1 0 7.07"/><path d="M19.07 4.93a10 10 0 0 1 0 14.14"/></svg><span>Sound</span>'
    : '<svg class="icon icon-sm" viewBox="0 0 24 24"><polygon points="11 5 6 9 2 9 2 15 6 15 11 19 11 5"/><line x1="23" y1="9" x2="17" y2="15"/><line x1="17" y1="9" x2="23" y2="15"/></svg><span>Muted</span>';
}

/* ---------- Shortcuts Modal ---------- */
const shortcutsModal = $('#shortcutsModal');
$('#shortcutsBtn')?.addEventListener('click', () => shortcutsModal?.showModal());
$('#closeShortcutsModal')?.addEventListener('click', () => shortcutsModal?.close());

/* ---------- Toast & Confetti ---------- */
function showToast(message, type = 'info', timeout = 3200) {
  const shelf = $('#toastShelf');
  if (!shelf) return;
  const t = document.createElement('div');
  t.className = `toast ${type}`;
  t.innerHTML = `
    <span style="display:flex; align-items:center;">
      ${type === 'ok' ? '<svg class="icon icon-sm" style="color:var(--ok);" viewBox="0 0 24 24"><polyline points="20 6 9 17 4 12"/></svg>' : ''}
      ${type === 'err' ? '<svg class="icon icon-sm" style="color:var(--err);" viewBox="0 0 24 24"><circle cx="12" cy="12" r="10"/><line x1="15" y1="9" x2="9" y2="15"/><line x1="9" y1="9" x2="15" y2="15"/></svg>' : ''}
    </span>
    <span>${escapeHTML(message)}</span>
  `;
  shelf.append(t);
  setTimeout(() => {
    t.style.opacity = '0';
    t.style.transform = 'translateY(8px)';
    t.style.transition = 'all 0.18s ease';
    setTimeout(() => t.remove(), 200);
  }, timeout);
}

function fireConfetti() {
  const canvas = $('#confettiCanvas');
  if (!canvas) return;
  const ctx = canvas.getContext('2d');
  canvas.width = window.innerWidth;
  canvas.height = window.innerHeight;

  const count = 75;
  const colors = ['#2563eb', '#38bdf8', '#10b981', '#f59e0b', '#ec4899', '#8b5cf6'];
  const particles = Array.from({ length: count }, () => ({
    x: canvas.width * 0.5,
    y: canvas.height * 0.4,
    vx: (Math.random() - 0.5) * 16,
    vy: (Math.random() - 0.7) * 18,
    size: Math.random() * 6 + 4,
    color: colors[Math.floor(Math.random() * colors.length)],
    rot: Math.random() * 360,
    vr: (Math.random() - 0.5) * 10,
    life: 1
  }));

  let start = performance.now();
  function frame(now) {
    const dt = (now - start) / 1000;
    start = now;
    ctx.clearRect(0, 0, canvas.width, canvas.height);

    let alive = 0;
    for (const p of particles) {
      p.x += p.vx;
      p.y += p.vy;
      p.vy += 22 * dt;
      p.rot += p.vr;
      p.life -= 0.6 * dt;

      if (p.life > 0) {
        alive++;
        ctx.save();
        ctx.translate(p.x, p.y);
        ctx.rotate((p.rot * Math.PI) / 180);
        ctx.globalAlpha = Math.max(0, p.life);
        ctx.fillStyle = p.color;
        ctx.fillRect(-p.size / 2, -p.size / 2, p.size, p.size);
        ctx.restore();
      }
    }

    if (alive > 0) requestAnimationFrame(frame);
    else ctx.clearRect(0, 0, canvas.width, canvas.height);
  }
  requestAnimationFrame(frame);
}

/* ---------- Number Animation Helper ---------- */
function animateNumber(el, targetVal, formatFn = v => v) {
  if (!el) return;
  const startVal = parseInt(el.dataset.val || '0', 10);
  if (isNaN(startVal) || startVal === targetVal) {
    el.textContent = formatFn(targetVal);
    el.dataset.val = targetVal;
    return;
  }
  const diff = targetVal - startVal;
  const duration = 220;
  const start = performance.now();

  function step(now) {
    const progress = Math.min((now - start) / duration, 1);
    const ease = 1 - Math.pow(1 - progress, 3);
    const current = Math.round(startVal + diff * ease);
    el.textContent = formatFn(current);
    if (progress < 1) {
      requestAnimationFrame(step);
    } else {
      el.textContent = formatFn(targetVal);
      el.dataset.val = targetVal;
    }
  }
  requestAnimationFrame(step);
}

/* ---------- Live Multi-Stage Pipeline Controls ---------- */
function setPipelineStage(stageNum, title, currentFileName, speedText, isDone = false) {
  const overlay = $('#pipelineOverlay');
  if (overlay) overlay.hidden = false;
  const card = $('#pipelineCard');
  if (!card) return;
  card.hidden = false;
  card.classList.remove('pipeline-error');

  if (title) $('#pipelineStatusText').textContent = title;
  if (currentFileName) {
    const pf = $('#pipelineFile');
    if (pf) {
      pf.textContent = currentFileName;
      pf.hidden = false;
    }
  }
  if (speedText) $('#pipelineSpeed').textContent = speedText;

  const spinner = $('#pipelineSpinner');

  if (isDone) {
    card.classList.add('pipeline-completed');
    if (spinner) {
      spinner.className = 'pipeline-check-icon';
      spinner.innerHTML = '<svg class="icon icon-sm" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><polyline points="20 6 9 17 4 12"/></svg>';
    }
    for (let i = 1; i <= 5; i++) {
      const stepEl = $('#stage' + i);
      if (!stepEl) continue;
      stepEl.className = 'pipeline-step completed';
      const dot = stepEl.querySelector('.stage-dot');
      if (dot) dot.innerHTML = '✓';
    }
  } else {
    card.classList.remove('pipeline-completed');
    if (spinner) {
      spinner.className = 'spinner-pulse';
      spinner.innerHTML = '';
    }
    for (let i = 1; i <= 5; i++) {
      const stepEl = $('#stage' + i);
      if (!stepEl) continue;
      const dot = stepEl.querySelector('.stage-dot');
      if (i < stageNum) {
        stepEl.className = 'pipeline-step completed';
        if (dot) dot.innerHTML = '✓';
      } else if (i === stageNum) {
        stepEl.className = 'pipeline-step active';
        if (dot) dot.textContent = i;
      } else {
        stepEl.className = 'pipeline-step';
        if (dot) dot.textContent = i;
      }
    }
  }
}

/* ---------- Auth & Token Management ---------- */
$('#reveal').onclick = () => {
  const t = $('#token'), isPw = t.type === 'password';
  t.type = isPw ? 'text' : 'password';
  $('#reveal').setAttribute('aria-pressed', isPw);
  $('#reveal span').textContent = isPw ? 'Hide' : 'Show';
};

$('#disconnectBtn').onclick = () => {
  token = '';
  me = '';
  $('#token').value = '';
  store.del('f2g.token');
  $('#authCard').hidden = true;
  $('#repos').textContent = '';
  $('#branches').textContent = '';
  refresh();
  showToast('Token cleared and disconnected', 'info');
  playSound('pop');
};

let verifyTimer = null;
async function verifyToken() {
  token = $('#token').value.trim();
  me = '';
  $('#repos').textContent = '';
  if (!token) {
    $('#authCard').hidden = true;
    return refresh();
  }

  $('#authCard').hidden = false;
  $('#authName').textContent = 'Authenticating…';
  $('#authAvatar').src = 'data:image/svg+xml,<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="%2394a3b8"><circle cx="12" cy="12" r="10"/></svg>';
  $('#authScopes').textContent = 'Checking scopes…';
  $('#rateLimitPill').textContent = 'Rate: …';

  try {
    const res = await fetch(API + '/user', {
      headers: {
        Authorization: 'token ' + token,
        Accept: 'application/vnd.github+json'
      }
    });

    const rate = res.headers.get('x-ratelimit-remaining');
    const limit = res.headers.get('x-ratelimit-limit');
    if (rate) $('#rateLimitPill').textContent = `Rate: ${rate}/${limit}`;

    if (!res.ok) {
      $('#authName').textContent = 'Authentication failed';
      $('#authScopes').textContent = res.status === 401 ? 'Bad credentials' : `HTTP ${res.status}`;
      return refresh();
    }

    const data = await res.json();
    me = data.login;
    $('#authName').textContent = '@' + data.login + (data.name ? ` (${data.name})` : '');
    $('#authAvatar').src = data.avatar_url;

    const scopes = res.headers.get('x-oauth-scopes');
    $('#authScopes').textContent = scopes !== null ? (scopes ? `Scope: ${scopes}` : 'Fine-grained PAT') : 'Active';

    showToast(`Connected as @${me}`, 'ok');
    playSound('success');

    // Populate user repositories in background
    gh('/user/repos?per_page=100&sort=updated').then(repos => {
      const dl = $('#repos');
      dl.textContent = '';
      repos.forEach(r => dl.append(Object.assign(document.createElement('option'), { value: r.full_name })));
    }).catch(() => {});
  } catch(e) {
    $('#authName').textContent = 'Network error';
    $('#authScopes').textContent = e.message;
  }
  refresh();
}

$('#token').addEventListener('input', () => {
  clearTimeout(verifyTimer);
  verifyTimer = setTimeout(verifyToken, 450);
});

/* ---------- Destination Management ---------- */
$('#create').addEventListener('change', () => {
  const c = $('#create').checked;
  $('#privWrap').hidden = !c;
  $('#repoLabel').textContent = c ? 'New Repository Name' : 'Repository';
  $('#repo').placeholder = c ? 'my-cool-project' : 'owner/repo or paste GitHub URL';
  $('#repoHelp').innerHTML = c 
    ? 'A fresh empty repository will be provisioned under <strong>' + (me || 'your account') + '</strong>.'
    : 'Type <code>owner/repository</code>, paste URL, or select from dropdown.';
  refresh();
});

let branchTimer = null;
function repoChanged() {
  clearTimeout(branchTimer);
  branchTimer = setTimeout(async () => {
    const slug = slugOf();
    if (!token || !slug || !/^[\w.-]+\/[\w.-]+$/.test(slug)) return;
    try {
      const bs = await gh('/repos/' + slug + '/branches?per_page=100');
      const dl = $('#branches');
      dl.textContent = '';
      bs.forEach(b => dl.append(Object.assign(document.createElement('option'), { value: b.name })));
      checkRemoteDiff();
    } catch {}
  }, 400);
  refresh();
}

$('#repo').addEventListener('input', repoChanged);
$('#branch').addEventListener('input', () => {
  checkRemoteDiff();
  refresh();
});
$('#prefix').addEventListener('input', refresh);

// Prefix Quick Chips
$$('.chip[data-prefix]').forEach(btn => {
  btn.addEventListener('click', () => {
    $('#prefix').value = btn.dataset.prefix;
    refresh();
    playSound('pop');
  });
});

/* ---------- Filter Accordion & Stack Presets ---------- */
$('#filterToggle').onclick = () => {
  const c = $('#filterContent');
  const exp = c.hidden;
  c.hidden = !exp;
  $('#filterToggle').setAttribute('aria-expanded', exp);
  $('#filterArrow').style.transform = exp ? 'rotate(180deg)' : '';
};

$$('.preset-chip').forEach(chip => {
  chip.addEventListener('click', () => {
    const preset = chip.dataset.preset;
    const input = $('#customIgnore');
    const presetsMap = {
      node: 'node_modules, .next, dist, coverage, *.log',
      python: '__pycache__, *.pyc, .venv, venv, .pytest_cache',
      rust: 'target/, Cargo.lock',
      os: '.DS_Store, Thumbs.db, desktop.ini, __MACOSX'
    };
    const val = presetsMap[preset];
    if (val) {
      if (input.value.trim()) {
        input.value = input.value.trim() + ', ' + val;
      } else {
        input.value = val;
      }
      showToast(`Added ${preset.toUpperCase()} ignore preset`, 'ok');
      playSound('pop');
      refresh();
    }
  });
});

$('#skip').addEventListener('change', refresh);
$('#keepRoot').addEventListener('change', refresh);
$('#customIgnore').addEventListener('input', refresh);
$('#applyGitignore')?.addEventListener('change', refresh);

/* ---------- File Ingestion & High-Speed Batch Reader ---------- */
function cleanPath(p) {
  return p.replace(/\\/g, '/').replace(/^\/+/, '').replace(/\/+/g, '/');
}

function addFile(rawPath, file) {
  const p = cleanPath(rawPath);
  if (!p) return;
  files.set(p, file);
}

function bindInput(btnSelector, inputSelector, handler) {
  const b = $(btnSelector), inp = $(inputSelector);
  if (!b || !inp) return;
  b.onclick = () => inp.click();
  inp.onchange = async () => {
    if (busy || !inp.files.length) return;
    await handler(inp.files);
    inp.value = '';
  };
}

async function reportFiles(count, name) {
  if (count <= 0) {
    srcMsg('No new files were found.');
    return;
  }
  srcMsg(`Staged ${count.toLocaleString()} file${count > 1 ? 's' : ''}${name ? ' from ' + name : ''}.`);
  showToast(`Staged ${count.toLocaleString()} file${count > 1 ? 's' : ''}`, 'ok');
  playSound('thud');

  // Auto-detect .gitignore in top-level directory
  for (const [p, f] of files) {
    if (/(^|\/)\.gitignore$/i.test(p)) {
      try {
        const text = asText(await f.arrayBuffer());
        if (text) {
          gitignoreRules = parseGitignore(text);
          $('#gitignoreOption').hidden = false;
          $('#gitignoreCount').textContent = `${gitignoreRules.length} rules`;
        }
      } catch(e) {}
      break;
    }
  }
}

// Button Bindings
bindInput('#bFolder', '#pFolder', async fileList => {
  srcMsg(`Staging ${fileList.length.toLocaleString()} files…`);
  const beforeCount = files.size;
  for (let i = 0; i < fileList.length; i++) {
    const f = fileList[i];
    addFile(f.webkitRelativePath || f.name, f);
  }
  await reportFiles(files.size - beforeCount);
  refresh();
});

bindInput('#bFiles', '#pFiles', async fileList => {
  const beforeCount = files.size;
  for (let i = 0; i < fileList.length; i++) {
    const f = fileList[i];
    addFile(f.name, f);
  }
  await reportFiles(files.size - beforeCount);
  refresh();
});

bindInput('#bZip', '#pZip', async fileList => {
  for (const f of fileList) await addZip(f);
  refresh();
});

let zipLibPromise = null;
function loadZipLib() {
  if (window.JSZip) return Promise.resolve();
  return zipLibPromise || (zipLibPromise = new Promise((resolve, reject) => {
    const s = document.createElement('script');
    s.src = 'https://cdnjs.cloudflare.com/ajax/libs/jszip/3.10.1/jszip.min.js';
    s.onload = resolve;
    s.onerror = () => {
      zipLibPromise = null;
      reject(new Error('Failed to load ZIP extraction library'));
    };
    document.head.append(s);
  }));
}

async function addZip(file) {
  try {
    srcMsg(`Unpacking ${file.name}…`);
    await loadZipLib();
    const zip = await JSZip.loadAsync(file);
    const jobs = [];
    zip.forEach((p, entry) => {
      if (!entry.dir) {
        jobs.push(entry.async('blob').then(b => {
          addFile(p, new File([b], p.split('/').pop()));
        }));
      }
    });
    await Promise.all(jobs);
    await reportFiles(jobs.length, file.name);
  } catch (e) {
    srcMsg(`Could not unpack ${file.name}: ${e.message}`);
  }
}

/* Fullscreen Drag & Drop Handling */
const hasFilesData = e => e.dataTransfer && [...e.dataTransfer.types].includes('Files');
let dragDepth = 0;

document.addEventListener('dragenter', e => {
  if (hasFilesData(e)) {
    e.preventDefault();
    dragDepth++;
    document.body.classList.add('window-dragging');
  }
});

document.addEventListener('dragover', e => {
  if (hasFilesData(e)) e.preventDefault();
});

document.addEventListener('dragleave', e => {
  if (hasFilesData(e) && (--dragDepth <= 0 || !e.relatedTarget)) {
    dragDepth = 0;
    document.body.classList.remove('window-dragging');
  }
});

// High-speed parallel entry traversal for huge drops
async function traverseFileSystemEntries(entryList) {
  const dirQueue = [];
  const fileJobs = [];
  let foundCount = 0;

  for (const en of entryList) {
    if (en.isFile) {
      fileJobs.push(new Promise((res, rej) => en.file(f => {
        addFile(en.fullPath, f);
        foundCount++;
        res();
      }, rej)));
    } else if (en.isDirectory) {
      dirQueue.push(en);
    }
  }

  // Concurrency-controlled directory queue processing
  while (dirQueue.length > 0) {
    const dir = dirQueue.shift();
    const reader = dir.createReader();
    let batch;
    do {
      batch = await new Promise((res, rej) => reader.readEntries(res, rej));
      for (const child of batch) {
        if (child.isFile) {
          fileJobs.push(new Promise((res, rej) => child.file(f => {
            addFile(child.fullPath, f);
            foundCount++;
            res();
          }, rej)));
        } else if (child.isDirectory) {
          dirQueue.push(child);
        }
      }
      if (foundCount % 200 === 0) {
        srcMsg(`Discovered ${foundCount.toLocaleString()} files…`);
        await sleep(0);
      }
    } while (batch.length > 0);
  }

  // Resolve files with a concurrency pool of 32
  const CONCURRENCY = 32;
  for (let i = 0; i < fileJobs.length; i += CONCURRENCY) {
    await Promise.all(fileJobs.slice(i, i + CONCURRENCY));
    if (i % 256 === 0) await sleep(0);
  }
}

document.addEventListener('drop', async e => {
  if (!hasFilesData(e)) return;
  e.preventDefault();
  dragDepth = 0;
  document.body.classList.remove('window-dragging');
  if (busy) return;

  const entries = [], loose = [];
  for (const i of e.dataTransfer.items) {
    if (i.kind !== 'file') continue;
    const en = i.webkitGetAsEntry && i.webkitGetAsEntry();
    if (en) entries.push(en);
    else { const f = i.getAsFile(); if (f) loose.push(f); }
  }

  srcMsg('Scanning dropped items…');
  const beforeCount = files.size;
  let hasZip = false;

  try {
    for (const f of loose) {
      if (/\.zip$/i.test(f.name)) { hasZip = true; await addZip(f); }
      else addFile(f.name, f);
    }
    
    const zipEntries = [];
    const nonZipEntries = [];
    for (const en of entries) {
      if (en.isFile && /\.zip$/i.test(en.name)) zipEntries.push(en);
      else nonZipEntries.push(en);
    }

    for (const en of zipEntries) {
      hasZip = true;
      await addZip(await new Promise((res, rej) => en.file(res, rej)));
    }

    if (nonZipEntries.length > 0) {
      await traverseFileSystemEntries(nonZipEntries);
    }

    if (!hasZip) await reportFiles(files.size - beforeCount);
  } catch (err) {
    srcMsg('Error reading dropped files: ' + err.message);
  }
  refresh();
});

/* ---------- Manifest & Filtering Logic ---------- */
function getCustomRegex() {
  const val = $('#customIgnore').value.trim();
  if (!val) return null;
  const parts = val.split(',').map(s => s.trim()).filter(Boolean);
  if (!parts.length) return null;
  const escaped = parts.map(p => p.replace(/[.+^${}()|[\]\\]/g, '\\$&').replace(/\*/g, '.*'));
  try {
    return new RegExp(`(^|/)(${escaped.join('|')})($|/)`, 'i');
  } catch {
    return null;
  }
}

function computeCurrentManifest() {
  const skipOn = $('#skip').checked;
  const customRegex = getCustomRegex();
  const out = [], bigFiles = [], hardRejects = [];
  let junkCount = 0;

  for (const [path, file] of files) {
    if (GITDIR_REGEX.test(path) || (skipOn && DEFAULT_SKIP_REGEX.test(path)) || (customRegex && customRegex.test(path)) || matchesGitignore(path)) {
      junkCount++;
      continue;
    }
    if (file.size > HARD_LIMIT) {
      hardRejects.push({ path, file });
      continue;
    }
    if (file.size > MAX_FILE_SIZE) {
      bigFiles.push({ path, file });
    }
    out.push({ path, file });
  }

  // Path Prefixing
  const keepRoot = $('#keepRoot').checked;
  const prefix = $('#prefix').value.trim().replace(/^\/+|\/+$/g, '');
  let commonRoot = '';

  if (!keepRoot && out.length > 0) {
    const firstSlash = out[0].path.indexOf('/');
    if (firstSlash !== -1) {
      const cand = out[0].path.slice(0, firstSlash + 1);
      if (out.every(o => o.path.startsWith(cand))) commonRoot = cand;
    }
  }

  for (const o of out) {
    let rel = commonRoot ? o.path.slice(commonRoot.length) : o.path;
    o.repoPath = prefix ? `${prefix}/${rel}` : rel;
  }

  return { out, junkCount, bigFiles, hardRejects };
}

/* ---------- Remote Diff Engine (Batched & Cached) ---------- */
let diffCheckTimer = null;
async function checkRemoteDiff() {
  const slug = slugOf();
  const wantBranch = $('#branch').value.trim();
  if (!token || !slug || !/^[\w.-]+\/[\w.-]+$/.test(slug)) return;

  try {
    const repo = await gh('/repos/' + slug);
    const branch = wantBranch || repo.default_branch || 'main';

    // Safely check if branch ref exists (returns 404 if repository is empty or branch does not exist)
    let refData = null;
    try {
      refData = await gh('/repos/' + slug + '/git/ref/heads/' + enc(branch));
    } catch (refErr) {
      // Empty repo or new branch: treat all staged files as new
      remoteTreeMap.clear();
      updateDiffUI();
      return;
    }

    if (!refData || !refData.object || !refData.object.sha) {
      remoteTreeMap.clear();
      updateDiffUI();
      return;
    }

    const baseSha = refData.object.sha;
    const commit = await gh('/repos/' + slug + '/git/commits/' + baseSha);
    const treeData = await gh('/repos/' + slug + '/git/trees/' + commit.tree.sha + '?recursive=1');

    remoteTreeMap.clear();
    if (treeData && treeData.tree) {
      treeData.tree.forEach(node => {
        if (node.type === 'blob') {
          remoteTreeMap.set(node.path, node.sha);
        }
      });
    }

    // Compute hashes for staged files with a concurrency pool of 8
    const { out } = computeCurrentManifest();
    const pending = out.filter(o => !fileGitShaMap.has(o.repoPath));
    const CONCURRENCY = 8;

    for (let i = 0; i < pending.length; i += CONCURRENCY) {
      const slice = pending.slice(i, i + CONCURRENCY);
      await Promise.all(slice.map(async item => {
        const sha = await computeGitBlobSha(item.file);
        if (sha) fileGitShaMap.set(item.repoPath, sha);
      }));
      // Debounce UI update
      clearTimeout(diffCheckTimer);
      diffCheckTimer = setTimeout(updateDiffUI, 80);
    }

    updateDiffUI();
  } catch(e) {
    remoteTreeMap.clear();
    updateDiffUI();
  }
}

function getFileDiffStatus(repoPath) {
  if (!remoteTreeMap.size) return 'unknown';
  if (!remoteTreeMap.has(repoPath)) return 'new';
  const localSha = fileGitShaMap.get(repoPath);
  if (!localSha) return 'checking';
  return localSha === remoteTreeMap.get(repoPath) ? 'same' : 'mod';
}

function updateDiffUI() {
  const { out } = computeCurrentManifest();
  if (!out.length || !remoteTreeMap.size) {
    $('#diffBar').hidden = true;
    return;
  }

  let countNew = 0, countMod = 0, countSame = 0;
  out.forEach(item => {
    const status = getFileDiffStatus(item.repoPath);
    if (status === 'new') countNew++;
    else if (status === 'mod') countMod++;
    else if (status === 'same') countSame++;
  });

  $('#diffBar').hidden = false;
  $('#diffNew').textContent = `+${countNew.toLocaleString()} new`;
  $('#diffMod').textContent = `~${countMod.toLocaleString()} modified`;
  $('#diffSame').textContent = `${countSame.toLocaleString()} identical`;
}

// Diff filter buttons
$$('.diff-pill').forEach(btn => {
  btn.addEventListener('click', () => {
    $$('.diff-pill').forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    activeDiffFilter = btn.dataset.diff;
    renderManifestRows();
  });
});

/* ---------- Clean ZIP Exporter ---------- */
async function downloadCleanZip() {
  const { out } = computeCurrentManifest();
  if (!out.length) return;
  try {
    showToast('Packing clean project ZIP…', 'info');
    await loadZipLib();
    const zip = new JSZip();
    for (const item of out) {
      zip.file(item.repoPath, item.file);
    }
    const blob = await zip.generateAsync({ type: 'blob' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = `clean-${slugOf().split('/').pop() || 'project'}.zip`;
    a.click();
    URL.revokeObjectURL(url);
    showToast('Clean project ZIP downloaded!', 'ok');
    playSound('success');
  } catch(err) {
    showToast('Failed to export ZIP: ' + err.message, 'err');
  }
}
$('#downloadZipBtn')?.addEventListener('click', downloadCleanZip);

/* ---------- Stepper State Sync ---------- */
function syncStepperState() {
  const hasToken = Boolean(token);
  const slug = slugOf();
  const hasDest = Boolean(slug && (($('#create')?.checked && /^[\w.-]+$/.test(slug)) || /^[\w.-]+\/[\w.-]+$/.test(slug)));
  const hasFiles = files.size > 0;

  const t1 = $('#tab1'), t2 = $('#tab2'), t3 = $('#tab3'), t4 = $('#tab4');
  if (t1) {
    t1.classList.toggle('completed', hasToken);
    t1.classList.toggle('active', !hasToken);
  }
  if (t2) {
    t2.classList.toggle('completed', hasToken && hasDest);
    t2.classList.toggle('active', hasToken && !hasDest);
  }
  if (t3) {
    t3.classList.toggle('completed', hasFiles);
    t3.classList.toggle('active', hasToken && hasDest && !hasFiles);
  }
  if (t4) {
    t4.classList.toggle('active', hasToken && hasDest && hasFiles);
  }
}

// Stepper click handlers to scroll to cards
$('#tab1')?.addEventListener('click', () => $('#step1-title')?.scrollIntoView({ behavior: 'smooth' }));
$('#tab2')?.addEventListener('click', () => $('#step2-title')?.scrollIntoView({ behavior: 'smooth' }));
$('#tab3')?.addEventListener('click', () => $('#step3-title')?.scrollIntoView({ behavior: 'smooth' }));
$('#tab4')?.addEventListener('click', () => $('#step4-title')?.scrollIntoView({ behavior: 'smooth' }));

/* ---------- Tree View Generator ---------- */
function buildTreeStructure(items) {
  const root = { name: '', isDir: true, children: new Map(), size: 0 };
  for (const item of items) {
    const parts = item.repoPath.split('/');
    let cur = root;
    for (let i = 0; i < parts.length; i++) {
      const part = parts[i];
      const isFile = i === parts.length - 1;
      if (!cur.children.has(part)) {
        cur.children.set(part, {
          name: part,
          isDir: !isFile,
          children: new Map(),
          item: isFile ? item : null,
          size: 0
        });
      }
      cur = cur.children.get(part);
      cur.size += item.file.size;
    }
  }
  return root;
}

function renderTree(node, container, depth = 0) {
  const sorted = Array.from(node.children.values()).sort((a, b) => {
    if (a.isDir !== b.isDir) return a.isDir ? -1 : 1;
    return a.name.localeCompare(b.name);
  });

  for (const child of sorted) {
    if (child.isDir) {
      const f = document.createElement('div');
      f.className = 'tree-folder';
      f.innerHTML = `
        <div class="tree-folder-title">
          <svg class="icon icon-sm" viewBox="0 0 24 24"><path d="m6 9 6 6 6-6"/></svg>
          <svg class="icon icon-sm" style="color:var(--accent);" viewBox="0 0 24 24"><path d="M4 20h16a2 2 0 0 0 2-2V8a2 2 0 0 0-2-2h-7.93a2 2 0 0 1-1.66-.9l-.82-1.2A2 2 0 0 0 7.93 3H4a2 2 0 0 0-2 2v13c0 1.1.9 2 2 2Z"/></svg>
          <span style="font-weight:600;">${escapeHTML(child.name)}</span>
          <span style="font-size:0.6875rem; color:var(--muted); margin-left:auto;">${fmt(child.size)}</span>
        </div>
        <div class="tree-children"></div>
      `;
      const title = f.querySelector('.tree-folder-title');
      const childrenBox = f.querySelector('.tree-children');
      title.onclick = () => {
        childrenBox.hidden = !childrenBox.hidden;
        title.querySelector('.icon').style.transform = childrenBox.hidden ? 'rotate(-90deg)' : '';
      };
      renderTree(child, childrenBox, depth + 1);
      container.append(f);
    } else {
      const el = document.createElement('div');
      el.className = 'tree-file';
      const ext = getExt(child.item.repoPath);
      el.innerHTML = `
        <div style="display:flex; align-items:center; gap:0.4rem; overflow:hidden;">
          <span class="ext-badge ${['js','ts','tsx','py','json','css','html','md'].includes(ext) ? ext : 'other'}">${ext || '·'}</span>
          <span class="file-path" style="white-space:nowrap; overflow:hidden; text-overflow:ellipsis;">${escapeHTML(child.name)}</span>
        </div>
        <span class="file-size">${fmt(child.item.file.size)}</span>
      `;
      el.querySelector('.file-path').onclick = () => openFilePreview(child.item);
      container.append(el);
    }
  }
}

// Tree view expand / collapse
$('#expandAllBtn')?.addEventListener('click', () => {
  $$('.tree-children').forEach(el => el.hidden = false);
  $$('.tree-folder-title .icon').forEach(el => el.style.transform = '');
});
$('#collapseAllBtn')?.addEventListener('click', () => {
  $$('.tree-children').forEach(el => el.hidden = true);
  $$('.tree-folder-title .icon').forEach(el => el.style.transform = 'rotate(-90deg)');
});

// View switching
$('#tabFlat')?.addEventListener('click', () => {
  currentView = 'flat';
  $('#tabFlat').classList.add('active');
  $('#tabTree').classList.remove('active');
  $('#manifestWrap .manifest-table-header').hidden = false;
  $('#manifestWrap .virtual-spacer').hidden = false;
  $('#treeView').hidden = true;
  $('#treeControls').hidden = true;
});
$('#tabTree')?.addEventListener('click', () => {
  currentView = 'tree';
  $('#tabTree').classList.add('active');
  $('#tabFlat').classList.remove('active');
  $('#manifestWrap .manifest-table-header').hidden = true;
  $('#manifestWrap .virtual-spacer').hidden = true;
  $('#treeView').hidden = false;
  $('#treeControls').hidden = false;

  const { out } = computeCurrentManifest();
  const treeContainer = $('#treeView');
  treeContainer.textContent = '';
  const root = buildTreeStructure(out);
  renderTree(root, treeContainer);
});

/* ==========================================================================
   Virtual Scroller Engine (60fps on 50,000+ files)
   ========================================================================== */
function renderManifestRows() {
  const q = ($('#filter')?.value || '').trim().toLowerCase();
  const { out } = computeCurrentManifest();

  // Filter by query and active diff
  let filtered = out;
  if (q) {
    filtered = filtered.filter(o => o.repoPath.toLowerCase().includes(q));
  }
  if (activeDiffFilter !== 'all') {
    filtered = filtered.filter(o => {
      if (activeDiffFilter === 'secret') return fileSecretsMap.has(o.path);
      return getFileDiffStatus(o.repoPath) === activeDiffFilter;
    });
  }

  currentFilteredList = filtered;
  const container = $('#manifestWrap');
  const spacer = $('.virtual-spacer');
  const list = $('#manifest');

  const total = filtered.length;
  const totalHeight = total * ROW_HEIGHT;
  if (spacer) spacer.style.height = `${totalHeight}px`;

  // Virtual slice calculation
  const scrollTop = container ? container.scrollTop : 0;
  const viewportHeight = container ? container.clientHeight : 400;

  const startIndex = Math.max(0, Math.floor(scrollTop / ROW_HEIGHT) - 5);
  const visibleCount = Math.ceil(viewportHeight / ROW_HEIGHT) + 10;
  const endIndex = Math.min(total, startIndex + visibleCount);

  list.textContent = '';
  list.style.transform = `translateY(${startIndex * ROW_HEIGHT}px)`;
  rowMap = new Map();

  for (let idx = startIndex; idx < endIndex; idx++) {
    const o = filtered[idx];
    const li = document.createElement('li');
    li.className = 'manifest-row' + (fileSecretsMap.has(o.path) ? ' has-secret' : '');
    li.dataset.path = o.path;

    const ext = getExt(o.repoPath);
    const isWarn = o.file.size > MAX_FILE_SIZE;
    const diffStatus = getFileDiffStatus(o.repoPath);
    const hasSecret = fileSecretsMap.has(o.path);

    // Path decomposition (directory dimmed, filename bold)
    const lastSlash = o.repoPath.lastIndexOf('/');
    const dir = lastSlash !== -1 ? o.repoPath.slice(0, lastSlash + 1) : '';
    const name = lastSlash !== -1 ? o.repoPath.slice(lastSlash + 1) : o.repoPath;

    let statusBadge = '';
    if (hasSecret) {
      statusBadge = '<span class="secret-badge">SECRET</span>';
    } else if (diffStatus === 'new') {
      statusBadge = '<span class="diff-badge new">+NEW</span>';
    } else if (diffStatus === 'mod') {
      statusBadge = '<span class="diff-badge mod">~MOD</span>';
    }

    const badgeCls = ['js','ts','tsx','py','json','css','html','md'].includes(ext) ? ext : 'other';

    li.innerHTML = `
      <span class="ext-badge ${badgeCls}">${ext || '·'}</span>
      <span class="file-path" title="${escapeHTML(o.repoPath)}">
        <span class="file-dir">${escapeHTML(dir)}</span><span class="file-name">${escapeHTML(name)}</span>
      </span>
      <span class="diff-status-col">${statusBadge}</span>
      <span class="file-size">${fmt(o.file.size)}</span>
      <button class="action-icon-btn remove-btn" type="button" aria-label="Remove file" title="Remove file">×</button>
    `;

    li.querySelector('.file-path').onclick = () => openFilePreview(o);
    li.querySelector('.remove-btn').onclick = (e) => {
      e.stopPropagation();
      files.delete(o.path);
      refresh();
      showToast(`Removed ${name}`, 'info');
    };

    list.append(li);
    rowMap.set(o.path, li);
  }
}

// Attach scroll listener with requestAnimationFrame to drive virtual scroller
let scrollRaf = null;
$('#manifestWrap')?.addEventListener('scroll', () => {
  if (currentView !== 'flat') return;
  if (!scrollRaf) {
    scrollRaf = requestAnimationFrame(() => {
      renderManifestRows();
      scrollRaf = null;
    });
  }
});

// Search input listener
let filterRaf = null;
$('#filter')?.addEventListener('input', () => {
  if (!filterRaf) {
    filterRaf = requestAnimationFrame(() => {
      if ($('#manifestWrap')) $('#manifestWrap').scrollTop = 0;
      renderManifestRows();
      filterRaf = null;
    });
  }
});

/* ---------- Main UI Refresh Loop ---------- */
let refreshTimer = null;
function refresh() {
  clearTimeout(refreshTimer);
  refreshTimer = setTimeout(doRefresh, 16);
}

function doRefresh() {
  const { out, junkCount, bigFiles, hardRejects } = computeCurrentManifest();
  const empty = files.size === 0;

  $('#emptyReview').hidden = !empty;
  $('#filledReview').hidden = empty;

  // Stats bar animation
  animateNumber($('#cnt'), out.length, v => v.toLocaleString());
  const totalBytes = out.reduce((sum, o) => sum + o.file.size, 0);
  $('#size').textContent = fmt(totalBytes);

  const estBlobs = out.filter(o => o.file.size > INLINE_MAX || BINARY_EXTS.has(getExt(o.repoPath))).length;
  const estTrees = Math.ceil(out.length / TREE_MAX_ENTRIES);
  animateNumber($('#apiEst'), estBlobs + estTrees + 2);

  // Background Secret Scanning
  scanAllStagedSecrets(out).then(secretCount => {
    const secBanner = $('#securityBanner');
    if (secretCount > 0) {
      secBanner.hidden = false;
      $('#secretCount').textContent = secretCount;
    } else {
      secBanner.hidden = true;
    }
  });

  // Render Manifest rows
  renderManifestRows();

  // Bottom action dock update & Inline Review Upload button
  const goBtn = $('#go');
  const inlineGoBtn = $('#inlineGo');
  const barMain = $('#barMain');
  const barSub = $('#barSub');

  if (empty) {
    barMain.textContent = 'BUFFER IDLE // NO PAYLOAD DETECTED';
    barSub.textContent = 'Ingest project directory or archive in Step 03 to arm commit';
    if (goBtn) goBtn.disabled = true;
    if (inlineGoBtn) inlineGoBtn.disabled = true;
  } else {
    barMain.textContent = `PAYLOAD ARMED: ${out.length.toLocaleString()} FILES (${fmt(totalBytes)})`;
    barSub.textContent = `TARGET VECTOR: ${slugOf() || 'UNRESOLVED'} // MERKLE BUFFER READY`;
    const canUpload = !!token && !!slugOf();
    if (goBtn) goBtn.disabled = !canUpload;
    if (inlineGoBtn) inlineGoBtn.disabled = !canUpload;
  }

  // Warnings / Hints
  const note = $('#note');
  if (hardRejects.length) {
    note.hidden = false;
    note.textContent = `⚠️ ${hardRejects.length} file(s) exceed GitHub's 100MB hard limit and will be skipped.`;
  } else if (bigFiles.length) {
    note.hidden = false;
    note.textContent = `ℹ️ ${bigFiles.length} file(s) exceed 50MB. They will be uploaded sequentially.`;
  } else {
    note.hidden = true;
  }

  syncStepperState();
}

$('#clear')?.addEventListener('click', () => {
  files.clear();
  remoteTreeMap.clear();
  fileGitShaMap.clear();
  fileSecretsMap.clear();
  gitignoreRules = [];
  $('#gitignoreOption').hidden = true;
  $('#result').hidden = true;
  const overlay = $('#pipelineOverlay');
  if (overlay) overlay.hidden = true;
  const card = $('#pipelineCard');
  if (card) {
    card.hidden = true;
    card.classList.remove('pipeline-completed', 'pipeline-error');
  }
  msg('');
  srcMsg('');
  refresh();
  showToast('All files cleared', 'info');
  playSound('pop');
});

/* ---------- File Preview Modal ---------- */
const modal = $('#previewModal');
$('#closeModal').onclick = () => modal?.close();

async function openFilePreview(item) {
  if (!modal) return;
  const title = $('#previewTitle');
  const body = $('#previewBody');
  const file = item.file;
  title.textContent = item.repoPath;
  body.innerHTML = '<div style="color:var(--muted); font-size:0.8125rem;">Loading preview…</div>';
  modal.showModal();

  $('#downloadFileBtn').onclick = () => {
    const url = URL.createObjectURL(file);
    const a = document.createElement('a');
    a.href = url;
    a.download = item.repoPath.split('/').pop();
    a.click();
    URL.revokeObjectURL(url);
  };

  const copyBtn = $('#copyContentBtn');
  copyBtn.onclick = async () => {
    try {
      const text = await file.text();
      await navigator.clipboard.writeText(text);
      $('#copyContentText').textContent = 'Copied!';
      showToast('File contents copied to clipboard', 'ok');
      playSound('pop');
      setTimeout(() => $('#copyContentText').textContent = 'Copy', 1500);
    } catch {
      showToast('Clipboard access denied', 'err');
    }
  };

  try {
    const ext = getExt(item.repoPath);
    if (['png', 'jpg', 'jpeg', 'gif', 'svg', 'webp'].includes(ext)) {
      const url = URL.createObjectURL(file);
      body.innerHTML = `<img class="preview-img" src="${url}" alt="Preview of ${escapeHTML(item.repoPath)}">`;
    } else {
      // Read first 64KB for safe text preview
      const slice = file.slice(0, 65536);
      const text = asText(await slice.arrayBuffer());
      if (text !== null) {
        const hits = fileSecretsMap.get(item.path);
        let secretWarning = '';
        if (hits && hits.length) {
          secretWarning = `
            <div style="background:var(--err-subtle); border:1px solid var(--err-border); color:var(--err); padding:0.65rem; border-radius:var(--radius-sm); font-size:0.75rem; margin-bottom:0.75rem;">
              ⚠️ <strong>Security Notice:</strong> Staged credential matches: ${hits.map(h => `${h.type} (${h.preview})`).join(', ')}
            </div>
          `;
        }
        body.innerHTML = `
          ${secretWarning}
          <pre class="preview-code">${escapeHTML(text)}${file.size > 65536 ? '\n\n/* [Truncated: showing first 64 KB of file] */' : ''}</pre>
        `;
      } else {
        body.innerHTML = `
          <div style="text-align:center; padding:2rem; color:var(--muted);">
            <p style="margin:0; font-weight:600;">Binary File</p>
            <span style="font-family:var(--font-mono); font-size:0.75rem;">Size: ${fmt(file.size)}</span>
          </div>
        `;
      }
    }
  } catch (err) {
    body.textContent = 'Could not preview file: ' + err.message;
  }
}

// Security Confirm Dialog
const secModal = $('#secretConfirmModal');
$('#cancelSecretPush')?.addEventListener('click', () => secModal?.close());
$('#proceedSecretPush')?.addEventListener('click', () => {
  secModal?.close();
  executeUpload(true);
});

/* ---------- Keyboard Shortcuts ---------- */
document.addEventListener('keydown', e => {
  if (e.key === '/' && !['INPUT', 'TEXTAREA'].includes(document.activeElement?.tagName)) {
    e.preventDefault();
    $('#filter')?.focus();
  }
  if (e.key === '?' && !['INPUT', 'TEXTAREA'].includes(document.activeElement?.tagName)) {
    e.preventDefault();
    shortcutsModal?.showModal();
  }
  if ((e.metaKey || e.ctrlKey) && e.key.toLowerCase() === 'o') {
    e.preventDefault();
    $('#bFolder')?.click();
  }
  if ((e.metaKey || e.ctrlKey) && e.key === 'Enter') {
    if (!$('#go')?.disabled) {
      e.preventDefault();
      $('#go')?.click();
    }
  }
  if (e.key === 'Escape') {
    if (modal?.open) modal.close();
    if (secModal?.open) secModal.close();
    if (shortcutsModal?.open) shortcutsModal.close();
    const overlay = $('#pipelineOverlay');
    if (overlay && !overlay.hidden && !busy) {
      overlay.hidden = true;
    }
  }
});

// Centered Pipeline Modal Dismiss & Re-open Handlers
$('#pipelineCloseBtn')?.addEventListener('click', () => {
  if (busy) {
    if (confirm('An upload is currently in progress. Cancel upload?')) {
      cancelled = true;
      abortCtrl?.abort();
      showToast('Cancelling upload…', 'warn');
    }
  } else {
    const overlay = $('#pipelineOverlay');
    if (overlay) overlay.hidden = true;
  }
});

$('#pipelineOverlay')?.addEventListener('click', (e) => {
  if (e.target === $('#pipelineOverlay') && !busy) {
    $('#pipelineOverlay').hidden = true;
  }
});

$('#barMain')?.addEventListener('click', () => {
  const overlay = $('#pipelineOverlay');
  const card = $('#pipelineCard');
  if (overlay && card && (!card.hidden || busy)) {
    overlay.hidden = false;
  }
});

/* ---------- GitHub API Client & Resilient Blob Pipeline ---------- */
const CANCELLED_ERR = () => Object.assign(new Error('Operation cancelled by user'), { cancelled: true });

async function gh(path, opts = {}) {
  const method = opts.method || 'GET';
  const url = /^https?:\/\//.test(path) ? path : API + path;
  let attempt = 0;

  while (attempt < 4) {
    attempt++;
    if (cancelled) throw CANCELLED_ERR();

    const res = await fetch(url, {
      ...opts,
      signal: abortCtrl?.signal,
      headers: {
        Authorization: 'token ' + token,
        Accept: 'application/vnd.github+json',
        'X-GitHub-Api-Version': '2022-11-28',
        ...(opts.headers || {})
      }
    });

    // Update live rate limit pill
    const rem = res.headers.get('x-ratelimit-remaining');
    const lim = res.headers.get('x-ratelimit-limit');
    if (rem) $('#rateLimitPill').textContent = `Rate: ${rem}/${lim}`;

    // Handle secondary rate limits (403 / 429)
    if (res.status === 403 || res.status === 429) {
      const retryAfter = parseInt(res.headers.get('retry-after') || '0', 10);
      const waitTime = retryAfter > 0 ? retryAfter * 1000 : Math.pow(2, attempt) * 1500;
      msg(`GitHub rate limit hit. Backing off for ${(waitTime/1000).toFixed(0)}s…`);
      await sleep(waitTime);
      continue;
    }

    if (res.status === 204) return null;
    if (res.ok) return await res.json();

    let errPayload = null;
    try { errPayload = await res.json(); } catch(e) {}
    const err = new Error(errPayload?.message || `GitHub API error: ${res.status}`);
    err.status = res.status;
    err.payload = errPayload;

    if (res.status >= 500 && attempt < 4) {
      await sleep(Math.pow(2, attempt) * 1000);
      continue;
    }

    throw err;
  }
}

function slugOf() {
  const v = $('#repo').value.trim();
  if (!v) return '';
  const m = v.match(/github\.com\/([^\/]+)\/([^\/]+)/);
  if (m) return `${m[1]}/${m[2].replace(/\.git$/, '')}`;
  return v.replace(/^\/+|\/+$/g, '');
}

function badBranch(b) {
  if (!b) return false;
  return /[\s~^:?*[\\]|\.\.|\/\.|\/\/|@\{/.test(b);
}

function msg(text, type = '') {
  const el = $('#msg');
  if (!el) return;
  el.textContent = text;
  el.className = 'status-msg ' + type;
}

function srcMsg(text) {
  const el = $('#srcMsg');
  if (!el) return;
  el.textContent = text;
}

function setBusy(b) {
  busy = b;
  const go = $('#go');
  const goText = $('#goText');
  const inlineGo = $('#inlineGo');
  const inlineGoText = $('#inlineGoText');

  if (go) {
    if (b) {
      go.disabled = true;
      if (goText) goText.textContent = 'DEPLOYING PAYLOAD…';
    } else {
      if (goText) goText.textContent = 'EXECUTE COMMIT PROTOCOL';
    }
  }
  if (inlineGo) {
    if (b) {
      inlineGo.disabled = true;
      if (inlineGoText) inlineGoText.textContent = 'DEPLOYING PAYLOAD…';
    } else {
      if (inlineGoText) inlineGoText.textContent = 'EXECUTE COMMIT PROTOCOL';
    }
  }
  if (!b) refresh();
}

function triggerUpload() {
  if (busy) return;
  const { out } = computeCurrentManifest();
  if (!out.length) return;

  // Pre-commit Secret Safety Guard
  if (fileSecretsMap.size > 0 && !$('#skipSecretsCheck')?.checked) {
    $('#secretModalCount').textContent = fileSecretsMap.size;
    secModal?.showModal();
    playSound('warn');
    return;
  }

  executeUpload(false);
}

$('#go')?.addEventListener('click', triggerUpload);
$('#inlineGo')?.addEventListener('click', triggerUpload);

async function executeUpload(overrideSecrets = false) {
  const { out } = computeCurrentManifest();
  if (!out.length) return;

  token = $('#token').value.trim();
  if (!token) return msg('Please provide your GitHub Personal Access Token in Step 1.', 'err');

  const create = $('#create').checked;
  let slug = slugOf();
  if (create ? !/^[\w.-]+$/.test(slug.split('/').pop()) : !/^[\w.-]+\/[\w.-]+$/.test(slug)) {
    return msg(create ? 'Enter a valid repository name.' : 'Enter destination as owner/repository.', 'err');
  }

  const wantBranch = $('#branch').value.trim();
  const commitTitle = $('#commit').value.trim() || 'Upload files via Folder to GitHub';
  const commitDesc = $('#commitDesc').value.trim();
  const fullCommitMessage = commitDesc ? `${commitTitle}\n\n${commitDesc}` : commitTitle;
  const isPrivate = $('#private').checked;

  if (badBranch(wantBranch)) {
    return msg('Invalid branch name. Avoid spaces and characters like ~ ^ : ? * [ \\ and ".."', 'err');
  }

  // Automatically show uploading status in the middle of the screen
  const overlay = $('#pipelineOverlay');
  if (overlay) overlay.hidden = false;
  const card = $('#pipelineCard');
  if (card) {
    card.hidden = false;
    card.classList.remove('pipeline-completed', 'pipeline-error');
  }
  const errBox = $('#pipelineErrorBox');
  if (errBox) errBox.hidden = true;
  const upActions = $('#pipelineUploadingActions');
  if (upActions) upActions.hidden = false;
  $('#result').hidden = true;

  const cancelBtn = $('#pipelineCancelBtn');
  if (cancelBtn) {
    cancelBtn.onclick = () => {
      if (busy && abortCtrl) {
        cancelled = true;
        abortCtrl.abort();
        showToast('Cancelling upload…', 'warn');
      }
    };
  }

  store.set('f2g.repo', create ? '' : slug);
  store.set('f2g.branch', wantBranch);
  store.set('f2g.prefix', $('#prefix').value.trim());
  if ($('#remember').checked) store.set('f2g.token', token);

  cancelled = false;
  abortCtrl = new AbortController();
  setBusy(true);
  uploadStartTime = Date.now();
  playSound('arm');

  setPipelineStage(1, '01 // CIPHER HANDSHAKE & CLEARANCE…', 'Establishing TLS 1.3 tunnel to ' + slug);

  try {
    let repo;
    if (create) {
      if (!me) await verifyToken();
      if (!me) throw new Error('Token verification required to create repository');
      msg('Creating new repository on GitHub…');
      setPipelineStage(1, 'Creating new repository…', slug);
      repo = await gh('/user/repos', {
        method: 'POST',
        body: JSON.stringify({
          name: slug.split('/').pop(),
          private: isPrivate,
          auto_init: true,
          description: 'Uploaded via Folder to GitHub'
        })
      });
      slug = repo.full_name;
      $('#create').checked = false;
      $('#create').dispatchEvent(new Event('change'));
      $('#repo').value = slug;
      store.set('f2g.repo', slug);

      for (let i = 0; i < 8; i++) {
        try {
          await gh('/repos/' + slug + '/git/ref/heads/' + enc(repo.default_branch));
          break;
        } catch (e) {
          if (e.status !== 404 && e.status !== 409) throw e;
          await sleep(1000);
          if (cancelled) throw CANCELLED_ERR();
        }
      }
    } else {
      msg('Verifying target repository…');
      repo = await gh('/repos/' + slug);
      if (repo.permissions && repo.permissions.push === false) {
        throw new Error('This token does not have write (push) permissions to ' + slug);
      }
    }

    const branch = wantBranch || repo.default_branch || 'main';
    const refPath = b => '/repos/' + slug + '/git/refs/heads/' + enc(b);
    let baseSha = null;
    let parentTreeSha = null;

    try {
      baseSha = (await gh(refPath(branch))).object.sha;
    } catch (e) {
      if (e.status === 404 || e.status === 409) {
        // If target branch does not exist, check default_branch for existing commits
        if (branch !== repo.default_branch && repo.default_branch) {
          try {
            baseSha = (await gh(refPath(repo.default_branch))).object.sha;
          } catch(err) {
            baseSha = null;
          }
        } else {
          baseSha = null;
        }
      } else {
        throw e;
      }
    }

    if (baseSha) {
      try {
        const parentCommit = await gh('/repos/' + slug + '/git/commits/' + baseSha);
        parentTreeSha = parentCommit?.tree?.sha || null;
      } catch(e) {
        baseSha = null;
        parentTreeSha = null;
      }
    }

    // Filter unchanged files if requested
    const skipUnchanged = $('#skipUnchanged')?.checked;
    const uploadTargets = (skipUnchanged && baseSha) 
      ? out.filter(o => getFileDiffStatus(o.repoPath) !== 'same')
      : out;

    if (!uploadTargets.length) {
      throw Object.assign(new Error('All staged files are identical to remote. Nothing to commit.'), { identical: true });
    }

    // Prepare entries & Blobs
    const totalBytes = uploadTargets.reduce((s, o) => s + o.file.size, 0);
    const entries = new Array(uploadTargets.length);
    let nextIndex = 0, doneCount = 0, sentBytes = 0;
    let bigFileGate = Promise.resolve();

    setPipelineStage(2, 'Uploading Blobs (0/' + uploadTargets.length + ')', 'Initializing workers…', '0 KB/s');

    const uploadBlob = async o => {
      const b = await gh('/repos/' + slug + '/git/blobs', {
        method: 'POST',
        body: JSON.stringify({ content: await toBase64(o.file), encoding: 'base64' })
      });
      return { path: o.repoPath, mode: '100644', type: 'blob', sha: b.sha };
    };

    async function prepareFileEntry(o) {
      if (o.file.size > 0 && o.file.size <= INLINE_MAX) {
        const text = asText(await o.file.arrayBuffer());
        if (text !== null) {
          return { path: o.repoPath, mode: '100644', type: 'blob', content: text };
        }
      }

      if (o.file.size <= BIG_FILE_THRESHOLD) {
        return uploadBlob(o);
      }

      const prevGate = bigFileGate;
      let releaseGate;
      bigFileGate = new Promise(r => releaseGate = r);
      await prevGate;
      try {
        if (cancelled) throw CANCELLED_ERR();
        return await uploadBlob(o);
      } finally {
        releaseGate();
      }
    }

    async function uploadWorker() {
      while (nextIndex < uploadTargets.length && !cancelled) {
        const i = nextIndex++;
        const o = uploadTargets[i];
        const li = rowMap.get(o.path);
        if (li) li.classList.add('uploading');

        try {
          entries[i] = await prepareFileEntry(o);
        } catch (e) {
          cancelled = true;
          abortCtrl.abort();
          throw e;
        }

        doneCount++;
        sentBytes += o.file.size;
        const pct = (sentBytes / Math.max(totalBytes, 1)) * 92;
        $('#prog').value = pct;

        const elapsed = (Date.now() - uploadStartTime) / 1000;
        const speed = elapsed > 0 ? sentBytes / elapsed : 0;
        const eta = speed > 0 ? Math.ceil((totalBytes - sentBytes) / speed) : 0;

        $('#barMain').textContent = `Uploading: ${doneCount} of ${uploadTargets.length} (${fmt(sentBytes)} / ${fmt(totalBytes)})`;
        $('#barSub').textContent = `${fmt(speed)}/s • ETA: ${eta}s remaining`;
        msg(`Uploading files (${Math.round(pct)}%)…`);

        setPipelineStage(2, `02 // STREAMING BLOBS [${doneCount}/${uploadTargets.length}]`, o.repoPath, `${fmt(speed)}/s`);

        if (li) {
          li.classList.remove('uploading');
          li.classList.add('done');
        }
      }
    }

    const CONCURRENCY = Math.min(8, Math.max(1, uploadTargets.length));
    await Promise.all(Array.from({ length: CONCURRENCY }, uploadWorker));
    if (cancelled) throw CANCELLED_ERR();

    msg('Constructing Git tree…');
    setPipelineStage(3, '03 // COMPOSING MERKLE TREE…', 'Chaining directory tree objects…');

    const treeList = entries.slice();
    let treeSha = parentTreeSha, chunk = [], currentChunkSize = 0;
    const flushTreeChunk = async () => {
      if (!chunk.length) return;
      const payload = treeSha 
        ? { base_tree: treeSha, tree: chunk } 
        : { tree: chunk };
      treeSha = (await gh('/repos/' + slug + '/git/trees', {
        method: 'POST',
        body: JSON.stringify(payload)
      })).sha;
      chunk = [];
      currentChunkSize = 0;
    };

    for (const e of treeList) {
      const entryLen = (e.content ? e.content.length : 0) + 160;
      if (chunk.length && (currentChunkSize + entryLen > TREE_MAX_CHARS || chunk.length >= TREE_MAX_ENTRIES)) {
        await flushTreeChunk();
      }
      chunk.push(e);
      currentChunkSize += entryLen;
    }
    await flushTreeChunk();

    msg('Creating Git commit object…');
    setPipelineStage(4, '04 // CRYPTOGRAPHIC COMMIT MUTATION…', 'Authoring single atomic Git commit…');

    const commitObj = await gh('/repos/' + slug + '/git/commits', {
      method: 'POST',
      body: JSON.stringify({
        message: fullCommitMessage,
        tree: treeSha,
        parents: baseSha ? [baseSha] : []
      })
    });

    msg('Publishing commit to ' + branch + '…');
    setPipelineStage(5, '05 // OVERRIDING REMOTE HEAD POINTER…', 'Overriding branch reference pointer…');

    let refUpdated = false;
    try {
      await gh(refPath(branch), {
        method: 'PATCH',
        body: JSON.stringify({ sha: commitObj.sha, force: true })
      });
      refUpdated = true;
    } catch (patchErr) {
      if (patchErr.status !== 404 && patchErr.status !== 422) {
        throw patchErr;
      }
    }

    if (!refUpdated) {
      try {
        await gh('/repos/' + slug + '/git/refs', {
          method: 'POST',
          body: JSON.stringify({ ref: 'refs/heads/' + branch, sha: commitObj.sha })
        });
      } catch (postErr) {
        // If reference already exists (422), force-update via PATCH
        if (postErr.status === 422) {
          await gh(refPath(branch), {
            method: 'PATCH',
            body: JSON.stringify({ sha: commitObj.sha, force: true })
          });
        } else {
          throw postErr;
        }
      }
    }

    $('#prog').value = 100;
    msg(''); // Clear any floating raw text
    const elapsedSec = ((Date.now() - uploadStartTime) / 1000).toFixed(1);
    setPipelineStage(5, '✓ PAYLOAD DEPLOYED // COMMIT MUTATION PUBLISHED', '', `Done in ${elapsedSec}s`, true);

    const pf = $('#pipelineFile');
    if (pf) pf.hidden = true;

    // Render Success Card
    const resultCard = $('#result');
    resultCard.hidden = false;
    $('#resultMeta').innerHTML = `
      <div class="result-meta-grid">
        <div class="meta-row">
          <span class="meta-label">
            <svg class="icon icon-sm" viewBox="0 0 24 24"><path d="M15 22v-4a4.8 4.8 0 0 0-1-3.5c3 0 6-2 6-5.5.08-1.25-.27-2.48-1-3.5.28-1.15.28-2.35 0-3.5 0 0-1 0-3 1.5-2.64-.5-5.36-.5-8 0C6 2 5 2 5 2c-.3 1.15-.3 2.35 0 3.5A5.403 5.403 0 0 0 4 9c0 3.5 3 5.5 6 5.5-.39.49-.68 1.05-.85 1.65-.17.6-.22 1.23-.15 1.85v4"/><path d="M9 18c-4.51 2-5-2-7-2"/></svg>
            Repository
          </span>
          <span class="meta-val">
            <a href="https://github.com/${escapeHTML(slug)}" target="_blank" rel="noopener" class="deploy-link">
              <strong>${escapeHTML(slug)}</strong>
              <svg class="icon icon-xs" viewBox="0 0 24 24"><path d="M18 13v6a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h6"/><polyline points="15 3 21 3 21 9"/><line x1="10" y1="14" x2="21" y2="3"/></svg>
            </a>
          </span>
        </div>
        <div class="meta-row">
          <span class="meta-label">
            <svg class="icon icon-sm" viewBox="0 0 24 24"><line x1="6" y1="3" x2="6" y2="15"/><circle cx="18" cy="6" r="3"/><circle cx="6" cy="18" r="3"/><path d="M18 9a9 9 0 0 1-9 9"/></svg>
            Branch
          </span>
          <span class="meta-val">
            <a href="https://github.com/${escapeHTML(slug)}/tree/${encodeURIComponent(branch)}" target="_blank" rel="noopener" class="deploy-link">
              <span class="branch-pill">${escapeHTML(branch)}</span>
              <svg class="icon icon-xs" viewBox="0 0 24 24"><path d="M18 13v6a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h6"/><polyline points="15 3 21 3 21 9"/><line x1="10" y1="14" x2="21" y2="3"/></svg>
            </a>
          </span>
        </div>
        <div class="meta-row">
          <span class="meta-label">
            <svg class="icon icon-sm" viewBox="0 0 24 24"><circle cx="12" cy="12" r="3"/><line x1="3" y1="12" x2="9" y2="12"/><line x1="15" y1="12" x2="21" y2="12"/></svg>
            Commit SHA
          </span>
          <span class="meta-val">
            <span class="sha-badge" id="shaPill">
              <code>${commitObj.sha.slice(0, 7)}</code>
              <button class="copy-sha-btn" id="copyShaBtn" type="button" title="Copy full 40-character SHA">
                <svg class="icon icon-sm" viewBox="0 0 24 24"><rect width="14" height="14" x="8" y="8" rx="2" ry="2"/><path d="M4 16c-1.1 0-2-.9-2-2V4c0-1.1.9-2 2-2h10c1.1 0 2 .9 2 2"/></svg>
              </button>
            </span>
          </span>
        </div>
        <div class="meta-row">
          <span class="meta-label">
            <svg class="icon icon-sm" viewBox="0 0 24 24"><path d="M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z"/><polyline points="14 2 14 8 20 8"/><line x1="16" y1="13" x2="8" y2="13"/><line x1="16" y1="17" x2="8" y2="17"/></svg>
            Summary
          </span>
          <span class="meta-val deploy-summary-text">
            ${uploadTargets.length} file${uploadTargets.length === 1 ? '' : 's'} (${fmt(totalBytes)}) • <em>"${escapeHTML(commitTitle)}"</em>
          </span>
        </div>
      </div>
    `;

    $('#copyShaBtn').onclick = () => {
      navigator.clipboard.writeText(commitObj.sha);
      showToast('Copied full SHA: ' + commitObj.sha, 'ok');
      const pill = $('#shaPill');
      if (pill) {
        pill.classList.add('copied');
        setTimeout(() => pill.classList.remove('copied'), 1200);
      }
      playSound('pop');
    };

    $('#resultActions').innerHTML = `
      <a class="btn btn-primary" href="https://github.com/${escapeHTML(slug)}/commit/${commitObj.sha}" target="_blank" rel="noopener">
        <svg class="icon icon-sm" viewBox="0 0 24 24"><path d="M18 13v6a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h6"/><polyline points="15 3 21 3 21 9"/><line x1="10" y1="14" x2="21" y2="3"/></svg>
        <span>View Commit on GitHub</span>
      </a>
      <a class="btn btn-secondary" href="https://github.com/${escapeHTML(slug)}/tree/${encodeURIComponent(branch)}" target="_blank" rel="noopener">
        <svg class="icon icon-sm" viewBox="0 0 24 24"><path d="M22 19a2 2 0 0 1-2 2H4a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h5l2 3h9a2 2 0 0 1 2 2z"/></svg>
        <span>Browse Repository Tree</span>
      </a>
      <button class="btn btn-subtle" id="uploadAnotherBtn" type="button">
        <svg class="icon icon-sm" viewBox="0 0 24 24"><path d="M3 12a9 9 0 0 1 9-9 9.75 9.75 0 0 1 6.74 2.74L21 8"/><path d="M21 3v5h-5"/><path d="M21 12a9 9 0 0 1-9 9 9.75 9.75 0 0 1-6.74-2.74L3 16"/><path d="M8 16H3v5"/></svg>
        <span>Upload Another Batch</span>
      </button>
    `;

    const upActions = $('#pipelineUploadingActions');
    if (upActions) upActions.hidden = true;
    const errBox = $('#pipelineErrorBox');
    if (errBox) errBox.hidden = true;

    $('#uploadAnotherBtn').onclick = () => {
      files.clear();
      resultCard.hidden = true;
      const overlay = $('#pipelineOverlay');
      if (overlay) overlay.hidden = true;
      $('#pipelineCard').hidden = true;
      $('#pipelineCard').classList.remove('pipeline-completed', 'pipeline-error');
      if (pf) pf.hidden = false;
      msg('');
      refresh();
      showToast('Manifest reset for next upload', 'info');
      playSound('pop');
    };

    // Update bottom dock
    $('#barMain').textContent = `COMMITTED: ${commitObj.sha.slice(0, 7).toUpperCase()} // HEAD UPDATED`;
    $('#barSub').textContent = `PAYLOAD DEPLOYED: ${uploadTargets.length} FILES TO ${slug}@${branch}`;

    fireConfetti();
    playSound('success');
  } catch (err) {
    const upActions = $('#pipelineUploadingActions');
    if (upActions) upActions.hidden = true;

    if (err.identical) {
      msg('Nothing to commit: All staged files are already identical on remote branch.', 'info');
      showToast('No new changes to commit', 'info');
      const overlay = $('#pipelineOverlay');
      if (overlay) overlay.hidden = true;
    } else {
      msg('Error uploading to GitHub: ' + err.message, 'err');
      showToast(err.message, 'err');
      playSound('warn');
      const card = $('#pipelineCard');
      if (card) {
        card.classList.add('pipeline-error');
        const spinner = $('#pipelineSpinner');
        if (spinner) {
          spinner.className = 'pipeline-error-badge';
          spinner.innerHTML = '<svg class="icon icon-sm" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5"><line x1="18" y1="6" x2="6" y2="18"/><line x1="6" y1="6" x2="18" y2="18"/></svg>';
        }
        $('#pipelineStatusText').textContent = err.cancelled ? 'Upload Cancelled' : 'Upload Failed';
        const pf = $('#pipelineFile');
        if (pf) pf.hidden = true;
      }

      // Display Retry Option inside the centered modal
      const errBox = $('#pipelineErrorBox');
      if (errBox) {
        errBox.hidden = false;
        const errText = $('#pipelineErrorText');
        if (errText) {
          errText.textContent = err.cancelled ? 'Upload was cancelled by user.' : (err.message || 'An error occurred during upload.');
        }
      }

      const retryBtn = $('#pipelineRetryBtn');
      if (retryBtn) {
        retryBtn.onclick = () => {
          if (errBox) errBox.hidden = true;
          $('#pipelineCard')?.classList.remove('pipeline-error');
          executeUpload(overrideSecrets);
        };
      }

      const dismissBtn = $('#pipelineDismissErrorBtn');
      if (dismissBtn) {
        dismissBtn.onclick = () => {
          const overlay = $('#pipelineOverlay');
          if (overlay) overlay.hidden = true;
        };
      }
    }
  } finally {
    setBusy(false);
  }
}

/* ---------- App Initialization ---------- */
window.addEventListener('DOMContentLoaded', () => {
  initTheme();
  initSound();

  // Restore saved token & settings
  const savedToken = store.get('f2g.token');
  if (savedToken) {
    $('#token').value = savedToken;
    $('#remember').checked = true;
    verifyToken();
  }

  const savedRepo = store.get('f2g.repo');
  if (savedRepo) $('#repo').value = savedRepo;

  const savedBranch = store.get('f2g.branch');
  if (savedBranch) $('#branch').value = savedBranch;

  const savedPrefix = store.get('f2g.prefix');
  if (savedPrefix) $('#prefix').value = savedPrefix;

  refresh();
});
