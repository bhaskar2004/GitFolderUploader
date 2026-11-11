/**
 * Folder to GitHub — Modern Client-Side Git Engine
 * Features:
 * 1. Pre-Commit In-Browser Secret Scanner
 * 2. Remote Branch Diff & Change Detection (with Git SHA-1 hashing)
 * 3. Real .gitignore Parser & Stack Presets
 * 4. Clean Filtered Project ZIP Exporter
 * 5. Web Audio Micro-Sound Effects with Persistent Mute
 * 6. Live Multi-Stage Git Object Upload Pipeline
 * 7. Tree & Flat Views with Inline File Previews
 */

const $ = s => document.querySelector(s);
const $$ = s => document.querySelectorAll(s);
const API = 'https://api.github.com';

// Limits & constants
const MAX_FILE_SIZE = 50 * 1024 * 1024;     // 50MB warning threshold
const HARD_LIMIT = 100 * 1024 * 1024;       // 100MB GitHub hard reject
const SHOW_LIMIT = 250;                     // max rows rendered in review flat list
const INLINE_MAX = 1024 * 1024;             // 1MB: text files up to this size can go directly into git tree
const BIG_FILE_THRESHOLD = 8 * 1024 * 1024; // 8MB: upload sequentially to avoid browser OOM
const TREE_MAX_CHARS = 2e6;
const TREE_MAX_ENTRIES = 400;

// Default clutter & secret filter
const DEFAULT_SKIP_REGEX = /(^|\/)(node_modules|__MACOSX|\.next|\.nuxt|dist|build|out|\.venv|venv|\.cache)(\/|$)|(^|\/)(\.DS_Store|Thumbs\.db|desktop\.ini|\.env(\.(?!example$|sample$)[^/]*)?|id_rsa|id_ed25519|.*\.pem|.*\.key|.*\.pfx|.*\.pkcs12)$/i;
const GITDIR_REGEX = /(^|\/)\.git(\/|$)/i;

// Secret detection patterns
const SECRET_PATTERNS = [
  { name: 'AWS Access Key', regex: /(?:^|[^A-Z0-9])(AKIA[0-9A-Z]{16})(?:[^A-Z0-9]|$)/ },
  { name: 'GitHub Personal Access Token', regex: /(?:^|[^A-Za-z0-9_])(gh[pousr]_[A-Za-z0-9_]{36,}|github_pat_[A-Za-z0-9_]{82})(?:[^A-Za-z0-9_]|$)/ },
  { name: 'Private Key Block', regex: /-----BEGIN (?:RSA |EC |DSA |OPENSSH )?PRIVATE KEY-----/ },
  { name: 'OpenAI / Anthropic API Key', regex: /(?:^|[^A-Za-z0-9_-])(sk-[A-Za-z0-9]{20,T3BlbkFJ[A-Za-z0-9]{20,}|sk-proj-[A-Za-z0-9_-]{40,}|sk-ant-[A-Za-z0-9_-]{40,})(?:[^A-Za-z0-9_-]|$)/ },
  { name: 'Slack Token or Webhook', regex: /(xox[baprs]-[0-9]{10,13}-[0-9]{10,13}[a-zA-Z0-9-]*|https:\/\/hooks\.slack\.com\/services\/T[0-9A-Z]{8}\/B[0-9A-Z]{8}\/[0-9A-Za-z]{24})/ },
  { name: 'Stripe Secret Key', regex: /(sk_live_[0-9a-zA-Z]{24,})/ },
  { name: 'Google API Key', regex: /(AIza[0-9A-Za-z\\-_]{35})/ }
];

// Application state
const files = new Map();           // clean path -> File
let token = '', me = '', currentRepoData = null, busy = false, cancelled = false;
let abortCtrl = null, rowMap = new Map(), defaults = {}, currentView = 'flat';
let uploadStartTime = 0;
let soundEnabled = true;

// Remote diff & secret tracking
let remoteTreeMap = new Map();     // path -> remote sha
let fileGitShaMap = new Map();     // local path -> sha1
let fileSecretsMap = new Map();    // path -> array of secret names
let gitignoreRules = [];           // array of parsed rules
let activeDiffFilter = 'all';      // all, new, mod, same, secret

// Audio synthesis context
let audioCtx = null;

/* ---------- Utilities ---------- */
const sleep = ms => new Promise(r => setTimeout(r, ms));
const fmt = n => {
  if (n < 1024) return n + ' B';
  if (n < 1048576) return (n / 1024).toFixed(1) + ' KB';
  if (n < 1073741824) return (n / 1048576).toFixed(1) + ' MB';
  return (n / 1073741824).toFixed(2) + ' GB';
};
const plural = (n, w) => `${n.toLocaleString()} ${w}${n === 1 ? '' : 's'}`;
const coarsePointer = matchMedia('(pointer:coarse)').matches;
const enc = b => b.split('/').map(encodeURIComponent).join('/');

const store = {
  get: k => { try { return localStorage.getItem(k) || ''; } catch { return ''; } },
  set: (k, v) => { try { localStorage.setItem(k, v); } catch {} },
  del: k => { try { localStorage.removeItem(k); } catch {} }
};

function escapeHTML(str) {
  return String(str).replace(/[&<>'"]/g, tag => ({
    '&': '&amp;',
    '<': '&lt;',
    '>': '&gt;',
    "'": '&#39;',
    '"': '&quot;'
  }[tag] || tag));
}

function asText(buf) {
  const u = new Uint8Array(buf);
  if (u.includes(0)) return null;
  try {
    return new TextDecoder('utf-8', { fatal: true, ignoreBOM: true }).decode(u);
  } catch {
    return null;
  }
}

/* ---------- Web Audio Synthesized Sound Effects ---------- */
function initAudio() {
  if (!audioCtx) {
    const AudioContextClass = window.AudioContext || window.webkitAudioContext;
    if (AudioContextClass) audioCtx = new AudioContextClass();
  }
  if (audioCtx && audioCtx.state === 'suspended') {
    audioCtx.resume();
  }
}

function playSound(type) {
  if (!soundEnabled) return;
  try {
    initAudio();
    if (!audioCtx) return;
    const now = audioCtx.currentTime;

    if (type === 'pop') {
      const osc = audioCtx.createOscillator();
      const gain = audioCtx.createGain();
      osc.type = 'sine';
      osc.frequency.setValueAtTime(320, now);
      osc.frequency.exponentialRampToValueAtTime(780, now + 0.08);
      gain.gain.setValueAtTime(0.2, now);
      gain.gain.exponentialRampToValueAtTime(0.01, now + 0.08);
      osc.connect(gain);
      gain.connect(audioCtx.destination);
      osc.start(now);
      osc.stop(now + 0.09);
    } else if (type === 'success') {
      [523.25, 659.25, 783.99, 1046.50].forEach((freq, i) => { // C-E-G-C major chord
        const osc = audioCtx.createOscillator();
        const gain = audioCtx.createGain();
        osc.type = 'triangle';
        osc.frequency.setValueAtTime(freq, now + i * 0.07);
        gain.gain.setValueAtTime(0.18, now + i * 0.07);
        gain.gain.exponentialRampToValueAtTime(0.001, now + i * 0.07 + 0.45);
        osc.connect(gain);
        gain.connect(audioCtx.destination);
        osc.start(now + i * 0.07);
        osc.stop(now + i * 0.07 + 0.46);
      });
    } else if (type === 'warn') {
      const osc = audioCtx.createOscillator();
      const gain = audioCtx.createGain();
      osc.type = 'sawtooth';
      osc.frequency.setValueAtTime(220, now);
      osc.frequency.exponentialRampToValueAtTime(140, now + 0.18);
      gain.gain.setValueAtTime(0.15, now);
      gain.gain.exponentialRampToValueAtTime(0.01, now + 0.18);
      osc.connect(gain);
      gain.connect(audioCtx.destination);
      osc.start(now);
      osc.stop(now + 0.19);
    }
  } catch(e) {}
}

/* ---------- Git Blob SHA-1 Calculation ---------- */
async function computeGitBlobSha(file) {
  try {
    const buf = await file.arrayBuffer();
    const header = `blob ${buf.byteLength}\0`;
    const headerBuf = new TextEncoder().encode(header);
    const combined = new Uint8Array(headerBuf.byteLength + buf.byteLength);
    combined.set(headerBuf, 0);
    combined.set(new Uint8Array(buf), headerBuf.byteLength);
    const hashBuffer = await crypto.subtle.digest('SHA-1', combined);
    const hashArray = Array.from(new Uint8Array(hashBuffer));
    return hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
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
    const isNegated = line.startsWith('!');
    const pattern = isNegated ? line.slice(1).trim() : line;
    if (!pattern) continue;

    // Convert gitignore glob pattern to regex
    let regexStr = pattern
      .replace(/\./g, '\\.')
      .replace(/\*\*/g, '§§')
      .replace(/\*/g, '[^/]*')
      .replace(/§§/g, '.*')
      .replace(/\?/g, '[^/]');

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

/* ---------- Secret Scanner Engine ---------- */
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
  fileSecretsMap.clear();
  let totalSecrets = 0;
  for (const item of stagedItems) {
    if (item.file.size <= INLINE_MAX) {
      try {
        const text = asText(await item.file.arrayBuffer());
        if (text !== null) {
          const hits = scanTextForSecrets(text);
          if (hits.length) {
            fileSecretsMap.set(item.path, hits);
            totalSecrets += hits.length;
          }
        }
      } catch(e) {}
    }
  }
  return totalSecrets;
}

/* ---------- Theme & Sound Controls ---------- */
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
    themeIcon.innerHTML = '<rect width="20" height="14" x="2" y="3" rx="2"/><line x1="8" y1="21" x2="16" y2="21"/><line x1="12" y1="17" x2="12" y2="21"/>';
    themeLabel.textContent = 'System';
  }
}

function initTheme() {
  const current = store.get('f2g.theme') || 'system';
  updateThemeUI(current);
  themeToggle.addEventListener('click', () => {
    const cur = store.get('f2g.theme') || 'system';
    let next = cur === 'system' ? 'dark' : cur === 'dark' ? 'light' : 'system';
    if (next === 'system') {
      store.del('f2g.theme');
      document.documentElement.removeAttribute('data-theme');
      $('meta[name="color-scheme"]').content = 'light dark';
    } else {
      store.set('f2g.theme', next);
      document.documentElement.setAttribute('data-theme', next);
      $('meta[name="color-scheme"]').content = next;
    }
    updateThemeUI(next);
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

/* ---------- Toast & Confetti ---------- */
function showToast(text, type = 'info', iconSvg = '') {
  const shelf = $('#toastShelf');
  if (!shelf) return;
  const item = document.createElement('div');
  item.className = 'toast-item' + (type === 'ok' ? ' toast-ok' : type === 'err' ? ' toast-err' : '');
  const icon = iconSvg || (type === 'ok' 
    ? '<svg class="icon icon-sm" viewBox="0 0 24 24"><path d="M20 6 9 17l-5-5"/></svg>' 
    : type === 'err' 
    ? '<svg class="icon icon-sm" viewBox="0 0 24 24"><circle cx="12" cy="12" r="10"/><line x1="15" y1="9" x2="9" y2="15"/><line x1="9" y1="9" x2="15" y2="15"/></svg>'
    : '<svg class="icon icon-sm" viewBox="0 0 24 24"><circle cx="12" cy="12" r="10"/><line x1="12" y1="16" x2="12" y2="12"/><line x1="12" y1="8" x2="12.01" y2="8"/></svg>');
  item.innerHTML = `${icon}<span>${escapeHTML(text)}</span>`;
  shelf.append(item);
  setTimeout(() => {
    item.classList.add('toast-out');
    setTimeout(() => item.remove(), 220);
  }, 3200);
}

function triggerConfetti() {
  const canvas = $('#confettiCanvas');
  if (!canvas) return;
  canvas.width = window.innerWidth;
  canvas.height = window.innerHeight;
  canvas.style.display = 'block';
  const ctx = canvas.getContext('2d');
  const colors = ['#2563eb', '#3b82f6', '#10b981', '#059669', '#f59e0b', '#ec4899', '#8b5cf6', '#06b6d4'];
  const particles = Array.from({ length: 95 }, () => ({
    x: canvas.width * 0.5 + (Math.random() - 0.5) * 350,
    y: canvas.height * 0.65,
    vx: (Math.random() - 0.5) * 16,
    vy: -Math.random() * 17 - 9,
    size: Math.random() * 8 + 5,
    color: colors[Math.floor(Math.random() * colors.length)],
    rotation: Math.random() * 360,
    vRot: (Math.random() - 0.5) * 12,
    opacity: 1
  }));

  const start = performance.now();
  function loop(now) {
    const elapsed = now - start;
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    let alive = false;
    particles.forEach(p => {
      p.x += p.vx;
      p.y += p.vy;
      p.vy += 0.48;
      p.vx *= 0.98;
      p.rotation += p.vRot;
      if (elapsed > 1700) p.opacity -= 0.025;
      if (p.opacity > 0 && p.y < canvas.height + 20) {
        alive = true;
        ctx.save();
        ctx.translate(p.x, p.y);
        ctx.rotate((p.rotation * Math.PI) / 180);
        ctx.fillStyle = p.color;
        ctx.globalAlpha = Math.max(0, p.opacity);
        ctx.fillRect(-p.size / 2, -p.size / 2, p.size, p.size * 0.65);
        ctx.restore();
      }
    });

    if (alive && elapsed < 3500) {
      requestAnimationFrame(loop);
    } else {
      ctx.clearRect(0, 0, canvas.width, canvas.height);
      canvas.style.display = 'none';
    }
  }
  requestAnimationFrame(loop);
}

function animateNumber(el, target, formatFn = n => n.toLocaleString()) {
  if (!el) return;
  const currentVal = Number(el.dataset.rawVal || 0);
  if (currentVal === target) {
    el.textContent = formatFn(target);
    return;
  }
  const duration = 380;
  const startTime = performance.now();
  function update(now) {
    const elapsed = now - startTime;
    const progress = Math.min(elapsed / duration, 1);
    const ease = 1 - Math.pow(1 - progress, 3);
    const cur = Math.round(currentVal + (target - currentVal) * ease);
    el.textContent = formatFn(cur);
    if (progress < 1) requestAnimationFrame(update);
    else {
      el.dataset.rawVal = target;
      el.textContent = formatFn(target);
    }
  }
  requestAnimationFrame(update);
}

function getFileBadge(filename) {
  const ext = filename.split('.').pop()?.toLowerCase() || '';
  let cls = 'ext-other', lbl = ext ? ext.slice(0, 4) : 'FILE';
  if (['js', 'mjs', 'cjs'].includes(ext)) { cls = 'ext-js'; lbl = 'JS'; }
  else if (['ts', 'mts'].includes(ext)) { cls = 'ext-ts'; lbl = 'TS'; }
  else if (['jsx', 'tsx'].includes(ext)) { cls = 'ext-ts'; lbl = ext.toUpperCase(); }
  else if (['json', 'yaml', 'yml'].includes(ext)) { cls = 'ext-json'; lbl = ext.toUpperCase(); }
  else if (['html', 'htm'].includes(ext)) { cls = 'ext-html'; lbl = 'HTML'; }
  else if (['css', 'scss', 'sass', 'less'].includes(ext)) { cls = 'ext-css'; lbl = 'CSS'; }
  else if (['md', 'txt', 'markdown'].includes(ext)) { cls = 'ext-md'; lbl = 'MD'; }
  else if (['png', 'jpg', 'jpeg', 'webp', 'svg', 'gif', 'ico'].includes(ext)) { cls = 'ext-img'; lbl = 'IMG'; }
  else if (['py'].includes(ext)) { cls = 'ext-py'; lbl = 'PY'; }
  else if (['sh', 'bash'].includes(ext)) { cls = 'ext-sh'; lbl = 'SH'; }
  return `<span class="ext-badge ${cls}">${lbl}</span>`;
}

function setPipelineStage(stageNum, title, currentFileName, speedText = '') {
  const card = $('#pipelineCard');
  if (!card) return;
  card.hidden = false;
  if (title) $('#pipelineStatusText').textContent = title;
  if (currentFileName) $('#pipelineFile').textContent = currentFileName;
  if (speedText) $('#pipelineSpeed').textContent = speedText;

  for (let i = 1; i <= 5; i++) {
    const stepEl = $('#stage' + i);
    if (!stepEl) continue;
    const dot = stepEl.querySelector('.stage-dot');
    if (i < stageNum) {
      stepEl.className = 'pipeline-step done';
      dot.innerHTML = '<svg class="icon icon-sm" viewBox="0 0 24 24"><path d="M20 6 9 17l-5-5"/></svg>';
    } else if (i === stageNum) {
      stepEl.className = 'pipeline-step active';
      dot.textContent = i;
    } else {
      stepEl.className = 'pipeline-step';
      dot.textContent = i;
    }
  }
}

/* ---------- Authentication Step ---------- */
$('#reveal').onclick = () => {
  const t = $('#token'), isPw = t.type === 'password';
  t.type = isPw ? 'text' : 'password';
  $('#reveal').setAttribute('aria-pressed', isPw);
  $('#reveal span').textContent = isPw ? 'Hide' : 'Show';
};

$('#disconnectBtn').onclick = () => {
  token = ''; me = '';
  $('#token').value = '';
  store.del('f2g.token');
  $('#authCard').hidden = true;
  $('#repos').textContent = '';
  $('#branches').textContent = '';
  msg('Disconnected.', 'ok');
  showToast('Disconnected from GitHub', 'info');
  refresh();
};

let verifyTimer = null, verifySeq = 0;
async function verifyToken() {
  const seq = ++verifySeq;
  token = $('#token').value.trim();
  me = ''; defaults = {};
  $('#repos').textContent = '';

  if (!token) {
    $('#authCard').hidden = true;
    return refresh();
  }

  $('#authCard').hidden = false;
  $('#authName').textContent = 'Authenticating with GitHub…';
  $('#authAvatar').src = 'data:image/svg+xml,<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="%2398a2b3"><circle cx="12" cy="12" r="10"/></svg>';
  $('#authScopes').textContent = 'Checking scopes…';
  $('#rateLimitPill').textContent = 'Rate limit: checking…';

  try {
    const res = await gh('/user');
    if (seq !== verifySeq) return;
    me = res.login;
    $('#authAvatar').src = res.avatar_url;
    $('#authName').textContent = res.name ? `${res.name} (@${res.login})` : `@${res.login}`;
    $('#authScopes').textContent = token.startsWith('github_pat_') ? 'Fine-grained Token' : 'Classic Token';
    
    // Check rate limit
    try {
      const rl = await gh('/rate_limit');
      if (rl && rl.rate) {
        const rem = rl.rate.remaining, tot = rl.rate.limit;
        const resetMin = Math.max(0, Math.ceil((rl.rate.reset - Date.now() / 1000) / 60));
        $('#rateLimitPill').textContent = `Rate: ${rem}/${tot} (${resetMin}m reset)`;
      }
    } catch {}

    updateStepper();
    showToast(`Connected as @${me}`, 'ok');
  } catch (err) {
    if (seq !== verifySeq) return;
    $('#authCard').hidden = true;
    msg(err.status === 401 ? 'Personal access token not accepted. Please check it.' : 'Could not reach GitHub: ' + err.message, 'err');
    return;
  }

  // Fetch list of repositories
  try {
    const list = await gh('/user/repos?per_page=100&sort=pushed&affiliation=owner,collaborator,organization_member');
    if (seq !== verifySeq) return;
    const dl = $('#repos');
    dl.textContent = '';
    list.filter(r => !r.permissions || r.permissions.push).forEach(r => {
      defaults[r.full_name.toLowerCase()] = r.default_branch;
      dl.append(Object.assign(document.createElement('option'), { value: r.full_name }));
    });
    repoChanged();
  } catch {}
}

$('#token').addEventListener('input', () => {
  clearTimeout(verifyTimer);
  verifyTimer = setTimeout(verifyToken, 650);
  if ($('#remember').checked) {
    const t = $('#token').value.trim();
    t ? store.set('f2g.token', t) : store.del('f2g.token');
  }
});
$('#token').addEventListener('change', () => { clearTimeout(verifyTimer); verifyToken(); });
$('#remember').addEventListener('change', () => {
  const t = $('#token').value.trim();
  $('#remember').checked && t ? store.set('f2g.token', t) : store.del('f2g.token');
});

/* ---------- Destination Step ---------- */
function slugOf() {
  let s = $('#repo').value.trim();
  const m = s.match(/github\.com[\/:]([^\/\s]+)\/([^\/\s#?]+)/i);
  if (m) s = m[1] + '/' + m[2];
  return s.replace(/\.git$/i, '').replace(/\/+$/, '');
}

const badBranch = b => !!b && (/[\s~^:?*\[\\]/.test(b) || /\.\.|\/\/|@\{/.test(b) || /^[\/.-]|[\/.]$|\.lock$/.test(b) || b === '@');

let branchTimer = null;
function repoChanged() {
  const slug = slugOf();
  $('#branch').placeholder = defaults[slug.toLowerCase()] || 'Default branch';
  clearTimeout(branchTimer);
  if (!token || $('#create').checked || !/^[\w.-]+\/[\w.-]+$/.test(slug)) return refresh();

  branchTimer = setTimeout(async () => {
    try {
      const bs = await gh('/repos/' + slug + '/branches?per_page=100');
      const dl = $('#branches');
      dl.textContent = '';
      bs.forEach(b => dl.append(Object.assign(document.createElement('option'), { value: b.name })));
      // Check remote tree for diffing
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

// Prefix chips
$$('.chips-row .chip').forEach(c => {
  c.addEventListener('click', () => {
    $('#prefix').value = c.dataset.prefix;
    refresh();
  });
});

$('#create').addEventListener('change', () => {
  const c = $('#create').checked;
  $('#privWrap').hidden = !c;
  $('#repoLabel').textContent = c ? 'New repository name' : 'Repository';
  $('#repo').placeholder = c ? 'my-awesome-repo' : 'owner/repo';
  $('#repoHelp').textContent = c ? 'Repository will be created under your GitHub account with an initial commit.' : 'Type owner/repo or paste a full GitHub repo link.';
  refresh();
});

// Filter Accordion
$('#filterToggle').onclick = () => {
  const c = $('#filterContent');
  const exp = c.hidden;
  c.hidden = !exp;
  $('#filterToggle').setAttribute('aria-expanded', exp);
  $('#filterArrow').style.transform = exp ? 'rotate(180deg)' : '';
};

// Stack Preset Chips in Filter Box
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
      const current = input.value.trim();
      input.value = current ? current + ', ' + val : val;
      refresh();
      showToast(`Applied ${chip.textContent.trim()} ignore preset`, 'ok');
      playSound('pop');
    }
  });
});

/* ---------- File Ingestion & Path Cleaning ---------- */
function srcMsg(t) { $('#srcMsg').textContent = t || ''; }

function cleanPath(p) {
  const parts = String(p).replace(/\\/g, '/').split('/').filter(s => s && s !== '.');
  return !parts.length || parts.includes('..') ? '' : parts.join('/');
}

let badPathCount = 0;
function addFile(path, file) {
  const c = cleanPath(path);
  if (c) files.set(c, file);
  else badPathCount++;
}

async function reportFiles(n, what) {
  srcMsg((n ? `Added ${plural(n, 'file')}` : 'No files discovered') + 
    (what ? ` from ${what}` : '') + '.' + 
    (badPathCount ? ` ${plural(badPathCount, 'file')} skipped due to unsafe paths.` : ''));
  badPathCount = 0;

  // Check if .gitignore exists in loaded files
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

  if (n) {
    showToast(`Added ${plural(n, 'file')}${what ? ' from ' + what : ''}`, 'ok');
    playSound('pop');
  }
}

const bindInput = (btn, input, fn) => {
  $(btn).onclick = () => { if (!busy) $(input).click(); };
  $(input).onchange = async e => {
    const f = [...e.target.files];
    e.target.value = '';
    if (!busy && f.length) await fn(f);
  };
};

bindInput('#bFolder', '#pFolder', async f => {
  f.forEach(x => addFile(x.webkitRelativePath || x.name, x));
  await reportFiles(f.length);
  refresh();
});

bindInput('#bFiles', '#pFiles', async f => {
  f.forEach(x => addFile(x.name, x));
  await reportFiles(f.length);
  refresh();
});

bindInput('#bZip', '#pZip', async f => {
  for (const z of f) await addZip(z);
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
      s.remove();
      reject(new Error('Failed to load ZIP processor library.'));
    };
    document.head.append(s);
  }));
}

async function addZip(file) {
  try {
    srcMsg(`Uncompressing ${file.name}…`);
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
    for (const en of entries) {
      if (en.isFile && /\.zip$/i.test(en.name)) {
        hasZip = true;
        await addZip(await new Promise((res, rej) => en.file(res, rej)));
      } else {
        await scanEntry(en);
      }
    }
    if (!hasZip) await reportFiles(files.size - beforeCount);
  } catch (err) {
    srcMsg('Error reading dropped files: ' + err.message);
  }
  refresh();
});

async function scanEntry(en) {
  if (en.isFile) {
    addFile(en.fullPath, await new Promise((res, rej) => en.file(res, rej)));
  } else if (en.isDirectory) {
    const reader = en.createReader();
    let batch;
    do {
      batch = await new Promise((res, rej) => reader.readEntries(res, rej));
      for (const child of batch) await scanEntry(child);
    } while (batch.length);
  }
}

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

  // Path normalization and stripping
  const roots = new Set(out.map(o => o.path.split('/')[0]));
  const strip = !$('#keepRoot').checked && roots.size === 1 && out.every(o => o.path.includes('/'));
  const pre = cleanPath($('#prefix').value);

  out.forEach(o => {
    const p = strip ? o.path.split('/').slice(1).join('/') : o.path;
    o.repoPath = pre ? pre + '/' + p : p;
    o.diffStatus = getFileDiffStatus(o.repoPath);
    o.hasSecret = fileSecretsMap.has(o.path);
  });

  return { out, junkCount, bigFiles, hardRejects };
}

/* ---------- Remote Diff Engine ---------- */
async function checkRemoteDiff() {
  const slug = slugOf();
  const wantBranch = $('#branch').value.trim();
  if (!token || !slug || !/^[\w.-]+\/[\w.-]+$/.test(slug)) return;

  try {
    const repo = await gh('/repos/' + slug);
    const branch = wantBranch || repo.default_branch;
    const refData = await gh('/repos/' + slug + '/git/ref/heads/' + enc(branch));
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

    // Compute hashes for staged files asynchronously
    const { out } = computeCurrentManifest();
    for (const item of out) {
      if (!fileGitShaMap.has(item.path)) {
        computeGitBlobSha(item.file).then(sha => {
          if (sha) {
            fileGitShaMap.set(item.path, sha);
            updateDiffUI();
          }
        });
      }
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
  $('#diffNew').textContent = `+${countNew} new`;
  $('#diffMod').textContent = `~${countMod} modified`;
  $('#diffSame').textContent = `${countSame} identical`;
}

// Diff filter buttons
$$('.diff-pill').forEach(btn => {
  btn.addEventListener('click', () => {
    $$('.diff-pill').forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    activeDiffFilter = btn.dataset.diff;
    refresh();
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
function updateStepper() {
  const hasToken = !!$('#token').value.trim();
  const slug = slugOf();
  const hasDestination = $('#create').checked ? !!slug : /^[\w.-]+\/[\w.-]+$/.test(slug);
  const { out } = computeCurrentManifest();
  const hasFiles = out.length > 0;

  $('#tab1').classList.toggle('completed', hasToken && !!me);
  $('#tab2').classList.toggle('completed', hasDestination);
  $('#tab3').classList.toggle('completed', hasFiles);
  $('#tab4').classList.toggle('completed', hasToken && hasDestination && hasFiles);
}

// Stepper click navigation
$('#tab1').onclick = () => $('#step1-title').scrollIntoView({ behavior: 'smooth', block: 'start' });
$('#tab2').onclick = () => $('#step2-title').scrollIntoView({ behavior: 'smooth', block: 'start' });
$('#tab3').onclick = () => $('#step3-title').scrollIntoView({ behavior: 'smooth', block: 'start' });
$('#tab4').onclick = () => $('#step4-title').scrollIntoView({ behavior: 'smooth', block: 'start' });

/* ---------- Review View: Flat & Tree ---------- */
function buildTreeStructure(items) {
  const root = { name: '', fullPath: '', isDir: true, children: new Map(), files: [] };
  items.forEach(item => {
    const parts = item.repoPath.split('/');
    let cur = root;
    let accumulatedPath = '';
    for (let i = 0; i < parts.length - 1; i++) {
      const part = parts[i];
      accumulatedPath = accumulatedPath ? accumulatedPath + '/' + part : part;
      if (!cur.children.has(part)) {
        cur.children.set(part, { name: part, fullPath: accumulatedPath, isDir: true, children: new Map(), files: [] });
      }
      cur = cur.children.get(part);
    }
    cur.files.push(item);
  });
  return root;
}

function deleteFolder(folderRepoPath) {
  const { out } = computeCurrentManifest();
  const toDelete = out.filter(o => o.repoPath === folderRepoPath || o.repoPath.startsWith(folderRepoPath + '/'));
  toDelete.forEach(o => files.delete(o.path));
  refresh();
}

function countNodeFiles(node) {
  let count = node.files.length;
  for (const child of node.children.values()) {
    count += countNodeFiles(child);
  }
  return count;
}

function renderTree(node, container, depth = 0) {
  // Folders first
  const folderNames = [...node.children.keys()].sort();
  for (const fName of folderNames) {
    const childNode = node.children.get(fName);
    const count = countNodeFiles(childNode);
    const folderWrap = document.createElement('div');
    folderWrap.className = 'tree-node';

    const folderBar = document.createElement('div');
    folderBar.className = 'tree-folder open';
    folderBar.innerHTML = `
      <svg class="icon icon-sm tree-folder-arrow" viewBox="0 0 24 24"><polyline points="9 18 15 12 9 6"/></svg>
      <svg class="icon icon-sm" style="color:var(--accent);" viewBox="0 0 24 24"><path d="M4 20h16a2 2 0 0 0 2-2V8a2 2 0 0 0-2-2h-7.93a2 2 0 0 1-1.66-.9l-.82-1.2A2 2 0 0 0 7.93 3H4a2 2 0 0 0-2 2v13c0 1.1.9 2 2 2Z"/></svg>
      <span style="flex:1;">${escapeHTML(fName)} <span style="font-size:0.75rem; color:var(--muted); font-weight:400;">(${count})</span></span>
      <button class="action-icon-btn remove-folder-btn" type="button" aria-label="Remove entire folder" title="Remove entire folder">×</button>
    `;

    const childrenWrap = document.createElement('div');
    childrenWrap.className = 'tree-children';

    folderBar.onclick = (e) => {
      if (e.target.closest('.remove-folder-btn')) return;
      folderBar.classList.toggle('open');
      childrenWrap.classList.toggle('collapsed');
    };

    folderBar.querySelector('.remove-folder-btn').onclick = (e) => {
      e.stopPropagation();
      deleteFolder(childNode.fullPath);
      showToast(`Removed folder: ${fName}`, 'info');
    };

    folderWrap.append(folderBar, childrenWrap);
    container.append(folderWrap);

    renderTree(childNode, childrenWrap, depth + 1);
  }

  // Files in this node
  node.files.sort((a,b) => a.repoPath.localeCompare(b.repoPath)).forEach(item => {
    const fileRow = document.createElement('div');
    fileRow.className = 'tree-file';
    fileRow.dataset.path = item.path;
    const name = item.repoPath.split('/').pop();
    const badge = getFileBadge(name);
    fileRow.innerHTML = `
      <div style="display:flex; align-items:center; gap:0.45rem; min-width:0; overflow:hidden;">
        ${badge}
        <span class="file-path" style="white-space:nowrap; text-overflow:ellipsis; overflow:hidden;" title="${escapeHTML(item.repoPath)}">${escapeHTML(name)}</span>
      </div>
      <div style="display:flex; align-items:center; gap:0.6rem;">
        <span class="file-size">${fmt(item.file.size)}</span>
        <button class="action-icon-btn remove-btn" type="button" aria-label="Remove file" title="Remove">×</button>
      </div>
    `;
    fileRow.querySelector('.file-path').onclick = () => openFilePreview(item);
    fileRow.querySelector('.remove-btn').onclick = (e) => {
      e.stopPropagation();
      files.delete(item.path);
      refresh();
      showToast(`Removed ${name}`, 'info');
    };
    container.append(fileRow);
  });
}

function refresh() {
  if (busy) return;
  const { out, junkCount, bigFiles, hardRejects } = computeCurrentManifest();
  const totalBytes = out.reduce((s, o) => s + o.file.size, 0);

  $('#emptyReview').hidden = files.size > 0;
  $('#filledReview').hidden = files.size === 0;
  
  // Smooth number transitions
  animateNumber($('#cnt'), out.length);
  animateNumber($('#size'), totalBytes, fmt);
  
  const estBlobs = out.filter(o => o.file.size > INLINE_MAX).length;
  const estTrees = Math.ceil(out.length / TREE_MAX_ENTRIES);
  animateNumber($('#apiEst'), estBlobs + estTrees + 2);

  // Run async secret scanning
  scanAllStagedSecrets(out).then(secretCount => {
    const secBanner = $('#securityBanner');
    if (secretCount > 0) {
      secBanner.hidden = false;
      $('#secretCount').textContent = secretCount;
      playSound('warn');
    } else {
      secBanner.hidden = true;
    }
  });

  // Render Flat List
  const q = $('#filter').value.trim().toLowerCase();
  const manifest = $('#manifest');
  manifest.textContent = '';
  rowMap = new Map();

  let filtered = out.filter(o => !q || o.repoPath.toLowerCase().includes(q));

  // Diff Filter
  if (activeDiffFilter !== 'all') {
    filtered = filtered.filter(o => {
      if (activeDiffFilter === 'secret') return fileSecretsMap.has(o.path);
      return getFileDiffStatus(o.repoPath) === activeDiffFilter;
    });
  }

  filtered.slice(0, SHOW_LIMIT).forEach(o => {
    const li = document.createElement('li');
    li.className = 'manifest-row' + (fileSecretsMap.has(o.path) ? ' has-secret' : '');
    li.dataset.path = o.path;

    const isWarn = o.file.size > MAX_FILE_SIZE;
    const badge = getFileBadge(o.repoPath);
    const diffStatus = getFileDiffStatus(o.repoPath);
    const hasSecret = fileSecretsMap.has(o.path);

    let statusBadge = '';
    if (hasSecret) {
      statusBadge = '<span class="secret-badge">Secret</span>';
    } else if (diffStatus === 'new') {
      statusBadge = '<span class="diff-badge new">New</span>';
    } else if (diffStatus === 'mod') {
      statusBadge = '<span class="diff-badge mod">Mod</span>';
    }

    li.innerHTML = `
      <span class="status-indicator"></span>
      <div style="display:flex; align-items:center; gap:0.5rem; min-width:0; overflow:hidden;">
        ${badge}
        <span class="file-path" title="${escapeHTML(o.repoPath)}" style="white-space:nowrap; text-overflow:ellipsis; overflow:hidden;">${escapeHTML(o.repoPath)}</span>
      </div>
      <div style="display:flex; align-items:center; gap:0.4rem;">
        ${statusBadge}
        ${isWarn ? `<span class="warning-badge" title="Files > 50MB should ideally use Git LFS">Large</span>` : ''}
        <span class="file-size">${fmt(o.file.size)}</span>
      </div>
      <div class="row-actions">
        <button class="action-icon-btn remove-btn" type="button" aria-label="Remove file" title="Remove file">×</button>
      </div>
    `;

    li.querySelector('.file-path').onclick = () => openFilePreview(o);
    li.querySelector('.remove-btn').onclick = (e) => {
      e.stopPropagation();
      files.delete(o.path);
      refresh();
      showToast(`Removed ${o.repoPath.split('/').pop()}`, 'info');
    };

    manifest.append(li);
    rowMap.set(o.path, li);
  });

  if (filtered.length > SHOW_LIMIT) {
    const li = document.createElement('li');
    li.style.padding = '0.75rem';
    li.style.textAlign = 'center';
    li.style.color = 'var(--muted)';
    li.textContent = `and ${(filtered.length - SHOW_LIMIT).toLocaleString()} more files (use search filter to locate)`;
    manifest.append(li);
  }

  // Render Tree View
  const treeContainer = $('#treeView');
  treeContainer.textContent = '';
  const treeRoot = buildTreeStructure(filtered);
  renderTree(treeRoot, treeContainer);

  // Notes & exclusions info
  const notes = [];
  if (junkCount) notes.push(`${junkCount.toLocaleString()} excluded by filters (clutter, secrets, or .git)`);
  if (bigFiles.length) notes.push(`${bigFiles.length} files over 50MB detected`);
  if (hardRejects.length) notes.push(`${hardRejects.length} files exceeded GitHub's 100MB limit and were skipped`);
  $('#note').hidden = !notes.length;
  $('#note').textContent = notes.join(' • ');

  // Bottom dock status
  const slug = slugOf(), br = $('#branch').value.trim() || $('#branch').placeholder || 'default branch';
  if (out.length) {
    $('#barMain').textContent = `${plural(out.length, 'file')} ready (${fmt(totalBytes)})`;
    $('#barSub').textContent = slug ? `Ready to push to ${slug} (${br})` : 'Enter a repository destination in Step 2';
    $('#go').disabled = !slug || !token;
  } else {
    $('#barMain').textContent = files.size ? 'All files excluded by filters' : 'No files selected';
    $('#barSub').textContent = 'Add a folder, files, or ZIP archive to continue';
    $('#go').disabled = true;
  }

  // Update Dropzone Title and Hint
  const idleTitle = () => coarsePointer ? 'Choose what to upload' : 'Drop a folder or ZIP here';
  const idleHint = () => coarsePointer ? 'On a mobile device, a ZIP file is the easiest way to send a whole folder.' : 'Or use the quick selection buttons below. You can add multiple times to merge files.';
  if (out.length) {
    const roots = new Set(out.map(o => o.path.split('/')[0]));
    $('#dropTitle').textContent = roots.size === 1 && out[0].path.includes('/') ? [...roots][0] : plural(out.length, 'file') + ' ready';
    $('#dropHint').textContent = 'Add more with the buttons below, or drop another folder to merge.';
  } else {
    $('#dropTitle').textContent = idleTitle();
    $('#dropHint').textContent = idleHint();
  }

  updateStepper();
}

// View toggle (Flat vs Tree)
$('#tabFlat').onclick = () => {
  currentView = 'flat';
  $('#tabFlat').classList.add('active');
  $('#tabFlat').setAttribute('aria-selected', 'true');
  $('#tabTree').classList.remove('active');
  $('#tabTree').setAttribute('aria-selected', 'false');
  $('#manifest').hidden = false;
  $('#treeView').hidden = true;
  $('#treeControls').hidden = true;
};

$('#tabTree').onclick = () => {
  currentView = 'tree';
  $('#tabTree').classList.add('active');
  $('#tabTree').setAttribute('aria-selected', 'true');
  $('#tabFlat').classList.remove('active');
  $('#tabFlat').setAttribute('aria-selected', 'false');
  $('#manifest').hidden = true;
  $('#treeView').hidden = false;
  $('#treeControls').hidden = false;
};

$('#expandAllBtn').onclick = () => {
  $$('.tree-children').forEach(c => c.classList.remove('collapsed'));
  $$('.tree-folder').forEach(f => f.classList.add('open'));
};

$('#collapseAllBtn').onclick = () => {
  $$('.tree-children').forEach(c => c.classList.add('collapsed'));
  $$('.tree-folder').forEach(f => f.classList.remove('open'));
};

$('#filter').addEventListener('input', refresh);
$('#skip').addEventListener('change', refresh);
$('#keepRoot').addEventListener('change', refresh);
$('#applyGitignore')?.addEventListener('change', refresh);
$('#customIgnore').addEventListener('input', refresh);

$('#clear').onclick = () => {
  if (busy) return;
  files.clear();
  remoteTreeMap.clear();
  fileGitShaMap.clear();
  fileSecretsMap.clear();
  gitignoreRules = [];
  $('#gitignoreOption').hidden = true;
  $('#result').hidden = true;
  msg('');
  srcMsg('');
  refresh();
  showToast('All files cleared', 'info');
};

/* ---------- File Preview Modal ---------- */
const modal = $('#previewModal');
let currentPreviewItem = null;
let currentPreviewText = null;

$('#closeModal').onclick = () => modal.close();
modal.addEventListener('click', (e) => {
  if (e.target === modal) modal.close();
});

$('#copyContentBtn').onclick = () => {
  if (!currentPreviewText) {
    showToast('No text content available to copy', 'err');
    return;
  }
  navigator.clipboard.writeText(currentPreviewText);
  const btn = $('#copyContentBtn');
  const txt = $('#copyContentText');
  txt.textContent = 'Copied!';
  btn.style.color = 'var(--ok)';
  showToast('File content copied to clipboard!', 'ok');
  setTimeout(() => {
    txt.textContent = 'Copy';
    btn.style.color = '';
  }, 2000);
};

$('#downloadFileBtn').onclick = () => {
  if (!currentPreviewItem) return;
  const a = document.createElement('a');
  a.href = URL.createObjectURL(currentPreviewItem.file);
  a.download = currentPreviewItem.repoPath.split('/').pop();
  a.click();
  URL.revokeObjectURL(a.href);
  showToast('Downloaded ' + a.download, 'ok');
};

async function openFilePreview(item) {
  currentPreviewItem = item;
  currentPreviewText = null;
  const { path, repoPath, file } = item;
  $('#previewTitle').textContent = repoPath;
  const body = $('#previewBody');
  body.textContent = 'Loading file contents…';
  modal.showModal();

  try {
    const isImage = /\.(png|jpe?g|gif|webp|svg|ico|bmp)$/i.test(path);
    if (isImage) {
      const url = URL.createObjectURL(file);
      body.innerHTML = `
        <div style="text-align:center; padding:1rem;">
          <img src="${url}" class="preview-img" alt="${escapeHTML(path)}">
          <div style="margin-top:1rem; font-size:0.8125rem; color:var(--muted); font-family:var(--mono);">
            Type: ${escapeHTML(file.type || 'image')} • Size: ${fmt(file.size)}
          </div>
        </div>
      `;
      return;
    }

    if (file.size > 2 * 1024 * 1024) {
      body.innerHTML = `
        <div style="padding:1.5rem; text-align:center; color:var(--muted);">
          <p>This file is ${fmt(file.size)}, which exceeds the in-browser 2MB preview limit.</p>
        </div>
      `;
      return;
    }

    const buf = await file.arrayBuffer();
    const text = asText(buf);
    if (text !== null) {
      currentPreviewText = text;
      const lines = text.split('\n');
      const secrets = fileSecretsMap.get(path) || [];
      const secretAlert = secrets.length ? `
        <div class="secret-hit-alert">
          <strong>Security Warning:</strong> Potential secret detected (${secrets.map(s => s.type).join(', ')}). Review before publishing!
        </div>
      ` : '';

      body.innerHTML = `
        ${secretAlert}
        <div style="display:flex; justify-content:space-between; align-items:center; font-size:0.75rem; color:var(--muted); margin-bottom:0.6rem; font-family:var(--mono);">
          <span>${lines.length} lines • ${fmt(file.size)}</span>
          ${getFileBadge(repoPath)}
        </div>
        <pre class="preview-code"><code>${escapeHTML(text)}</code></pre>
      `;
    } else {
      body.innerHTML = `
        <div style="padding:1.5rem; text-align:center; color:var(--muted);">
          <p>Binary file cannot be displayed as plain text.</p>
          <span style="font-family:var(--mono); font-size:0.8125rem;">Size: ${fmt(file.size)}</span>
        </div>
      `;
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
  if (e.key === 'Escape') {
    if (modal?.open) modal.close();
    if (secModal?.open) secModal.close();
  }
});

/* ---------- GitHub API Client ---------- */
const CANCELLED_ERR = () => Object.assign(new Error('Operation cancelled by user'), { cancelled: true });

async function gh(path, opts = {}, attempt = 0) {
  const { noRetry, ...init } = opts;
  const headers = {
    'Accept': 'application/vnd.github+json',
    'Authorization': 'Bearer ' + token,
    'X-GitHub-Api-Version': '2022-11-28'
  };
  if (init.body) headers['Content-Type'] = 'application/json';

  let res;
  try {
    res = await fetch(API + path, { ...init, headers, signal: abortCtrl ? abortCtrl.signal : null });
  } catch (e) {
    if (e.name === 'AbortError') throw CANCELLED_ERR();
    if (!noRetry && attempt < 2) {
      await sleep(1000 * (attempt + 1));
      if (cancelled) throw CANCELLED_ERR();
      return gh(path, opts, attempt + 1);
    }
    throw e;
  }

  // Update rate limit pill
  const remaining = res.headers.get('x-ratelimit-remaining');
  const limit = res.headers.get('x-ratelimit-limit');
  const reset = Number(res.headers.get('x-ratelimit-reset'));
  if (remaining && limit) {
    const mins = reset ? Math.max(0, Math.ceil((reset - Date.now() / 1000) / 60)) : 0;
    $('#rateLimitPill').textContent = `Rate: ${remaining}/${limit} (${mins}m reset)`;
  }

  if (!res.ok) {
    const retryAfter = Number(res.headers.get('retry-after'));
    let wait = 0;
    if (retryAfter) wait = retryAfter;
    else if ((res.status === 403 || res.status === 429) && remaining === '0' && reset) {
      wait = Math.max(1, reset - Date.now() / 1000 + 1);
    } else if (res.status >= 500) {
      wait = 1.5 * (attempt + 1);
    }

    if (wait && wait <= 90 && attempt < 4 && !noRetry) {
      if (busy && wait > 2) msg(`GitHub rate limit wait. Resuming in ${Math.ceil(wait)}s…`);
      await sleep(wait * 1000);
      if (cancelled) throw CANCELLED_ERR();
      return gh(path, opts, attempt + 1);
    }

    let m = res.statusText;
    try {
      const j = await res.json();
      m = j.message || m;
      if (j.errors && j.errors[0] && j.errors[0].message) m += ` (${j.errors[0].message})`;
    } catch {}
    throw Object.assign(new Error(m), { status: res.status });
  }

  return res.status === 204 ? null : res.json();
}

const toBase64 = f => new Promise((res, rej) => {
  const r = new FileReader();
  r.onload = () => res(r.result.slice(r.result.indexOf(',') + 1));
  r.onerror = () => rej(new Error('Failed to read file'));
  r.readAsDataURL(f);
});

function msg(t, cls) {
  const m = $('#msg');
  m.textContent = t;
  m.className = 'status-msg ' + (cls || '');
}

function setBusy(b) {
  busy = b;
  const g = $('#go');
  const txt = $('#goText');
  if (b) {
    txt.textContent = 'Cancel';
    g.classList.add('btn-cancel');
    g.classList.remove('btn-primary');
    uploadStartTime = Date.now();
  } else {
    txt.textContent = 'Upload to GitHub';
    g.classList.remove('btn-cancel');
    g.classList.add('btn-primary');
    $('#prog').value = 0;
    refresh();
  }
  $('#clear').disabled = b;
}

window.addEventListener('beforeunload', e => {
  if (busy) {
    e.preventDefault();
    e.returnValue = '';
  }
});

/* ---------- Main Upload Execution ---------- */
$('#go').onclick = () => {
  if (busy) {
    cancelled = true;
    if (abortCtrl) abortCtrl.abort();
    msg('Cancelling upload process…');
    return;
  }

  // Pre-commit Secret Safety Guard
  if (fileSecretsMap.size > 0 && !$('#skipSecretsCheck')?.checked) {
    $('#secretModalCount').textContent = fileSecretsMap.size;
    secModal?.showModal();
    playSound('warn');
    return;
  }

  executeUpload(false);
};

async function executeUpload(overrideSecrets = false) {
  const { out } = computeCurrentManifest();
  if (!out.length) return;

  $('#result').hidden = true;
  token = $('#token').value.trim();
  if (!token) return msg('Please provide your GitHub Personal Access Token in Step 1.', 'err');

  const create = $('#create').checked;
  let slug = slugOf();
  if (create ? !/^[\w.-]+$/.test(slug.split('/').pop()) : !/^[\w.-]+\/[\w.-]+$/.test(slug)) {
    return msg(create ? 'Enter a valid repository name for your account.' : 'Enter destination as owner/repository.', 'err');
  }

  const wantBranch = $('#branch').value.trim();
  const commitTitle = $('#commit').value.trim() || 'Upload files via Folder to GitHub';
  const commitDesc = $('#commitDesc').value.trim();
  const fullCommitMessage = commitDesc ? `${commitTitle}\n\n${commitDesc}` : commitTitle;
  const isPrivate = $('#private').checked;

  if (badBranch(wantBranch)) {
    return msg('Invalid branch name. Avoid spaces and characters like ~ ^ : ? * [ \\ and ".."', 'err');
  }

  store.set('f2g.repo', create ? '' : slug);
  store.set('f2g.branch', wantBranch);
  store.set('f2g.prefix', $('#prefix').value.trim());
  if ($('#remember').checked) store.set('f2g.token', token);

  cancelled = false;
  abortCtrl = new AbortController();
  setBusy(true);
  let repoCreated = false;

  setPipelineStage(1, 'Verifying GitHub repository…', 'Connecting to ' + slug + '…');

  try {
    let repo;
    if (create) {
      if (!me) await verifyToken();
      if (!me) throw new Error('Token verification required to create repository');
      msg('Creating new repository on GitHub…');
      setPipelineStage(1, 'Creating new repository…', slug);
      repo = await gh('/user/repos', {
        method: 'POST',
        noRetry: true,
        body: JSON.stringify({
          name: slug.split('/').pop(),
          private: isPrivate,
          auto_init: true,
          description: 'Uploaded via Folder to GitHub'
        })
      });
      repoCreated = true;
      slug = repo.full_name;
      $('#create').checked = false;
      $('#create').dispatchEvent(new Event('change'));
      $('#repo').value = slug;
      store.set('f2g.repo', slug);

      // Wait for initial commit initialization
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

    const branch = wantBranch || repo.default_branch;
    const refPath = b => '/repos/' + slug + '/git/ref/heads/' + enc(b);
    let baseSha = null, seededEmpty = false;

    try {
      baseSha = (await gh(refPath(branch))).object.sha;
    } catch (e) {
      if (e.status === 409) {
        msg('Repository is empty. Initializing starter commit…');
        await gh('/repos/' + slug + '/contents/.gitkeep', {
          method: 'PUT',
          body: JSON.stringify({ message: 'Initialize repository', content: 'Cg==', branch })
        });
        baseSha = (await gh(refPath(branch))).object.sha;
        seededEmpty = true;
      } else if (e.status !== 404) {
        throw e;
      }
    }

    if (!baseSha) {
      msg(`Creating branch "${branch}" based on "${repo.default_branch}"…`);
      baseSha = (await gh(refPath(repo.default_branch))).object.sha;
      await gh('/repos/' + slug + '/git/refs', {
        method: 'POST',
        body: JSON.stringify({ ref: 'refs/heads/' + branch, sha: baseSha })
      });
    }

    const parentCommit = await gh('/repos/' + slug + '/git/commits/' + baseSha);

    // Filter unchanged files if requested
    const skipUnchanged = $('#skipUnchanged')?.checked;
    const uploadTargets = skipUnchanged 
      ? out.filter(o => getFileDiffStatus(o.repoPath) !== 'same')
      : out;

    if (!uploadTargets.length) {
      throw Object.assign(new Error('identical_tree'), { identical: true });
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
          if (!e.cancelled) e.file = o.repoPath;
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

        setPipelineStage(2, `Uploading Blobs (${doneCount}/${uploadTargets.length})`, o.repoPath, `${fmt(speed)}/s`);

        if (li) {
          li.classList.remove('uploading');
          li.classList.add('done');
        }
      }
    }

    const CONCURRENCY = Math.min(5, Math.max(1, uploadTargets.length));
    await Promise.all(Array.from({ length: CONCURRENCY }, uploadWorker));
    if (cancelled) throw CANCELLED_ERR();

    msg('Constructing Git tree…');
    setPipelineStage(3, 'Constructing Git Tree…', 'Chaining directory tree objects…');

    const treeList = entries.slice();
    if (seededEmpty && !uploadTargets.some(o => o.repoPath === '.gitkeep')) {
      treeList.push({ path: '.gitkeep', mode: '100644', type: 'blob', sha: null });
    }

    let treeSha = parentCommit.tree.sha, chunk = [], currentChunkSize = 0;
    const flushTreeChunk = async () => {
      if (!chunk.length) return;
      treeSha = (await gh('/repos/' + slug + '/git/trees', {
        method: 'POST',
        body: JSON.stringify({ base_tree: treeSha, tree: chunk })
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

    if (treeSha === parentCommit.tree.sha) {
      throw Object.assign(new Error('identical_tree'), { identical: true });
    }

    msg('Creating Git commit object…');
    setPipelineStage(4, 'Creating Git Commit Object…', fullCommitMessage.split('\n')[0]);

    const commitObj = await gh('/repos/' + slug + '/git/commits', {
      method: 'POST',
      body: JSON.stringify({ message: fullCommitMessage, tree: treeSha, parents: [baseSha] })
    });

    msg('Updating branch reference…');
    setPipelineStage(5, 'Updating Branch Reference…', `Pointing refs/heads/${branch} to ${commitObj.sha.slice(0, 7)}`);

    await gh('/repos/' + slug + '/git/refs/heads/' + enc(branch), {
      method: 'PATCH',
      body: JSON.stringify({ sha: commitObj.sha })
    });

    $('#prog').value = 100;
    setPipelineStage(6, 'Commit Published!', 'Complete');
    setTimeout(() => {
      $('#pipelineCard').hidden = true;
    }, 1400);

    // Confetti & Audio celebration
    triggerConfetti();
    playSound('success');
    showToast(`Published ${plural(uploadTargets.length, 'file')} to ${branch}!`, 'ok');
    msg('');

    // Success Card Presentation
    const resEl = $('#result');
    resEl.hidden = false;

    $('#resultMeta').innerHTML = `
      Pushed <strong>${plural(uploadTargets.length, 'file')}</strong> (${fmt(totalBytes)}) to 
      <a href="${repo.html_url}/tree/${enc(branch)}" target="_blank" rel="noopener" style="color:var(--accent); text-decoration:underline;">
        ${escapeHTML(slug)}:${escapeHTML(branch)}
      </a>
      <div style="margin-top:0.6rem;">
        Commit: <span class="sha-badge" id="shaPill">${commitObj.sha.slice(0, 7)}
          <button class="action-icon-btn" id="copyShaBtn" type="button" title="Copy full SHA" style="width:1.25rem; height:1.25rem;">
            <svg class="icon icon-sm" viewBox="0 0 24 24"><rect width="14" height="14" x="8" y="8" rx="2" ry="2"/><path d="M4 16c-1.1 0-2-.9-2-2V4c0-1.1.9-2 2-2h10c1.1 0 2 .9 2 2"/></svg>
          </button>
        </span>
      </div>
    `;

    $('#copyShaBtn').onclick = () => {
      navigator.clipboard.writeText(commitObj.sha);
      showToast('Commit SHA copied: ' + commitObj.sha.slice(0, 7), 'ok');
      const pill = $('#shaPill');
      if (pill) {
        pill.style.borderColor = 'var(--ok)';
        setTimeout(() => pill.style.borderColor = '', 2000);
      }
    };

    const acts = $('#resultActions');
    acts.innerHTML = `
      <a class="btn btn-primary" href="${repo.html_url}/commit/${commitObj.sha}" target="_blank" rel="noopener">
        <svg class="icon" viewBox="0 0 24 24"><path d="M15 3h6v6"/><path d="M10 14 21 3"/><path d="M18 13v6a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h6"/></svg>
        <span>View Commit Diff</span>
      </a>
      <a class="btn" href="${repo.html_url}/tree/${enc(branch)}" target="_blank" rel="noopener">
        <svg class="icon" viewBox="0 0 24 24"><path d="M22 19a2 2 0 0 1-2 2H4a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h5l2 3h9a2 2 0 0 1 2 2z"/></svg>
        <span>Browse Repository</span>
      </a>
      <a class="btn" href="https://github.dev/${slug}/tree/${enc(branch)}" target="_blank" rel="noopener" title="Open in browser VS Code">
        <svg class="icon" viewBox="0 0 24 24"><polyline points="16 18 22 12 16 6"/><polyline points="8 6 2 12 8 18"/></svg>
        <span>Open in github.dev</span>
      </a>
      <button class="btn btn-subtle" id="uploadAnotherBtn" type="button">Upload another batch</button>
    `;

    $('#uploadAnotherBtn').onclick = () => {
      $('#clear').click();
    };

    resEl.scrollIntoView({ behavior: 'smooth', block: 'center' });
  } catch (err) {
    $('#pipelineCard').hidden = true;
    playSound('warn');
    if (err.cancelled) {
      msg('Upload cancelled. No commits were created.' + (repoCreated ? ' The new repository was already initialized.' : ''));
    } else if (err.identical) {
      msg('Nothing to commit. The destination branch already has these exact files and contents.', 'ok');
      showToast('Destination branch already has these exact files', 'info');
    } else {
      let advice = '';
      if (err.status === 401) advice = ' Verify your token has not expired and has valid permissions.';
      else if (err.status === 403) advice = ' The token is missing write permissions for this repository' + (create ? ' or lacks repo creation scope.' : '.');
      else if (err.status === 404) advice = ' Target repository not found, or your token does not have access.';
      else if (err.status === 422 && create) advice = ' A repository with this name already exists. Uncheck "Create new repository" to push to it.';
      else if (err.name === 'TypeError') advice = ' Network error. Check your internet connection.';
      msg(`Upload failed${err.file ? ' on ' + err.file : ''}: ${err.message}.${advice}`, 'err');
      showToast(`Upload failed: ${err.message}`, 'err');
    }
  } finally {
    abortCtrl = null;
    setBusy(false);
  }
}

/* ---------- Initialization ---------- */
initTheme();
initSound();
$('#repo').value = store.get('f2g.repo');
$('#branch').value = store.get('f2g.branch');
$('#prefix').value = store.get('f2g.prefix');
if (store.get('f2g.token')) {
  $('#token').value = store.get('f2g.token');
  $('#remember').checked = true;
  verifyToken();
}
refresh();
