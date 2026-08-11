import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';

const scriptDirectory = dirname(fileURLToPath(import.meta.url));
const userscriptPath = resolve(scriptDirectory, '..', 'nodeseek-nested-replies.user.js');
const source = readFileSync(userscriptPath, 'utf8');
const failures = [];

const requiredPatterns = [
  ['exact NodeSeek post scope', /^\/\/ @match\s+https:\/\/www\.nodeseek\.com\/post-\*$/m],
  ['document-start anti-flicker', /^\/\/ @run-at\s+document-start$/m],
  ['no privileged userscript APIs', /^\/\/ @grant\s+none$/m],
  ['no iframe execution', /^\/\/ @noframes$/m],
  ['namespaced boolean preference', /const STORAGE_KEY = 'ns-nested-replies:enabled';/],
  ['preference read uses the fixed key', /window\.localStorage\.getItem\(STORAGE_KEY\)/],
  ['preference write uses the fixed key', /window\.localStorage\.setItem\(STORAGE_KEY, enabled \? 'true' : 'false'\)/],
  ['header theme-switch adjacency', /#nsk-head > \.color-theme-switcher/],
  ['same-origin authenticated page fetch', /credentials:\s*includeSession \? 'same-origin' : 'omit'/],
  ['same-origin request mode', /mode:\s*'same-origin'/],
  ['redirect rejection', /redirect:\s*'error'/],
  ['referrer suppression', /referrerPolicy:\s*'no-referrer'/],
  ['post-only read allowlist', /&& POST_PATH_RE\.test\(url\.pathname\)/],
  ['bounded page scan', /maxPagesPerPost:\s*12/],
  ['bounded response size', /maxResponseBytes:\s*2_000_000/],
  ['bounded native page wait', /nativePageTimeoutMs:\s*12_000/],
  ['limited scan concurrency', /scanConcurrency:\s*2/],
  ['remote event-handler stripping', /name\.startsWith\('on'\)/],
  ['boot visibility mask', /function beginInitialMask\(\)[\s\S]*BOOT_CLASS/],
  ['final one-shot reveal', /function revealFinalView\(\)[\s\S]*classList\.remove\(BOOT_CLASS\)/],
  ['lazy native page loader', /function preloadNativePage\(page\)/],
  ['native page only loads on hydration', /async function hydrateRemoteFloor\(floor\)[\s\S]*await preloadNativePage\(page\)/],
  ['strict same-post iframe URL', /new URL\(\x60\/post-\$\{postInfo\.postId\}-\$\{page\}\x60, window\.location\.origin\)/],
  ['restricted native frame sandbox', /setAttribute\('sandbox', 'allow-scripts allow-same-origin'\)/],
  ['same-origin frame referrer policy', /frame\.referrerPolicy = 'same-origin'/],
  ['native menu readiness check', /comments\.every\(\(item\) => item\.querySelector\(':scope > \.comment-menu'\)\)/],
  ['cross-realm element helper', /function isElementNode\(value, expectedLocalName = null\)[\s\S]*value\.nodeType === Node\.ELEMENT_NODE/],
  ['cross-realm source-node validation', /!isElementNode\(sourceItem, 'li'\)/],
  ['cross-realm reply-anchor validation', /\(child\) => isElementNode\(child, 'a'\)/],
  ['unloaded earlier-page reply suppression', /target < earliestOrdinaryLocalFloor[\s\S]*reachesEarlierPage = true/],
  ['native menu node adoption', /document\.adoptNode\(sourceItem\)/],
  ['native profile card reuse', /const card = window\.hoverCard/],
  ['native card method validation', /typeof card\.loadUser !== 'function'[\s\S]*typeof card\.show !== 'function'/],
  ['native editor reuse', /const editor = window\.editor/],
  ['transient source config bridge', /function withTemporaryPageConfig\(config, callback\)[\s\S]*Reflect\.deleteProperty\(window, '__config__'\)/],
];

const forbiddenPatterns = [
  ['remote dependency', /^\/\/ @(require|resource|updateURL|downloadURL)\b/m],
  ['cross-origin userscript permission', /^\/\/ @connect\b/m],
  ['userscript sandbox privilege', /^\/\/ @sandbox\b/m],
  ['XMLHttpRequest', /\bXMLHttpRequest\b/],
  ['WebSocket', /\bWebSocket\b/],
  ['EventSource', /\bEventSource\b/],
  ['sendBeacon', /\bsendBeacon\b/],
  ['cookie access', /\bdocument\s*\.\s*cookie\b/],
  ['storage enumeration or deletion', /\blocalStorage\s*\.\s*(?:key|clear|removeItem)\s*\(/],
  ['session storage access', /\bsessionStorage\b/],
  ['userscript privileged API', /\bGM(?:_|\.)/],
  ['page-global escape', /\bunsafeWindow\b/],
  ['dynamic code execution', /\beval\s*\(|\bFunction\s*\(/],
  ['HTML string injection', /\binnerHTML\s*=|\bouterHTML\s*=|\binsertAdjacentHTML\s*\(/],
  ['document stream injection', /\bdocument\s*\.\s*write\s*\(/],
  ['iframe srcdoc injection', /\.srcdoc\s*=|setAttribute\(\s*['"]srcdoc['"]/i],
  ['powerful iframe sandbox flag', /allow-(?:top-navigation|forms|popups|downloads|pointer-lock|presentation)/],
  ['direct API endpoint call', /['"]\/api\//i],
  ['handwritten profile card', /fetchPublicProfileInfo|createProfileCardShell|PROFILE_CARD_CLASS/],
  ['cross-realm-unsafe source-node check', /!\(sourceItem instanceof HTMLElement\)/],
];

const metadataVersion = source.match(/^\/\/ @version\s+([^\s]+)$/m)?.[1];
const scriptVersion = source.match(/const SCRIPT_VERSION = '([^']+)';/)?.[1];
if (!metadataVersion || metadataVersion !== scriptVersion) {
  failures.push(`Metadata version ${metadataVersion || 'missing'} does not match SCRIPT_VERSION ${scriptVersion || 'missing'}`);
}

const fetchCallCount = (source.match(/\b(?:window\.)?fetch\s*\(/g) || []).length;
if (fetchCallCount !== 1) {
  failures.push(`Expected exactly one audited fetch call, found ${fetchCallCount}`);
}

const iframeCreationCount = (source.match(/createElement\s*\(\s*['"]iframe['"]\s*\)/g) || []).length;
if (iframeCreationCount !== 1) {
  failures.push(`Expected exactly one audited iframe creation site, found ${iframeCreationCount}`);
}

const localStorageReferenceCount = (source.match(/\bwindow\.localStorage\b/g) || []).length;
if (localStorageReferenceCount !== 2) {
  failures.push(
    `Expected exactly two fixed-key localStorage references, found ${localStorageReferenceCount}`,
  );
}

for (const [label, pattern] of requiredPatterns) {
  if (!pattern.test(source)) {
    failures.push(`Missing requirement: ${label}`);
  }
}

for (const [label, pattern] of forbiddenPatterns) {
  if (pattern.test(source)) {
    failures.push(`Forbidden capability found: ${label}`);
  }
}

if (failures.length > 0) {
  console.error(failures.join('\n'));
  process.exitCode = 1;
} else {
  console.log('Security checks passed.');
}
