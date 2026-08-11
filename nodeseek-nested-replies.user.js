// ==UserScript==
// @name         NodeSeek 楼中楼
// @name:en      NodeSeek Nested Replies
// @namespace    https://www.nodeseek.com/
// @version      0.8.2
// @description  将同一帖子内（含跨页）的回复整理为紧凑、可开关的楼中楼。
// @description:en Group same-thread NodeSeek replies, including later pages, into compact toggleable threads.
// @author       NodeSeek community
// @license      MIT
// @match        https://www.nodeseek.com/post-*
// @run-at       document-start
// @grant        none
// @noframes
// ==/UserScript==

(() => {
  'use strict';

  /**
   * Security design:
   * - Runs only on NodeSeek post pages and requests no userscript privileges.
   * - Never reads cookies, tokens, clipboard, private messages, or unrelated storage.
   * - Stores only one namespaced boolean that remembers whether the UI is enabled.
   * - Makes bounded same-post GET requests with the current NodeSeek session to discover reply
   *   relationships. A source page is loaded in an isolated, non-interactive same-origin frame
   *   only after the user expands one of its cross-page replies.
   * - Reuses NodeSeek's already-mounted comment menu, profile card, and editor components. It
   *   never recreates those account-facing controls or calls their action endpoints itself.
   * - Never performs account actions automatically. Native and mirrored controls act only after
   *   the user's click; the script never invents or calls vote/reply endpoints.
   * - Builds UI with DOM APIs and textContent; it never injects strings as HTML.
   * - Sanitizes inert cross-page comment nodes before adding them to the live page.
   */

  const CONFIG = Object.freeze({
    defaultVisibleReplies: 3,
    maxCommentsPerPage: 500,
    maxPagesPerPost: 12,
    maxResponseBytes: 2_000_000,
    fetchTimeoutMs: 8_000,
    scanConcurrency: 2,
    nativePageTimeoutMs: 12_000,
    renderDelayMs: 40,
  });

  const SCRIPT_VERSION = '0.8.2';
  const PREFIX = 'ns-nested-replies';
  const STORAGE_KEY = 'ns-nested-replies:enabled';
  const STYLE_ID = `${PREFIX}-style`;
  const BOOT_STYLE_ID = `${PREFIX}-boot-style`;
  const BOOT_CLASS = `${PREFIX}--booting`;
  const LOADING_ID = `${PREFIX}-loading`;
  const TOGGLE_ID = `${PREFIX}-toggle`;
  const THREAD_CLASS = `${PREFIX}__thread`;
  const LIST_CLASS = `${PREFIX}__list`;
  const CHILD_CLASS = `${PREFIX}__child`;
  const COLLAPSED_CLASS = `${PREFIX}__collapsed`;
  const THREAD_TOGGLE_CLASS = `${PREFIX}__thread-toggle`;
  const SUMMARY_CLASS = `${PREFIX}__summary`;
  const COMPACT_HEADER_CLASS = `${PREFIX}__compact-header`;
  const RELATION_CLASS = `${PREFIX}__relation`;
  const DETAIL_TOGGLE_CLASS = `${PREFIX}__detail-toggle`;
  const DETAIL_EXPANDED_CLASS = `${PREFIX}__detail-expanded`;
  const REPLY_MARKER_CLASS = `${PREFIX}__reply-marker`;
  const SUPPRESSED_CLASS = `${PREFIX}__suppressed`;
  const MIRROR_ATTRIBUTE = `data-${PREFIX}-mirror`;
  const FLOOR_ATTRIBUTE = `data-${PREFIX}-floor`;
  const HIGHLIGHT_CLASS = `${PREFIX}__highlight`;
  const PROFILE_AVATAR_CLASS = `${PREFIX}__profile-avatar`;
  const PROFILE_NAME_CLASS = `${PREFIX}__profile-name`;
  const FLOOR_LABEL_CLASS = `${PREFIX}__floor-label`;
  const REMOTE_ATTRIBUTE = `data-${PREFIX}-remote`;
  const SOURCE_PAGE_ATTRIBUTE = `data-${PREFIX}-source-page`;
  const NATIVE_READY_ATTRIBUTE = `data-${PREFIX}-native-ready`;
  const NATIVE_FRAME_CLASS = `${PREFIX}__native-frame`;
  const POST_PATH_RE = /^\/post-(\d+)-(\d+)\/?$/;
  const PROFILE_PATH_RE = /^\/space\/([1-9]\d*)\/?$/;
  const FLOOR_TEXT_RE = /^#([1-9]\d*)$/;
  const FLOOR_ID_RE = /^[1-9]\d*$/;
  const DANGEROUS_REMOTE_ELEMENTS = [
    'script',
    'style',
    'link',
    'meta',
    'base',
    'iframe',
    'object',
    'embed',
    'form',
    'input',
    'textarea',
    'select',
    'button',
  ].join(',');

  const state = {
    enabled: true,
    commentList: null,
    originalLocalItems: [],
    listObserver: null,
    discoveryObserver: null,
    discoveryTimer: null,
    renderTimer: null,
    remoteTemplates: new Map(),
    hydratedRemoteItems: new Map(),
    nativePages: new Map(),
    bridgedNativeItems: new WeakSet(),
    profileBridgedItems: new WeakSet(),
    pageScanStarted: false,
    pageScanComplete: false,
    scanGeneration: 0,
    viewKey: '',
    expandedThreads: new Set(),
    expandedDetails: new Set(),
    lastRevealedFloor: null,
    initialRevealComplete: false,
  };

  function beginInitialMask() {
    if (!readEnabledPreference() || !document.documentElement) {
      return;
    }

    document.documentElement.classList.add(BOOT_CLASS);
    if (document.getElementById(BOOT_STYLE_ID)) {
      return;
    }

    const style = document.createElement('style');
    style.id = BOOT_STYLE_ID;
    style.textContent = `
      html.${BOOT_CLASS} .comment-container {
        visibility: hidden !important;
      }
    `;
    document.documentElement.append(style);
  }

  function showLoadingIndicator(commentList) {
    if (!state.enabled || document.getElementById(LOADING_ID)) {
      return;
    }

    const loading = createElement('div', `${PREFIX}__loading`, '正在整理楼中楼…');
    loading.id = LOADING_ID;
    loading.setAttribute('role', 'status');
    loading.setAttribute('aria-live', 'polite');
    const container = commentList.closest('.comment-container');
    container?.insertAdjacentElement('beforebegin', loading);
  }

  function revealFinalView() {
    state.initialRevealComplete = true;
    document.documentElement?.classList.remove(BOOT_CLASS);
    document.getElementById(LOADING_ID)?.remove();
  }

  beginInitialMask();

  function readEnabledPreference() {
    try {
      return window.localStorage.getItem(STORAGE_KEY) !== 'false';
    } catch {
      return true;
    }
  }

  function writeEnabledPreference(enabled) {
    try {
      window.localStorage.setItem(STORAGE_KEY, enabled ? 'true' : 'false');
    } catch {
      // A blocked storage API only makes the preference non-persistent.
    }
  }

  function parseSafePositiveInteger(value) {
    if (typeof value !== 'string' || value.length > 15 || !FLOOR_ID_RE.test(value)) {
      return null;
    }

    const number = Number(value);
    return Number.isSafeInteger(number) && number > 0 ? number : null;
  }

  function getCurrentPostInfo() {
    const match = POST_PATH_RE.exec(window.location.pathname);
    if (!match) {
      return null;
    }

    const page = parseSafePositiveInteger(match[2]);
    return page === null ? null : { postId: match[1], page };
  }

  function getFloor(item) {
    return parseSafePositiveInteger(item.getAttribute('id') || '');
  }

  // adoptNode() preserves the source frame's DOM wrappers, so parent-realm instanceof checks
  // reject otherwise valid native floors and descendants. Structural checks work in both realms.
  function isElementNode(value, expectedLocalName = null) {
    return Boolean(
      value
      && typeof value === 'object'
      && value.nodeType === Node.ELEMENT_NODE
      && typeof value.localName === 'string'
      && typeof value.getAttribute === 'function'
      && typeof value.querySelector === 'function'
      && typeof value.closest === 'function'
      && (expectedLocalName === null || value.localName === expectedLocalName),
    );
  }

  function createElement(tagName, className, text) {
    const element = document.createElement(tagName);
    if (className) {
      element.className = className;
    }
    if (typeof text === 'string') {
      element.textContent = text;
    }
    return element;
  }

  function parseSameOriginUrl(rawValue) {
    if (typeof rawValue !== 'string' || rawValue.length > 2_048) {
      return null;
    }

    try {
      const url = new URL(rawValue, window.location.href);
      return url.origin === window.location.origin ? url : null;
    } catch {
      return null;
    }
  }

  function isAllowedReadOnlyRequest(url) {
    return url instanceof URL
      && url.origin === window.location.origin
      && !url.username
      && !url.password
      && !url.hash
      && POST_PATH_RE.test(url.pathname);
  }

  async function fetchSameOriginText(
    url,
    accept,
    expectedContentType,
    maxBytes,
    includeSession = false,
  ) {
    if (!isAllowedReadOnlyRequest(url)) {
      return null;
    }

    const controller = new AbortController();
    const timeout = window.setTimeout(() => controller.abort(), CONFIG.fetchTimeoutMs);

    try {
      const response = await window.fetch(url, {
        method: 'GET',
        mode: 'same-origin',
        credentials: includeSession ? 'same-origin' : 'omit',
        cache: 'force-cache',
        redirect: 'error',
        referrerPolicy: 'no-referrer',
        headers: { Accept: accept },
        signal: controller.signal,
      });
      if (!response.ok) {
        return null;
      }

      const responseUrl = new URL(response.url);
      const contentType = (response.headers.get('content-type') || '').toLowerCase();
      const contentLength = Number(response.headers.get('content-length') || '0');
      if (
        !isAllowedReadOnlyRequest(responseUrl)
        || !contentType.includes(expectedContentType)
        || (Number.isFinite(contentLength) && contentLength > maxBytes)
      ) {
        return null;
      }

      const text = await response.text();
      if (text.length === 0 || text.length > maxBytes) {
        return null;
      }
      return { text, responseUrl };
    } catch {
      return null;
    } finally {
      window.clearTimeout(timeout);
    }
  }

  function isMemberMention(anchor) {
    if (!isElementNode(anchor, 'a')) {
      return false;
    }

    const url = parseSameOriginUrl(anchor.getAttribute('href') || '');
    return Boolean(url && url.pathname === '/member' && url.searchParams.has('t'));
  }

  function getReplyMetadata(item, currentPostId) {
    const firstParagraph = item.querySelector(':scope > article.post-content > p:first-child');
    if (!firstParagraph) {
      return null;
    }

    const anchors = Array.from(firstParagraph.children).filter(
      (child) => isElementNode(child, 'a'),
    );

    for (const floorAnchor of anchors) {
      const floorMatch = FLOOR_TEXT_RE.exec((floorAnchor.textContent || '').trim());
      const memberAnchor = floorAnchor.previousElementSibling;
      if (!floorMatch || !isMemberMention(memberAnchor)) {
        continue;
      }

      const url = parseSameOriginUrl(floorAnchor.getAttribute('href') || '');
      const pathMatch = url ? POST_PATH_RE.exec(url.pathname) : null;
      const targetFloor = parseSafePositiveInteger(floorMatch[1]);

      if (
        targetFloor !== null
        && url
        && pathMatch
        && pathMatch[1] === currentPostId
        && url.hash === `#${targetFloor}`
      ) {
        const targetUser = (memberAnchor.textContent || '')
          .trim()
          .replace(/^@/, '')
          .slice(0, 80);

        return {
          targetFloor,
          targetUser: targetUser || `楼层 ${targetFloor}`,
          memberAnchor,
          floorAnchor,
        };
      }
    }

    return null;
  }

  function getAuthorName(item) {
    const profileLinks = Array.from(
      item.querySelectorAll(':scope > .nsk-content-meta-info a[href^="/space/"]'),
    );
    const visibleName = profileLinks
      .map((link) => (link.textContent || '').trim())
      .find(Boolean);

    if (visibleName) {
      return visibleName.slice(0, 80);
    }

    const avatarAlt = item.querySelector(':scope > .nsk-content-meta-info img[alt]')
      ?.getAttribute('alt')
      ?.trim();
    return avatarAlt ? avatarAlt.slice(0, 80) : '该用户';
  }

  function isPinnedItem(item) {
    return Boolean(item.querySelector(
      ':scope > .nsk-content-meta-info .hot-badge,'
      + ':scope > .nsk-content-meta-info .pined-comment-badge,'
      + ':scope > .nsk-content-meta-info [title="置顶"]',
    ));
  }

  function getSafeProfileUrl(item) {
    const profileAnchor = item.querySelector(
      ':scope > .nsk-content-meta-info a[href^="/space/"]',
    );
    const url = profileAnchor
      ? parseSameOriginUrl(profileAnchor.getAttribute('href') || '')
      : null;
    return url && url.pathname.startsWith('/space/') ? url : null;
  }

  function getSafeAvatarImageSource(item) {
    const image = item.querySelector(
      ':scope > .nsk-content-meta-info .avatar-wrapper img[src],'
      + ':scope > .nsk-content-meta-info img.avatar-normal[src]',
    );
    const source = image?.getAttribute('src') || '';
    return source && isSafeRemoteUrl('src', source) ? source : null;
  }

  function getMemberIdFromProfileUrl(profileUrl) {
    const match = profileUrl instanceof URL ? PROFILE_PATH_RE.exec(profileUrl.pathname) : null;
    return match ? parseSafePositiveInteger(match[1]) : null;
  }

  function createProfileName(item, fallbackName) {
    const name = getAuthorName(item) || fallbackName;
    const url = getSafeProfileUrl(item);
    if (!url) {
      return createElement('span', PROFILE_NAME_CLASS, name);
    }

    const link = createElement('a', PROFILE_NAME_CLASS, name);
    link.classList.add('author-name');
    link.href = `${url.pathname}${url.search}${url.hash}`;
    link.rel = 'noopener noreferrer';
    link.title = name;
    return link;
  }

  function getNativeHoverCard() {
    const card = window.hoverCard;
    if (
      !card
      || typeof card.setIsHoverCard !== 'function'
      || typeof card.loadUser !== 'function'
      || typeof card.show !== 'function'
      || typeof card.$mount !== 'function'
    ) {
      return null;
    }

    try {
      card.setIsHoverCard(true);
      if (!(card.$el instanceof HTMLElement) || !card.$el.isConnected) {
        const mount = document.createElement('div');
        (document.body || document.documentElement).append(mount);
        card.$mount(mount);
      }
      return card.$el instanceof HTMLElement && card.$el.isConnected ? card : null;
    } catch {
      return null;
    }
  }

  function showNativeProfileCard(profileUrl, sourceElement) {
    const memberId = getMemberIdFromProfileUrl(profileUrl);
    const card = getNativeHoverCard();
    if (memberId === null || !card) {
      return false;
    }

    const rect = isElementNode(sourceElement)
      ? sourceElement.getBoundingClientRect()
      : { left: 12, top: 12 };
    const left = Math.max(8, Math.min(window.innerWidth - 268, rect.left));
    const top = Math.max(8, Math.min(window.innerHeight - 178, rect.top));

    try {
      card.left = left;
      card.top = top;
      card.loadUser(memberId);
      card.show();
      return true;
    } catch {
      return false;
    }
  }

  function createProfileAvatar(item) {
    const url = getSafeProfileUrl(item);
    const rawSource = getSafeAvatarImageSource(item);
    if (!url || !rawSource) {
      return null;
    }

    const name = getAuthorName(item);
    const button = createElement('button', PROFILE_AVATAR_CLASS);
    button.type = 'button';
    button.title = `查看 ${name} 的个人卡片`;
    button.setAttribute('aria-label', button.title);
    button.addEventListener('click', (event) => {
      event.preventDefault();
      event.stopPropagation();
      showNativeProfileCard(url, button);
    });

    const image = document.createElement('img');
    image.src = rawSource;
    image.alt = name;
    image.className = 'avatar-normal';
    image.loading = 'lazy';
    image.decoding = 'async';
    image.referrerPolicy = 'no-referrer';
    button.append(image);
    return button;
  }

  function installExpandedAvatarCardProxy(item) {
    if (!item.hasAttribute(REMOTE_ATTRIBUTE) && !item.hasAttribute(MIRROR_ATTRIBUTE)) {
      return;
    }
    if (state.profileBridgedItems.has(item)) {
      return;
    }

    const anchor = item.querySelector(
      ':scope > .nsk-content-meta-info .avatar-wrapper > a[href^="/space/"]',
    );
    const url = anchor ? parseSameOriginUrl(anchor.getAttribute('href') || '') : null;
    if (!isElementNode(anchor, 'a') || !url || !PROFILE_PATH_RE.test(url.pathname)) {
      return;
    }
    state.profileBridgedItems.add(item);

    anchor.addEventListener('click', (event) => {
      event.preventDefault();
      event.stopImmediatePropagation();
      showNativeProfileCard(url, anchor);
    }, true);
  }

  function createReplyTargetName(replyMetadata, targetItem) {
    if (targetItem) {
      return createProfileName(targetItem, replyMetadata.targetUser);
    }

    const url = parseSameOriginUrl(replyMetadata.memberAnchor.getAttribute('href') || '');
    if (!url || url.pathname !== '/member' || !url.searchParams.has('t')) {
      return createElement('span', PROFILE_NAME_CLASS, replyMetadata.targetUser);
    }

    const link = createElement('a', PROFILE_NAME_CLASS, replyMetadata.targetUser);
    link.classList.add('author-name');
    link.href = `${url.pathname}${url.search}`;
    link.rel = 'noopener noreferrer';
    link.title = replyMetadata.targetUser;
    return link;
  }

  function getTotalPages(postId, currentPage) {
    let totalPages = currentPage;
    const links = document.querySelectorAll('a.pager-pos[href], a.pager-next[href]');

    for (const link of links) {
      const url = parseSameOriginUrl(link.getAttribute('href') || '');
      const match = url ? POST_PATH_RE.exec(url.pathname) : null;
      if (!match || match[1] !== postId) {
        continue;
      }

      const page = parseSafePositiveInteger(match[2]);
      if (page !== null) {
        totalPages = Math.max(totalPages, page);
      }
    }

    return Math.min(totalPages, CONFIG.maxPagesPerPost);
  }

  function isSafeRemoteUrl(attributeName, rawValue) {
    if (rawValue.length > 4_096) {
      return false;
    }

    if (attributeName === 'src' && rawValue.startsWith('data:image/')) {
      return rawValue.length <= 262_144;
    }

    try {
      const url = new URL(rawValue, window.location.href);
      if (attributeName === 'href') {
        return ['http:', 'https:', 'mailto:'].includes(url.protocol);
      }
      return ['http:', 'https:'].includes(url.protocol);
    } catch {
      return false;
    }
  }

  function sanitizeRemoteItem(sourceItem, sourcePage) {
    const imported = document.importNode(sourceItem, true);
    const floor = getFloor(imported);
    if (floor === null) {
      return null;
    }

    imported.setAttribute(REMOTE_ATTRIBUTE, 'true');
    imported.setAttribute(SOURCE_PAGE_ATTRIBUTE, String(sourcePage));
    imported.querySelectorAll(DANGEROUS_REMOTE_ELEMENTS).forEach((element) => element.remove());
    imported.querySelectorAll('[id]').forEach((element) => element.removeAttribute('id'));

    for (const element of imported.querySelectorAll('*')) {
      for (const attribute of Array.from(element.attributes)) {
        const name = attribute.name.toLowerCase();
        if (
          name.startsWith('on')
          || ['style', 'srcdoc', 'srcset', 'formaction', 'contenteditable'].includes(name)
        ) {
          element.removeAttribute(attribute.name);
          continue;
        }

        if (['href', 'src', 'poster'].includes(name) && !isSafeRemoteUrl(name, attribute.value)) {
          element.removeAttribute(attribute.name);
        }
      }

      if (element instanceof HTMLAnchorElement && element.hasAttribute('href')) {
        element.rel = 'noopener noreferrer';
      }
      if (element instanceof HTMLImageElement) {
        element.loading = 'lazy';
        element.decoding = 'async';
        element.referrerPolicy = 'no-referrer';
      }
    }

    return { floor, item: imported };
  }

  function setNativeLoadStatus(status) {
    const toggle = document.getElementById(TOGGLE_ID);
    if (toggle) {
      toggle.setAttribute(`data-${PREFIX}-native-status`, status);
    }
  }

  function destroyNativePages() {
    for (const nativePage of state.nativePages.values()) {
      nativePage.frame?.remove();
    }
    state.nativePages.clear();
    state.hydratedRemoteItems.clear();
    setNativeLoadStatus('idle');
  }

  function waitForNativePage(frame, postInfo, page, scanGeneration) {
    const startedAt = Date.now();

    return new Promise((resolve) => {
      const inspect = () => {
        if (
          !state.enabled
          || scanGeneration !== state.scanGeneration
          || !frame.isConnected
          || Date.now() - startedAt > CONFIG.nativePageTimeoutMs
        ) {
          resolve(null);
          return;
        }

        try {
          const frameWindow = frame.contentWindow;
          const frameDocument = frame.contentDocument;
          const pathMatch = frameWindow ? POST_PATH_RE.exec(frameWindow.location.pathname) : null;
          const allItems = frameDocument
            ? Array.from(frameDocument.querySelectorAll('.content-item'))
            : [];
          const comments = frameDocument
            ? Array.from(
              frameDocument.querySelectorAll(
                '.comment-container > ul.comments > .content-item[id]',
              ),
            )
            : [];
          const config = frameWindow?.__config__;

          if (
            pathMatch
            && pathMatch[1] === postInfo.postId
            && parseSafePositiveInteger(pathMatch[2]) === page
            && comments.length > 0
            && comments.every((item) => item.querySelector(':scope > .comment-menu'))
            && config?.postData
            && String(config.postData.postId) === postInfo.postId
          ) {
            const items = new Map();
            const indexByFloor = new Map();
            allItems.forEach((item, index) => {
              const floor = getFloor(item);
              if (floor !== null) {
                items.set(floor, item);
                indexByFloor.set(floor, index);
              }
            });

            try {
              if (typeof window.mscAlert === 'function') {
                frameWindow.mscAlert = window.mscAlert;
              }
              if (typeof window.mscConfirm === 'function') {
                frameWindow.mscConfirm = window.mscConfirm;
              }
              if (typeof window.mscPrompt === 'function') {
                frameWindow.mscPrompt = window.mscPrompt;
              }
            } catch {
              // Native actions still work; only their dialogs may remain inside the frame.
            }

            resolve({
              frame,
              frameWindow,
              items,
              indexByFloor,
              page,
            });
            return;
          }
        } catch {
          // The frame is not ready yet or did not stay on the allowed same-origin page.
        }

        window.setTimeout(inspect, 100);
      };

      inspect();
    });
  }

  function preloadNativePage(page) {
    const existing = state.nativePages.get(page);
    if (existing) {
      return existing.promise;
    }

    const postInfo = getCurrentPostInfo();
    if (
      !state.enabled
      || !postInfo
      || page === postInfo.page
      || page > CONFIG.maxPagesPerPost
    ) {
      return Promise.resolve(null);
    }

    const url = new URL(`/post-${postInfo.postId}-${page}`, window.location.origin);
    const pathMatch = POST_PATH_RE.exec(url.pathname);
    if (!pathMatch || pathMatch[1] !== postInfo.postId) {
      return Promise.resolve(null);
    }

    const frame = document.createElement('iframe');
    frame.className = NATIVE_FRAME_CLASS;
    frame.title = `NodeSeek 第 ${page} 页原生评论预加载`;
    frame.setAttribute('aria-hidden', 'true');
    frame.setAttribute('sandbox', 'allow-scripts allow-same-origin');
    frame.referrerPolicy = 'same-origin';
    frame.src = url.href;

    const scanGeneration = state.scanGeneration;
    const record = { frame, promise: null };
    record.promise = new Promise((resolve) => {
      let settled = false;
      const finish = (nativePage) => {
        if (settled) {
          return;
        }
        settled = true;
        if (!nativePage) {
          frame.remove();
          state.nativePages.delete(page);
          setNativeLoadStatus('failed');
        } else {
          Object.assign(record, nativePage);
          setNativeLoadStatus('ready');
        }
        resolve(nativePage);
      };

      frame.addEventListener('load', () => {
        void waitForNativePage(frame, postInfo, page, scanGeneration).then(finish);
      }, { once: true });
      frame.addEventListener('error', () => finish(null), { once: true });
      window.setTimeout(() => finish(null), CONFIG.nativePageTimeoutMs + 500);
    });

    state.nativePages.set(page, record);
    setNativeLoadStatus(`loading-page-${page}`);
    (document.body || document.documentElement).append(frame);
    return record.promise;
  }

  function withTemporaryPageConfig(config, callback) {
    if (!config || typeof callback !== 'function') {
      return false;
    }

    const hadOwnConfig = Object.prototype.hasOwnProperty.call(window, '__config__');
    const previousConfig = window.__config__;
    try {
      window.__config__ = config;
      callback();
      return true;
    } catch {
      return false;
    } finally {
      if (hadOwnConfig) {
        window.__config__ = previousConfig;
      } else {
        Reflect.deleteProperty(window, '__config__');
      }
    }
  }

  function installRemoteNativeActionBridge(item, floor, page) {
    if (state.bridgedNativeItems.has(item)) {
      return;
    }
    state.bridgedNativeItems.add(item);

    item.addEventListener('click', (event) => {
      if (!isElementNode(event.target)) {
        return;
      }

      const menuItem = event.target.closest('.comment-menu > .menu-item');
      if (!isElementNode(menuItem) || !item.contains(menuItem)) {
        return;
      }

      const label = (menuItem.textContent || '').trim();
      const action = label === '回复' ? 'reply' : label === '引用' ? 'quote' : null;
      if (!action) {
        return;
      }

      const nativePage = state.nativePages.get(page);
      const sourceIndex = nativePage?.indexByFloor?.get(floor);
      const sourceConfig = nativePage?.frameWindow?.__config__;
      const editor = window.editor;
      if (
        !sourceConfig?.postData
        || !Number.isSafeInteger(sourceIndex)
        || !editor
        || typeof editor[action] !== 'function'
      ) {
        return;
      }

      event.preventDefault();
      event.stopImmediatePropagation();
      withTemporaryPageConfig(sourceConfig, () => editor[action](sourceIndex));
    }, true);
  }

  async function hydrateRemoteFloor(floor) {
    const existing = state.hydratedRemoteItems.get(floor);
    if (existing) {
      return true;
    }

    const template = state.remoteTemplates.get(floor);
    const page = parseSafePositiveInteger(
      template?.getAttribute(SOURCE_PAGE_ATTRIBUTE) || '',
    );
    if (!template || page === null) {
      return false;
    }

    const nativePage = await preloadNativePage(page);
    const sourceItem = nativePage?.items?.get(floor);
    // Elements created by the hidden source-page frame belong to that frame's realm. Validate
    // the node structurally so its descendants remain usable after adoptNode() moves the native
    // Vue-backed floor into this document.
    if (
      !isElementNode(sourceItem, 'li')
      || !sourceItem.querySelector(':scope > .comment-menu')
    ) {
      return false;
    }

    const nativeItem = document.adoptNode(sourceItem);
    nativeItem.setAttribute(REMOTE_ATTRIBUTE, 'true');
    nativeItem.setAttribute(SOURCE_PAGE_ATTRIBUTE, String(page));
    nativeItem.setAttribute(NATIVE_READY_ATTRIBUTE, 'true');
    installRemoteNativeActionBridge(nativeItem, floor, page);
    state.hydratedRemoteItems.set(floor, nativeItem);
    return true;
  }

  async function fetchPostPage(postId, page) {
    const url = new URL(`/post-${postId}-${page}`, window.location.origin);
    const pathMatch = POST_PATH_RE.exec(url.pathname);
    if (url.origin !== window.location.origin || !pathMatch || pathMatch[1] !== postId) {
      return [];
    }

    const result = await fetchSameOriginText(
      url,
      'text/html',
      'text/html',
      CONFIG.maxResponseBytes,
      true,
    );
    if (!result) {
      return [];
    }

    const responsePathMatch = POST_PATH_RE.exec(result.responseUrl.pathname);
    if (
      !responsePathMatch
      || responsePathMatch[1] !== postId
      || parseSafePositiveInteger(responsePathMatch[2]) !== page
    ) {
      return [];
    }

    const parsedDocument = new DOMParser().parseFromString(result.text, 'text/html');
    const commentList = parsedDocument.querySelector('.comment-container > ul.comments');
    if (!(commentList instanceof HTMLUListElement)) {
      return [];
    }

    return Array.from(commentList.children)
      .filter((item) => item instanceof HTMLElement && item.matches('.content-item[id]'))
      .slice(0, CONFIG.maxCommentsPerPage)
      .map((item) => sanitizeRemoteItem(item, page))
      .filter(Boolean);
  }

  async function scanOtherPages(postInfo) {
    if (!state.enabled || state.pageScanStarted || state.pageScanComplete) {
      return;
    }
    state.pageScanStarted = true;
    const scanGeneration = state.scanGeneration;

    try {
      const totalPages = getTotalPages(postInfo.postId, postInfo.page);
      if (totalPages <= 1) {
        state.pageScanComplete = true;
        finishInitialRender();
        return;
      }

      const pages = [];
      for (let page = 1; page <= totalPages; page += 1) {
        if (page !== postInfo.page) {
          pages.push(page);
        }
      }
      let cursor = 0;
      const worker = async () => {
        while (cursor < pages.length) {
          const page = pages[cursor];
          cursor += 1;
          if (!state.enabled || scanGeneration !== state.scanGeneration) {
            return;
          }

          const entries = await fetchPostPage(postInfo.postId, page);
          if (!state.enabled || scanGeneration !== state.scanGeneration) {
            return;
          }
          for (const { floor, item } of entries) {
            if (!state.remoteTemplates.has(floor)) {
              state.remoteTemplates.set(floor, item);
            }
          }
        }
      };
      const workerCount = Math.min(CONFIG.scanConcurrency, pages.length);
      await Promise.all(Array.from({ length: workerCount }, () => worker()));

      if (scanGeneration === state.scanGeneration) {
        state.pageScanComplete = true;
        finishInitialRender();
      }
    } finally {
      if (scanGeneration === state.scanGeneration) {
        state.pageScanStarted = false;
        if (state.enabled && !state.initialRevealComplete) {
          state.pageScanComplete = true;
          finishInitialRender();
        }
      }
    }
  }

  function getRequestedFloor() {
    const match = /^#([1-9]\d*)$/.exec(window.location.hash);
    return match ? parseSafePositiveInteger(match[1]) : null;
  }

  function findFloorTarget(floor) {
    const nested = state.commentList?.querySelector(
      `.${CHILD_CLASS}[${FLOOR_ATTRIBUTE}="${floor}"]`,
    );
    return isElementNode(nested) ? nested : document.getElementById(String(floor));
  }

  function revealFloor(floor, shouldScroll = true) {
    const target = findFloorTarget(floor);
    if (!isElementNode(target)) {
      return false;
    }

    let currentItem = target;
    while (currentItem) {
      currentItem.classList.remove(COLLAPSED_CLASS, SUPPRESSED_CLASS);
      const parentThread = currentItem.closest(`.${THREAD_CLASS}`);
      if (!parentThread) {
        break;
      }

      const rootFloor = parseSafePositiveInteger(parentThread.dataset.rootFloor || '');
      if (rootFloor !== null) {
        state.expandedThreads.add(rootFloor);
      }
      updateThreadVisibility(parentThread, true);
      currentItem = parentThread.parentElement?.closest('.content-item[id]') || null;
    }

    if (shouldScroll) {
      document.querySelectorAll(`.${HIGHLIGHT_CLASS}`)
        .forEach((item) => item.classList.remove(HIGHLIGHT_CLASS));
      target.classList.add(HIGHLIGHT_CLASS);
      window.requestAnimationFrame(() => {
        target.scrollIntoView({ behavior: 'smooth', block: 'center' });
      });
      window.setTimeout(() => target.classList.remove(HIGHLIGHT_CLASS), 1_600);
    }
    state.lastRevealedFloor = floor;
    return true;
  }

  function revealRequestedFloor() {
    const floor = getRequestedFloor();
    if (floor !== null) {
      revealFloor(floor, floor !== state.lastRevealedFloor);
    }
  }

  function handleFloorLinkClick(event) {
    if (!state.enabled || !isElementNode(event.target)) {
      return;
    }
    const anchor = event.target.closest('a[href]');
    if (!isElementNode(anchor, 'a')) {
      return;
    }

    const floorMatch = FLOOR_TEXT_RE.exec((anchor.textContent || '').trim());
    const url = parseSameOriginUrl(anchor.getAttribute('href') || '');
    const postInfo = getCurrentPostInfo();
    const pathMatch = url ? POST_PATH_RE.exec(url.pathname) : null;
    const floor = floorMatch ? parseSafePositiveInteger(floorMatch[1]) : null;
    if (
      floor === null
      || !url
      || !postInfo
      || !pathMatch
      || pathMatch[1] !== postInfo.postId
      || url.hash !== `#${floor}`
      || !findFloorTarget(floor)
    ) {
      return;
    }

    event.preventDefault();
    event.stopPropagation();
    state.lastRevealedFloor = null;
    window.history.pushState(null, '', `#${floor}`);
    revealFloor(floor, true);
  }

  function installFloorNavigation() {
    document.addEventListener('click', handleFloorLinkClick, true);
    window.addEventListener('hashchange', () => {
      state.lastRevealedFloor = null;
      revealRequestedFloor();
    });
  }

  function updateThreadVisibility(thread, expanded) {
    const children = Array.from(thread.querySelectorAll(`.${CHILD_CLASS}`));
    children.forEach((child, index) => {
      child.classList.toggle(
        COLLAPSED_CLASS,
        !expanded && index >= CONFIG.defaultVisibleReplies,
      );
    });

    const toggle = thread.querySelector(`:scope > .${THREAD_TOGGLE_CLASS}`);
    if (!(toggle instanceof HTMLButtonElement)) {
      return;
    }

    const hiddenCount = Math.max(0, children.length - CONFIG.defaultVisibleReplies);
    toggle.setAttribute('aria-expanded', String(expanded));
    toggle.textContent = expanded
      ? '收起回复'
      : `展开其余 ${hiddenCount} 条回复`;
  }

  function installTopLevelThreadControls(commentList) {
    const threads = Array.from(commentList.querySelectorAll(`.${THREAD_CLASS}`));
    for (const thread of threads) {
      if (thread.parentElement?.closest(`.${THREAD_CLASS}`)) {
        thread.querySelector(`:scope > .${SUMMARY_CLASS}`)?.remove();
        continue;
      }

      const rootFloor = parseSafePositiveInteger(thread.dataset.rootFloor || '');
      if (rootFloor === null) {
        continue;
      }

      const children = Array.from(thread.querySelectorAll(`.${CHILD_CLASS}`));
      const summary = thread.querySelector(`:scope > .${SUMMARY_CLASS}`);
      if (summary) {
        summary.textContent = `${children.length} 条回复`;
      }

      if (children.length > CONFIG.defaultVisibleReplies) {
        const list = thread.querySelector(`:scope > .${LIST_CLASS}`);
        const toggle = createElement('button', THREAD_TOGGLE_CLASS);
        toggle.type = 'button';
        if (list?.id) {
          toggle.setAttribute('aria-controls', list.id);
        }
        toggle.addEventListener('click', () => {
          if (state.expandedThreads.has(rootFloor)) {
            state.expandedThreads.delete(rootFloor);
          } else {
            state.expandedThreads.add(rootFloor);
          }
          updateThreadVisibility(thread, state.expandedThreads.has(rootFloor));
        });
        thread.append(toggle);
      }

      updateThreadVisibility(thread, state.expandedThreads.has(rootFloor));
    }
  }

  function applyDetailState(item, floor, detailToggle) {
    const expanded = state.expandedDetails.has(floor);
    item.classList.toggle(DETAIL_EXPANDED_CLASS, expanded);
    detailToggle.setAttribute('aria-expanded', String(expanded));
    detailToggle.textContent = expanded ? '收起详情' : '展开详情';
  }

  function installMirrorActionProxy(mirrorItem, originalItem) {
    const mirrorActions = Array.from(
      mirrorItem.querySelectorAll(':scope > .comment-menu > .menu-item'),
    );
    const originalActions = Array.from(
      originalItem.querySelectorAll(':scope > .comment-menu > .menu-item'),
    );
    if (mirrorActions.length === 0 || mirrorActions.length !== originalActions.length) {
      return;
    }

    const syncLabels = () => {
      mirrorActions.forEach((action, index) => {
        const mirrorLabel = action.querySelector('span');
        const originalLabel = originalActions[index]?.querySelector('span');
        if (mirrorLabel && originalLabel) {
          mirrorLabel.textContent = originalLabel.textContent;
        }
      });
    };

    mirrorActions.forEach((action, index) => {
      action.addEventListener('click', (event) => {
        event.preventDefault();
        event.stopPropagation();
        const originalAction = originalActions[index];
        if (!originalAction) {
          return;
        }
        originalAction.dispatchEvent(new MouseEvent('click', {
          bubbles: true,
          cancelable: true,
          view: window,
          clientX: event.clientX,
          clientY: event.clientY,
        }));
        window.setTimeout(syncLabels, 600);
        window.setTimeout(syncLabels, 1_500);
      });
    });
  }

  function decorateChild(entry, replyMetadata, entryByFloor) {
    const { item, floor, originalItem } = entry;
    item.classList.add(CHILD_CLASS);
    item.setAttribute(FLOOR_ATTRIBUTE, String(floor));
    replyMetadata.memberAnchor.classList.add(REPLY_MARKER_CLASS);
    replyMetadata.floorAnchor.classList.add(REPLY_MARKER_CLASS);

    const compactHeader = createElement('div', COMPACT_HEADER_CLASS);
    const relation = createElement('span', RELATION_CLASS);
    const floorLabel = createElement('a', FLOOR_LABEL_CLASS, `#${floor}`);
    floorLabel.href = `#${floor}`;
    floorLabel.title = `跳转到 #${floor}`;
    const avatar = createProfileAvatar(item);
    const authorName = createProfileName(item, getAuthorName(item));
    const targetEntry = entryByFloor.get(replyMetadata.targetFloor);
    const targetItem = targetEntry?.item;
    const targetAvatar = targetItem
      ? createProfileAvatar(targetItem)
      : null;
    const targetName = createReplyTargetName(replyMetadata, targetItem);

    relation.append(floorLabel);
    if (avatar) {
      relation.append(avatar);
    }
    relation.append(
      authorName,
      document.createTextNode(' 回复了 '),
    );
    if (targetAvatar) {
      relation.append(targetAvatar);
    }
    relation.append(targetName, document.createTextNode('：'));
    const detailToggle = createElement('button', DETAIL_TOGGLE_CLASS);
    detailToggle.type = 'button';
    detailToggle.addEventListener('click', async () => {
      if (state.expandedDetails.has(floor)) {
        state.expandedDetails.delete(floor);
        applyDetailState(item, floor, detailToggle);
        return;
      }

      if (item.hasAttribute(REMOTE_ATTRIBUTE) && !item.hasAttribute(NATIVE_READY_ATTRIBUTE)) {
        detailToggle.disabled = true;
        detailToggle.textContent = '正在加载原楼层…';
        let hydrated = false;
        try {
          hydrated = await hydrateRemoteFloor(floor);
        } catch {
          hydrated = false;
        }
        detailToggle.disabled = false;
        if (!hydrated) {
          detailToggle.textContent = '加载失败，点击重试';
          return;
        }

        state.expandedDetails.add(floor);
        renderNestedReplies();
        return;
      }

      state.expandedDetails.add(floor);
      applyDetailState(item, floor, detailToggle);
    });
    compactHeader.append(relation, detailToggle);
    item.prepend(compactHeader);

    if (originalItem) {
      installMirrorActionProxy(item, originalItem);
    }
    installExpandedAvatarCardProxy(item);

    applyDetailState(item, floor, detailToggle);
  }

  function createThread(rootFloor, childEntries, metadataByFloor, entryByFloor) {
    const thread = createElement('section', THREAD_CLASS);
    thread.setAttribute('aria-label', `楼层 ${rootFloor} 的楼中楼回复`);
    thread.dataset.rootFloor = String(rootFloor);

    const summary = createElement('div', SUMMARY_CLASS, `${childEntries.length} 条回复`);
    const nestedList = createElement('ul', LIST_CLASS);
    const listId = `${PREFIX}-list-${rootFloor}`;
    nestedList.id = listId;

    const children = [];
    for (const entry of childEntries) {
      const metadata = entry.metadata || metadataByFloor.get(entry.floor);
      if (!metadata) {
        continue;
      }
      cleanupLocalItem(entry.item);
      decorateChild(entry, metadata, entryByFloor);
      nestedList.append(entry.item);
      children.push(entry.item);
    }

    if (children.length === 0) {
      return null;
    }

    thread.append(summary, nestedList);
    return thread;
  }

  function cleanupLocalItem(item) {
    item.classList.remove(
      CHILD_CLASS,
      COLLAPSED_CLASS,
      DETAIL_EXPANDED_CLASS,
      SUPPRESSED_CLASS,
      HIGHLIGHT_CLASS,
    );
    item.removeAttribute(FLOOR_ATTRIBUTE);
    item.querySelectorAll(`:scope > .${COMPACT_HEADER_CLASS}`)
      .forEach((element) => element.remove());
    item.querySelectorAll(`.${REPLY_MARKER_CLASS}`)
      .forEach((element) => element.classList.remove(REPLY_MARKER_CLASS));
  }

  function restoreLocalItems(commentList) {
    commentList.querySelectorAll(`[${REMOTE_ATTRIBUTE}]`).forEach((item) => item.remove());

    const discoveredItems = Array.from(commentList.querySelectorAll('.content-item[id]'))
      .filter((item) => item instanceof HTMLElement && !item.hasAttribute(REMOTE_ATTRIBUTE));
    const discoveredSet = new Set(discoveredItems);
    const orderedItems = state.originalLocalItems.filter((item) => discoveredSet.has(item));
    for (const item of discoveredItems) {
      if (!orderedItems.includes(item)) {
        orderedItems.push(item);
        state.originalLocalItems.push(item);
      }
    }

    for (const item of orderedItems) {
      cleanupLocalItem(item);
      commentList.append(item);
    }

    const localEntries = orderedItems
      .map((item) => ({
        item,
        floor: getFloor(item),
        source: 'local',
        pinned: isPinnedItem(item),
      }))
      .filter(({ floor }) => floor !== null);
    commentList.querySelectorAll(`.${THREAD_CLASS}`).forEach((thread) => thread.remove());
    return localEntries;
  }

  function resolveEntryPlacement(entry, targetByFloor, entryByFloor, currentPage) {
    const visited = new Set([entry.floor]);
    let target = targetByFloor.get(entry.floor);
    let reachesEarlierPage = false;

    while (target) {
      if (visited.has(target)) {
        return null;
      }
      visited.add(target);

      const targetEntry = entryByFloor.get(target);
      if (!targetEntry) {
        break;
      }
      if (targetEntry.source === 'local') {
        if (targetEntry.pinned) {
          return null;
        }
        return {
          rootFloor: target,
          suppress: false,
          mirror: entry.source === 'local' && entry.pinned,
        };
      }

      const sourcePage = parseSafePositiveInteger(
        targetEntry.item.getAttribute(SOURCE_PAGE_ATTRIBUTE) || '',
      );
      if (sourcePage !== null && sourcePage < currentPage) {
        reachesEarlierPage = true;
      }
      target = targetByFloor.get(target);
    }

    return entry.source === 'local' && !entry.pinned && reachesEarlierPage
      ? { rootFloor: null, suppress: true }
      : null;
  }

  function renderNestedReplies() {
    const commentList = state.commentList;
    const postInfo = getCurrentPostInfo();
    if (!state.enabled || !commentList?.isConnected || !postInfo) {
      return;
    }

    state.listObserver?.disconnect();

    try {
      const localEntries = restoreLocalItems(commentList);
      if (localEntries.length === 0 || localEntries.length > CONFIG.maxCommentsPerPage) {
        return;
      }

      const entryByFloor = new Map(localEntries.map((entry) => [entry.floor, entry]));
      for (const [floor, template] of state.remoteTemplates) {
        if (!entryByFloor.has(floor)) {
          entryByFloor.set(floor, {
            floor,
            item: state.hydratedRemoteItems.get(floor) || template.cloneNode(true),
            source: 'remote',
          });
        }
      }

      const allEntries = Array.from(entryByFloor.values()).sort((a, b) => a.floor - b.floor);
      const targetByFloor = new Map();
      const metadataByFloor = new Map();

      for (const entry of allEntries) {
        const metadata = getReplyMetadata(entry.item, postInfo.postId);
        if (metadata && metadata.targetFloor !== entry.floor) {
          targetByFloor.set(entry.floor, metadata.targetFloor);
          metadataByFloor.set(entry.floor, metadata);
        }
      }

      const childrenByRoot = new Map();
      for (const entry of allEntries) {
        const placement = resolveEntryPlacement(
          entry,
          targetByFloor,
          entryByFloor,
          postInfo.page,
        );
        if (!placement) {
          continue;
        }

        if (placement.suppress) {
          entry.item.classList.add(SUPPRESSED_CLASS);
          continue;
        }

        const { rootFloor } = placement;
        if (rootFloor === null) {
          continue;
        }

        const rootEntry = entryByFloor.get(rootFloor);
        if (!rootEntry || rootEntry.source !== 'local' || rootEntry.pinned) {
          continue;
        }

        let childEntry = entry;
        if (placement.mirror) {
          const mirrorItem = entry.item.cloneNode(true);
          mirrorItem.removeAttribute('id');
          mirrorItem.setAttribute(MIRROR_ATTRIBUTE, 'true');
          mirrorItem.querySelectorAll('[id]').forEach((element) => element.removeAttribute('id'));
          const mirrorMetadata = getReplyMetadata(mirrorItem, postInfo.postId);
          if (!mirrorMetadata) {
            continue;
          }
          childEntry = {
            ...entry,
            item: mirrorItem,
            source: 'mirror',
            pinned: false,
            originalItem: entry.item,
            metadata: mirrorMetadata,
          };
        }

        const children = childrenByRoot.get(rootFloor) || [];
        children.push(childEntry);
        childrenByRoot.set(rootFloor, children);
      }

      for (const [rootFloor, childEntries] of childrenByRoot) {
        const rootEntry = entryByFloor.get(rootFloor);
        if (!rootEntry || rootEntry.source !== 'local' || rootEntry.pinned) {
          continue;
        }

        const thread = createThread(rootFloor, childEntries, metadataByFloor, entryByFloor);
        if (thread) {
          rootEntry.item.append(thread);
        }
      }
      installTopLevelThreadControls(commentList);
      revealRequestedFloor();
    } finally {
      state.listObserver?.observe(commentList, { childList: true });
    }
  }

  function finishInitialRender() {
    try {
      renderNestedReplies();
    } finally {
      revealFinalView();
    }
  }

  function scheduleRender() {
    if (
      !state.enabled
      || (!state.pageScanComplete && !state.initialRevealComplete)
      || state.renderTimer !== null
    ) {
      return;
    }

    state.renderTimer = window.setTimeout(() => {
      state.renderTimer = null;
      renderNestedReplies();
    }, CONFIG.renderDelayMs);
  }

  function restoreOriginalView() {
    const commentList = state.commentList;
    if (!commentList?.isConnected) {
      return;
    }

    state.listObserver?.disconnect();
    if (state.renderTimer !== null) {
      window.clearTimeout(state.renderTimer);
      state.renderTimer = null;
    }
    restoreLocalItems(commentList);
    state.listObserver?.observe(commentList, { childList: true });
    revealFinalView();
  }

  function updateToggleControl() {
    const toggle = document.getElementById(TOGGLE_ID);
    if (!(toggle instanceof HTMLButtonElement)) {
      return;
    }

    toggle.classList.toggle(`${PREFIX}__toggle-enabled`, state.enabled);
    toggle.setAttribute('aria-pressed', String(state.enabled));
    toggle.setAttribute(
      'aria-label',
      state.enabled ? '关闭楼中楼并恢复原始楼层' : '开启楼中楼',
    );
    toggle.title = state.enabled ? '关闭楼中楼' : '开启楼中楼';
  }

  function setEnabled(enabled) {
    state.enabled = enabled;
    writeEnabledPreference(enabled);
    updateToggleControl();

    if (!state.commentList) {
      return;
    }
    if (!enabled) {
      destroyNativePages();
      restoreOriginalView();
      return;
    }

    state.initialRevealComplete = false;
    beginInitialMask();
    showLoadingIndicator(state.commentList);
    if (state.pageScanComplete) {
      finishInitialRender();
      return;
    }

    const postInfo = getCurrentPostInfo();
    if (postInfo) {
      if (document.readyState === 'loading') {
        window.addEventListener('DOMContentLoaded', () => {
          if (state.enabled) {
            void scanOtherPages(postInfo);
          }
        }, { once: true });
      } else {
        void scanOtherPages(postInfo);
      }
    }
  }

  function installToggle() {
    const themeToggle = document.querySelector('#nsk-head > .color-theme-switcher');
    if (!(themeToggle instanceof HTMLElement) || !themeToggle.parentElement) {
      return false;
    }

    let toggle = document.getElementById(TOGGLE_ID);
    if (!(toggle instanceof HTMLButtonElement)) {
      toggle = createElement('button', `${PREFIX}__toggle`, '楼');
      toggle.id = TOGGLE_ID;
      toggle.type = 'button';
      toggle.addEventListener('click', () => setEnabled(!state.enabled));
    }
    toggle.setAttribute(`data-${PREFIX}-version`, SCRIPT_VERSION);
    themeToggle.insertAdjacentElement('beforebegin', toggle);
    updateToggleControl();
    return true;
  }

  function attachToCommentList(commentList) {
    const postInfo = getCurrentPostInfo();
    const viewKey = postInfo ? `${postInfo.postId}:${postInfo.page}` : '';
    const viewChanged = viewKey !== state.viewKey;
    if (state.commentList === commentList && !viewChanged) {
      if (state.pageScanComplete) {
        scheduleRender();
      }
      return;
    }

    state.listObserver?.disconnect();
    if (viewChanged) {
      destroyNativePages();
      state.viewKey = viewKey;
      state.scanGeneration += 1;
      state.pageScanStarted = false;
      state.pageScanComplete = false;
      state.remoteTemplates.clear();
      state.hydratedRemoteItems.clear();
      state.bridgedNativeItems = new WeakSet();
      state.profileBridgedItems = new WeakSet();
      state.expandedThreads.clear();
      state.expandedDetails.clear();
      state.lastRevealedFloor = null;
      state.initialRevealComplete = false;
    }
    state.commentList = commentList;
    state.originalLocalItems = Array.from(commentList.children)
      .filter((item) => item instanceof HTMLElement && item.matches('.content-item[id]'));
    state.listObserver = new MutationObserver(scheduleRender);
    state.listObserver.observe(commentList, { childList: true });
    if (!state.enabled) {
      revealFinalView();
      return;
    }

    beginInitialMask();
    showLoadingIndicator(commentList);

    if (postInfo) {
      if (document.readyState === 'loading') {
        window.addEventListener('DOMContentLoaded', () => {
          if (state.commentList === commentList && state.enabled) {
            void scanOtherPages(postInfo);
          }
        }, { once: true });
      } else {
        void scanOtherPages(postInfo);
      }
    }
  }

  function discoverCommentList() {
    const commentList = document.querySelector('.comment-container > ul.comments');
    if (!(commentList instanceof HTMLUListElement)) {
      return false;
    }

    attachToCommentList(commentList);
    return true;
  }

  function discoverInterfaces() {
    const commentsReady = discoverCommentList();
    const toggleReady = installToggle();
    if (!commentsReady || !toggleReady) {
      return false;
    }

    state.discoveryObserver?.disconnect();
    state.discoveryObserver = null;
    if (state.discoveryTimer !== null) {
      window.clearTimeout(state.discoveryTimer);
      state.discoveryTimer = null;
    }
    return true;
  }

  function installStyles() {
    if (document.getElementById(STYLE_ID)) {
      return;
    }

    const style = document.createElement('style');
    style.id = STYLE_ID;
    style.textContent = `
      .${PREFIX}__loading {
        box-sizing: border-box;
        margin: 8px 0;
        padding: 12px;
        border-radius: 6px;
        color: inherit;
        background: rgba(127, 127, 127, 0.08);
        text-align: center;
        opacity: 0.72;
      }

      .${NATIVE_FRAME_CLASS} {
        position: fixed !important;
        top: 0 !important;
        left: -100000px !important;
        width: 1024px !important;
        height: 768px !important;
        border: 0 !important;
        opacity: 0 !important;
        pointer-events: none !important;
      }

      .${THREAD_CLASS} {
        margin: 7px 0 1px 34px;
        padding: 4px 8px;
        border-left: 2px solid rgba(127, 127, 127, 0.35);
        border-radius: 0 6px 6px 0;
        background: rgba(127, 127, 127, 0.045);
      }

      .${THREAD_CLASS} .${THREAD_CLASS} {
        margin-left: 16px;
        background: rgba(127, 127, 127, 0.035);
      }

      .${SUMMARY_CLASS} {
        margin: 0 0 1px;
        font-size: 0.75rem;
        font-weight: 600;
        line-height: 1.35;
        opacity: 0.62;
      }

      .${LIST_CLASS} {
        margin: 0;
        padding: 0;
        list-style: none;
      }

      .${THREAD_CLASS} .${CHILD_CLASS} {
        margin: 0;
        padding: 6px 0;
        border: 0;
        border-bottom: 1px solid rgba(127, 127, 127, 0.16);
        background: transparent;
      }

      .${THREAD_CLASS} .${CHILD_CLASS}:last-child {
        border-bottom: 0;
      }

      .${COMPACT_HEADER_CLASS} {
        display: flex;
        align-items: center;
        gap: 8px;
        min-width: 0;
        margin: 0 0 2px;
        font-size: 0.82rem;
        line-height: 1.35;
      }

      .${RELATION_CLASS} {
        display: inline-flex;
        align-items: center;
        gap: 4px;
        min-width: 0;
        overflow-wrap: anywhere;
        font-weight: 600;
      }

      .${FLOOR_LABEL_CLASS} {
        flex: 0 0 auto;
        color: inherit;
        text-decoration: none;
        opacity: 0.68;
      }

      .${FLOOR_LABEL_CLASS}:hover {
        text-decoration: underline;
      }

      .${PROFILE_AVATAR_CLASS} {
        appearance: none;
        display: inline-flex;
        flex: 0 0 auto;
        width: 18px;
        height: 18px;
        margin: 0;
        padding: 0;
        border: 0;
        border-radius: 50%;
        overflow: hidden;
        background: transparent;
        cursor: pointer;
      }

      .${PROFILE_AVATAR_CLASS} > img {
        display: block;
        width: 100%;
        height: 100%;
        object-fit: cover;
      }

      .${PROFILE_NAME_CLASS} {
        color: inherit;
        font-weight: 600;
        text-decoration: none;
      }

      a.${PROFILE_NAME_CLASS}:hover,
      .${PROFILE_AVATAR_CLASS}:hover + a.${PROFILE_NAME_CLASS} {
        text-decoration: underline;
      }

      .${DETAIL_TOGGLE_CLASS},
      .${THREAD_TOGGLE_CLASS} {
        appearance: none;
        border: 0;
        padding: 0;
        color: inherit;
        background: transparent;
        font: inherit;
        text-decoration: underline;
        text-decoration-style: dotted;
        text-underline-offset: 2px;
        opacity: 0.66;
        cursor: pointer;
      }

      .${DETAIL_TOGGLE_CLASS} {
        flex: 0 0 auto;
        margin-left: auto;
        font-size: 0.75rem;
      }

      .${THREAD_TOGGLE_CLASS} {
        display: block;
        margin: 4px auto 1px;
        font-size: 0.8rem;
      }

      .${DETAIL_TOGGLE_CLASS}:hover,
      .${THREAD_TOGGLE_CLASS}:hover {
        opacity: 1;
      }

      .${DETAIL_TOGGLE_CLASS}:focus-visible,
      .${THREAD_TOGGLE_CLASS}:focus-visible {
        outline: 2px solid currentColor;
        outline-offset: 2px;
      }

      .${THREAD_CLASS} .${CHILD_CLASS} > article.post-content,
      .${THREAD_CLASS} .${CHILD_CLASS} > article.post-content > p {
        margin-top: 2px;
        margin-bottom: 2px;
      }

      .${THREAD_CLASS} .${CHILD_CLASS}:not(.${DETAIL_EXPANDED_CLASS})
        > .nsk-content-meta-info,
      .${THREAD_CLASS} .${CHILD_CLASS}:not(.${DETAIL_EXPANDED_CLASS})
        > .signature,
      .${THREAD_CLASS} .${CHILD_CLASS}:not(.${DETAIL_EXPANDED_CLASS})
        > .comment-menu,
      .${THREAD_CLASS} .${CHILD_CLASS}:not(.${DETAIL_EXPANDED_CLASS})
        > .comment-menu-mount {
        display: none !important;
      }

      .${THREAD_CLASS} .${CHILD_CLASS}
        > .nsk-content-meta-info .floor-link-wrapper,
      .${REPLY_MARKER_CLASS} {
        display: none !important;
      }

      .${COLLAPSED_CLASS},
      .${SUPPRESSED_CLASS} {
        display: none !important;
      }

      .${HIGHLIGHT_CLASS} {
        animation: ${PREFIX}-highlight 1.6s ease-out;
      }

      @keyframes ${PREFIX}-highlight {
        0%, 35% { background: rgba(255, 205, 64, 0.24); }
        100% { background: transparent; }
      }

      .${PREFIX}__toggle {
        display: inline-flex;
        flex: 0 0 auto;
        align-items: center;
        justify-content: center;
        box-sizing: border-box;
        width: 27px;
        height: 20px;
        margin: 0 3px 0 0;
        padding: 0;
        border: 0;
        border-radius: 4px;
        color: inherit;
        background: transparent;
        font: 600 12px/1 system-ui, sans-serif;
        opacity: 0.66;
        cursor: pointer;
        vertical-align: middle;
      }

      .${PREFIX}__toggle:hover,
      .${PREFIX}__toggle:focus-visible {
        opacity: 1;
      }

      .${PREFIX}__toggle:focus-visible {
        outline: 2px solid currentColor;
        outline-offset: 2px;
      }

      .${PREFIX}__toggle-enabled {
        background: rgba(127, 127, 127, 0.16);
        opacity: 0.92;
      }

      @media (max-width: 640px) {
        .${THREAD_CLASS} {
          margin-left: 10px;
          padding: 4px 6px;
        }

        .${THREAD_CLASS} .${THREAD_CLASS} {
          margin-left: 8px;
        }
      }
    `;
    (document.head || document.documentElement).append(style);
  }

  function init() {
    if (!getCurrentPostInfo()) {
      revealFinalView();
      return;
    }

    state.enabled = readEnabledPreference();
    if (state.enabled) {
      beginInitialMask();
    }
    installStyles();
    installFloorNavigation();
    if (discoverInterfaces()) {
      return;
    }

    state.discoveryObserver = new MutationObserver(discoverInterfaces);
    state.discoveryObserver.observe(document.documentElement, {
      childList: true,
      subtree: true,
    });

    state.discoveryTimer = window.setTimeout(() => {
      state.discoveryObserver?.disconnect();
      state.discoveryObserver = null;
      state.discoveryTimer = null;
      revealFinalView();
    }, 15_000);
  }

  function start() {
    if (!document.documentElement) {
      window.setTimeout(start, 0);
      return;
    }
    init();
  }

  start();
})();
