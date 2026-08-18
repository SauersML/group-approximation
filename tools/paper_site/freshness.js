(() => {
  'use strict';
  const BUILD_ID = /*__BUILD_ID_JSON__*/;
  if (!/^[0-9a-f]{7,64}$/i.test(BUILD_ID)) return;

  const match = location.pathname.match(/^(.*\/paper\/)/);
  if (!match) return;

  const root = match[1];
  const html = document.documentElement;
  let checking = false;

  function check() {
    if (checking) return;
    checking = true;
    html.classList.remove('freshness-error');
    html.classList.add('freshness-check');

    fetch(root + 'version.json?_=' + Date.now(), { cache: 'no-store' })
      .then(r => r.ok ? r.json() : Promise.reject(new Error('version check failed')))
      .then(meta => {
        const current = String(meta.version || '');
        if (!/^[0-9a-f]{7,64}$/i.test(current)) throw new Error('invalid version');
        if (current === BUILD_ID) {
          checking = false;
          html.classList.remove('freshness-check');
          // fresh: canonicalize a leftover cache-bust query so the address
          // bar always shows the stable /paper/ URL (fragment kept)
          if (location.search.indexOf('?v=') === 0 && location.pathname.slice(-root.length) === root) {
            history.replaceState(null, '', root + location.hash);
          }
          return;
        }
        // Stale copy.  Reload the canonical page with a cache-busting query
        // so the address bar keeps the stable, shareable /paper/ URL; the
        // fragment survives.  If that exact query is already in the URL the
        // cache ignored it, so fall back to the immutable snapshot path.
        const q = '?v=' + encodeURIComponent(current);
        if (location.search === q) {
          location.replace(root + 'v/' + encodeURIComponent(current) + '/' + location.hash);
        } else {
          location.replace(root + q + location.hash);
        }
      })
      .catch(() => {
        // could not verify: show what we have rather than a blank page
        checking = false;
        html.classList.remove('freshness-check');
        html.classList.add('freshness-error');
        try { console.warn('[paper] freshness check failed; showing the loaded copy'); } catch (_) {}
      });
  }

  check();
  addEventListener('pagehide', () => html.classList.add('freshness-check'));
  addEventListener('pageshow', ev => { if (ev.persisted) check(); });
  document.addEventListener('visibilitychange', () => {
    if (document.visibilityState === 'visible') check();
  });
})();
