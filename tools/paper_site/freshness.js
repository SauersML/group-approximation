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
          return;
        }
        const target = root + 'v/' + encodeURIComponent(current) + '/' + location.search + location.hash;
        location.replace(target);
      })
      .catch(() => {
        checking = false;
        html.classList.remove('freshness-check');
        html.classList.add('freshness-error');
      });
  }

  check();
  addEventListener('pagehide', () => html.classList.add('freshness-check'));
  addEventListener('pageshow', ev => { if (ev.persisted) check(); });
  document.addEventListener('visibilitychange', () => {
    if (document.visibilityState === 'visible') check();
  });
})();
