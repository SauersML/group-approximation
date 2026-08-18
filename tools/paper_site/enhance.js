(() => {
  'use strict';

  function whenReady(fn) {
    const tick = () => document.querySelector('.toc') ? fn() : setTimeout(tick, 16);
    if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', tick, { once: true });
    else tick();
  }

  whenReady(() => {
    const body = document.body;
    const tabs = [...document.querySelectorAll('.tab')].filter(t => t.dataset.view);
    const tablist = document.querySelector('.tabs');
    const proofToggle = document.getElementById('proof-toggle');
    const tocToggle = document.getElementById('toc-toggle');
    const tocScrim = document.getElementById('toc-scrim');
    const sidebar = document.getElementById('paper-sidebar');
    const positions = { paper: window.scrollY, claims: 0, graph: 0 };

    function syncTabs(active) {
      tabs.forEach(tab => {
        const on = tab.dataset.view === active;
        tab.setAttribute('aria-selected', String(on));
        tab.tabIndex = on ? 0 : -1;
      });
    }

    tablist.addEventListener('click', ev => {
      const tab = ev.target.closest('.tab');
      if (!tab || !tab.dataset.view) return;
      const current = body.dataset.view || 'paper';
      const next = tab.dataset.view;
      if (ev.isTrusted && current !== next) {
        positions[current] = window.scrollY;
        requestAnimationFrame(() => window.scrollTo({ top: positions[next] || 0, behavior: 'auto' }));
      }
      syncTabs(next);
      closeToc();
    }, true);

    tablist.addEventListener('keydown', ev => {
      if (!['ArrowLeft', 'ArrowRight', 'Home', 'End'].includes(ev.key)) return;
      ev.preventDefault();
      const i = tabs.indexOf(document.activeElement);
      let next = i;
      if (ev.key === 'ArrowLeft') next = (i - 1 + tabs.length) % tabs.length;
      if (ev.key === 'ArrowRight') next = (i + 1) % tabs.length;
      if (ev.key === 'Home') next = 0;
      if (ev.key === 'End') next = tabs.length - 1;
      const current = body.dataset.view || 'paper';
      positions[current] = window.scrollY;
      tabs[next].focus();
      tabs[next].click();
      requestAnimationFrame(() => window.scrollTo({ top: positions[tabs[next].dataset.view] || 0, behavior: 'auto' }));
    });

    const proofs = [...document.querySelectorAll('details.proof')];
    if (!proofs.length) proofToggle.hidden = true;

    function setProofMode(compact, persist) {
      proofs.forEach(proof => { proof.open = !compact; });
      proofToggle.textContent = compact ? 'Show proofs' : 'Hide proofs';
      proofToggle.setAttribute('aria-pressed', String(compact));
      if (persist) {
        try { localStorage.setItem('paper-proof-mode', compact ? 'compact' : 'full'); } catch (_) {}
      }
    }

    // proofs start folded so the paper reads as statements first; a reader
    // who opts into full proofs keeps that choice across visits
    let compact = true;
    try { if (localStorage.getItem('paper-proof-mode') === 'full') compact = false; } catch (_) {}
    setProofMode(compact, false);
    proofToggle.addEventListener('click', () => {
      compact = !compact;
      setProofMode(compact, true);
    });

    function openToc() {
      body.classList.add('toc-open');
      tocToggle.setAttribute('aria-expanded', 'true');
      tocScrim.hidden = false;
      const first = sidebar.querySelector('a');
      if (first) first.focus();
    }
    function closeToc() {
      body.classList.remove('toc-open');
      tocToggle.setAttribute('aria-expanded', 'false');
      tocScrim.hidden = true;
    }
    tocToggle.addEventListener('click', () => body.classList.contains('toc-open') ? closeToc() : openToc());
    tocScrim.addEventListener('click', closeToc);
    sidebar.addEventListener('click', ev => { if (ev.target.closest('a')) closeToc(); });
    document.addEventListener('keydown', ev => {
      if (ev.key === 'Escape' && body.classList.contains('toc-open')) {
        closeToc();
        tocToggle.focus();
      }
    });

    document.addEventListener('focusin', ev => {
      const ref = ev.target.closest && ev.target.closest('.xref, .cite');
      if (ref) ref.dispatchEvent(new MouseEvent('mouseover', { bubbles: true }));
    });
    document.addEventListener('focusout', ev => {
      const ref = ev.target.closest && ev.target.closest('.xref, .cite');
      if (ref) ref.dispatchEvent(new MouseEvent('mouseout', { bubbles: true }));
    });

    syncTabs(body.dataset.view || 'paper');
  });
})();
