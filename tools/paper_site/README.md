# Web edition of the non-MF paper

`build.py` assembles a single self-contained page at `/paper/` on the Pages
site from three inputs, none of which live here: `non_mf_groups_exist.tex`
(embedded raw and typeset in the browser by `parser.js` + `ui.js` with the
inlined KaTeX under `katex/`), `docs/NON_MF_NUMBERED_CLAIMS.json` (Lean
badges, the claim explorer, and the dependency graph), and nothing else — so
a tex or manifest push republishes the page with no edits here.

The renderer covers exactly this manuscript's command set.  A construct it
does not know is not dropped silently: the page logs it to the console and
`window.__diag` collects every warning and KaTeX parse error, so check that
after adding new TeX constructs.  The cairn-site workflow builds this page
non-fatally — a failure here warns and publishes the rest of the site.

The one TikZ figure is hand-mirrored in `ui.js` (`renderFigure`); if the
figure in the tex changes, that function must follow by hand.
