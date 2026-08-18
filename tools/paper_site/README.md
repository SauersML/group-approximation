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

`build.py` also embeds the full Lean source of every declaration the
manifest or an in-tex `\leanverified` marker names — statement and proof,
split at the top-level `:=`, with the source line for a GitHub deep link.
On the page: Lean badges (on theorem heads and on every Proof line whose
statement is formalized) open a fixed side drawer — statement and proof
shown together, the manuscript never reflows.  A `\leanverified` marker in
running text renders as a chip at that exact spot, and identifiers inside
drawer code expand the declaration they name (statements of every decl in
the cited modules are embedded for this).  Manuscript proofs
start folded behind the topbar toggle, and cross-reference hover cards
stack, so a link inside a card opens a nested card instead of replacing
it.  `freshness.js` keeps the address bar
on the canonical `/paper/` URL: a stale cached copy reloads itself with a
`?v=<sha>` cache-buster (fragment preserved) and falls back to the
immutable `/paper/v/<sha>/` snapshot only if the query is ignored.
