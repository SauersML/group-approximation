# lx-redpow — class-level reduced powers at odd p (R4–R8), 2026-09-12

Owns `CharClass/OddPClasses*`, `OddPRedPow*`, `OddPInstab*`.  Clone lix-d (shared with lx-diag).

## Design
R4 is proved GENERICALLY instead of for `oddD`: any `NaturalCocycleOp K q N` (a function on
q-cochains of every space, natural, cocycle-preserving; no additivity) descends to cohomology.
So lx-diag owes only R1–R3, and `oddD` is packaged as `oddDOp`.

## GREEN
(pending: probe of OddPClasses on lix-d)

## AUTHORED, UNVERIFIED
* `CharClass/OddPClasses.lean` (probe running): R5 `exists_eq_add_coboundary_of_cocycleClassK_eq`
  (any CommRing K), `eq_of_cocycleClassK_eq_deg_zero`, `cochainCoboundary_add_coboundary_eq_zero`;
  the cylinder `oddCyl`, `oddCylPr`, `oddCylIncl`, `oddCylHomotopy`, `toSSetObjEquiv_map_app_eq_comp`,
  `oddCylPr_app_oddCylIncl_app`, `oddCylIncl_zero_app_ne`, `cochainPullback_oddCylIncl_oddCylPr`,
  `oddCylCochain` + its two end values; `NaturalCocycleOp` (op, natural, cocycle), R4
  `NaturalCocycleOp.class_add_coboundary`, `.classMap`, R8-generic `.classMap_mk`, `.classMap_natural`.
* `CharClass/OddPRedPow.lean` (not probed; imports lx-diag's unlanded `OddPCochain`): `oddDOp`,
  `redPow_index_le`, `redPow_deg`, R6 `redPow`, R7 `redPow_eq_zero_of_lt`, R8 `redPow_mk`,
  `pull_cohCast_redPow`, `redPow_natural`.

## NEEDS
* lx-diag: `OddPCochain` with `oddD`, `oddD_cocycle (hp : Odd p) (hj : j ≤ p*q)`, `oddD_natural`
  exactly as in lix-descent SCOPE 3 R1–R3 (message sent).

## TRAPS
* zsh: `"$B:path"` colon modifier; quote separators.
