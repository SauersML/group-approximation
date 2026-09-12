# lx-redpow — class-level reduced powers at odd p (R4–R8), 2026-09-12

Owns `CharClass/OddPClasses*`, `OddPRedPow*`, `OddPInstab*`.  Clone lix-d (shared with lx-diag).

## Design
R4 is proved GENERICALLY instead of for `oddD`: any `NaturalCocycleOp K q N` (a function on
q-cochains of every space, natural, cocycle-preserving, no additivity) descends to cohomology.
So lx-diag owes only R1–R3, and `oddD` is packaged as `oddDOp`.  Instability (R7) is the `dif_neg`
branch of `redPow`, so no `OddPInstab*` file is needed.

## GREEN
* `CharClass/OddPClasses.lean` — probe 0912-104106-27928 (lix-d, SLURM acn111, base 2dc0f5976): PROBE GREEN,
  `BUILT`, 2818 jobs, `#audit_axioms` classical only.  Bytes on main at 1a447ee02 (landed unverified before the
  probe; same bytes).  Contents: R5 `exists_eq_add_coboundary_of_cocycleClassK_eq` (any CommRing K),
  `eq_of_cocycleClassK_eq_deg_zero`, `cochainCoboundary_add_coboundary_eq_zero`; the cylinder `oddCyl`, `oddCylPr`,
  `oddCylIncl`, `oddCylHomotopy`, `toSSetObjEquiv_map_app_eq_comp`, `oddCylPr_app_oddCylIncl_app`,
  `oddCylIncl_zero_app_ne`, `cochainPullback_oddCylIncl_oddCylPr`, `oddCylCochain` and its two end values;
  `NaturalCocycleOp` (`op`, `natural`, `cocycle`), R4 `NaturalCocycleOp.class_add_coboundary`, `.classMap`,
  `.classMap_mk`, `.classMap_natural`.

## AUTHORED, UNVERIFIED (on main at 1a447ee02)
* `CharClass/OddPRedPow.lean` (imports lx-diag's `OddPCochain`, itself unverified): `oddDOp`, `oddDClass` at every
  index `j ≤ pq` with `oddDClass_mk`, `oddDClass_natural` (lx-design's request); `redPow_index_le`, `redPow_deg`,
  R6 `redPow p hp q i : Hmod (ZMod p) X q → Hmod (ZMod p) X (q + 2 * i * (p - 1))`, R7 `redPow_eq_zero_of_lt`,
  R8 `redPow_mk`, `pull_cohCast_redPow`, `redPow_natural`.  Probe waits on lx-diag's green OddPDiagonal*/OddPCochain
  (probing that closure now would duplicate their build).

## NEEDS
* lx-diag: green `OddPDiagonalAug`, `OddPDiagonal`, `OddPCochain`, then one probe of `OddPRedPow` here.
  `oddD` carries `[NeZero p] [Fact p.Prime]`; `OddPRedPow` has only `[Fact p.Prime]` and relies on
  `NeZero.of_gt'` + `Nat.Prime.one_lt'`.  If the probe says otherwise, add `[NeZero p]`.

## SPLIT (helpers, none needed now)
* `→+` bundling of `redPow`/`oddDClass`: needs R9 `redPow_add` (lx-additive).
* Packaging into `OddPTotal.GradedReducedPowers` fields `op`/`natural`/`unstable`: lx-pzero, from `redPow`,
  `redPow_natural`, `redPow_eq_zero_of_lt`.

## TRAPS
* `ShortComplex.exact_of_g_is_cokernel` takes `S` EXPLICITLY (`variable (S)` section): pass `_`.
* `ShortComplex.moduleCat_exact_iff` needs `import Mathlib.Algebra.Homology.ShortComplex.ModuleCat` (not in the
  CharClass closure by default).
* zsh: `"$B:path"` colon modifier eats `:P…`; quote separators.
* A congrArg with a lambda over `toSSetObjEquiv` needs no simp: the evaluation is definitional; a `simp only [lemma]`
  there is an unused-simp-argument ERROR under warningAsError.
