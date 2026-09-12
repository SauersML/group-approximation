# lx-redpow — class-level reduced powers at odd p (R4–R8), plus σ_r (OddPShufflePrimRoot), 2026-09-12

Owns `CharClass/OddPClasses*`, `OddPRedPow*`, `OddPInstab*`, and (coordinator, from lx-cartan-a's SPLIT)
`CharClass/OddPShufflePrimRoot.lean`.  Clone lix-m (probes of 09-12 morning ran on lix-d).

## Design
R4 is proved GENERICALLY instead of for `oddD`: any `NaturalCocycleOp K q N` (a function on
q-cochains of every space, natural, cocycle-preserving, no additivity) descends to cohomology.
So lx-diag owes only R1–R3, and `oddD` is packaged as `oddDOp`.  Instability (R7) is the `dif_neg`
branch of `redPow`, so no `OddPInstab*` file is needed.

## GREEN
* `CharClass/OddPClasses.lean` — probe 0912-104106-27928 (lix-d, SLURM acn111, base 2dc0f5976): PROBE GREEN,
  `BUILT`, 2818 jobs, `#audit_axioms` classical only.  Bytes on main at 1a447ee02 (md5 d3cb0ae1…, equal to the
  green record).  Contents: R5 `exists_eq_add_coboundary_of_cocycleClassK_eq` (any CommRing K),
  `eq_of_cocycleClassK_eq_deg_zero`, `cochainCoboundary_add_coboundary_eq_zero`; the cylinder `oddCyl`, `oddCylPr`,
  `oddCylIncl`, `oddCylHomotopy`, `toSSetObjEquiv_map_app_eq_comp`, `oddCylPr_app_oddCylIncl_app`,
  `oddCylIncl_zero_app_ne`, `cochainPullback_oddCylIncl_oddCylPr`, `oddCylCochain` and its two end values;
  `NaturalCocycleOp` (`op`, `natural`, `cocycle`), R4 `NaturalCocycleOp.class_add_coboundary`, `.classMap`,
  `.classMap_mk`, `.classMap_natural`.

## AUTHORED, UNVERIFIED
* `CharClass/OddPRedPow.lean` (on main at 1a447ee02; imports lx-diag's `OddPCochain`, itself unverified): `oddDOp`,
  `oddDClass` at every index `j ≤ pq` with `oddDClass_mk`, `oddDClass_natural`; `redPow_index_le`, `redPow_deg`,
  R6 `redPow p hp q i : Hmod (ZMod p) X q → Hmod (ZMod p) X (q + 2 * i * (p - 1))`, R7 `redPow_eq_zero_of_lt`,
  R8 `redPow_mk`, `pull_cohCast_redPow`, `redPow_natural`.  One probe once lx-diag's chain is green.
* `CharClass/OddPShufflePrimRoot.lean` (landing unverified now; probe on lix-m launched with the landing):
  permutations `mulPermFun`, `mulPermFun_injective`, `mulPerm (p r) (hr : Nat.Coprime r p)`, `@[simp] mulPerm_val`,
  `finRotate_pow_val`, `finRotate_pow_eq_of_mod_eq`, `mulPerm_mul_finRotate_pow` (`M*R^s = R^(rs)*M`),
  `mulPerm_mul_finRotate` (`M*R = R^r*M`), `mulPerm_inv_mul_finRotate_pow` (`M⁻¹*R^r = R*M⁻¹`),
  `mulPerm_mul_finRotate_pow_of_mul_mod_eq_one` (`M*R^s = R*M` if `r·s ≡ 1`), `mulPerm_mul_mulPerm`,
  `mulPerm_eq_one_of_mod_eq_one`, `mulPerm_inv_eq`; operators `tupPermAll_pow`, `tupTAll_mul_tupPermAll_mulPerm`
  (`T*P(M) = P(M)*T^r`), `tupTAll_pow_mul_tupPermAll_mulPerm_inv` (`T^r*σ_r = σ_r*T`, σ_r = P(M⁻¹)),
  `tupTAll_pow_mul_tupPermAll_mulPerm` (`T^s*P(M) = P(M)*T` if `r·s ≡ 1`); degree k `tupPerm_one`, `tupPerm_pow`,
  `tupT_mul_tupPerm_mulPerm`, `tupT_pow_mul_tupPerm_mulPerm_inv`.
  Model test `notes/lix-strong-swarm/tools/redpow_mulperm_test.py` (MSI, python3.11, seconds, v2): every identity
  0 failures (p ≤ 13, all units r, all s ≤ 2p); control `T^r*P(M) = P(M)*T` fails 84/117 (holds iff r² ≡ 1).

## NEEDS
* lx-diag: green `OddPDiagonalAug`, `OddPDiagonal`, `OddPCochain`, then one probe of `OddPRedPow`.
  `oddD` carries `[NeZero p] [Fact p.Prime]`; `OddPRedPow` has only `[Fact p.Prime]` and relies on
  `NeZero.of_gt'`.  If the probe says otherwise, add `[NeZero p]`.

## SPLIT (helpers, none needed now)
* `→+` bundling of `redPow`/`oddDClass`: needs R9 `redPow_add` (lx-additive).
* Packaging into `OddPTotal.GradedReducedPowers` fields `op`/`natural`/`unstable`: lx-pzero, from `redPow`,
  `redPow_natural`, `redPow_eq_zero_of_lt`.

## TRAPS
* `ShortComplex.exact_of_g_is_cokernel` takes `S` EXPLICITLY (`variable (S)` section): pass `_`.
* `ShortComplex.moduleCat_exact_iff` needs `import Mathlib.Algebra.Homology.ShortComplex.ModuleCat`.
* `Nat.Coprime.mul` does not exist at v4.32 core: the product lemma is `Nat.Coprime.mul_left (H1 : Coprime m k)
  (H2 : Coprime n k) : Coprime (m * n) k` (`Init/Data/Nat/Coprime.lean`); the toolchain source is readable locally at
  `~/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean/`.
* Model-test the COMPOSITION ORDER literally: v1 of the mulPerm test coded `R^r ∘ M⁻¹` where the Lean form is
  `M⁻¹ * R^r`, so it "refuted" a true identity and mislabeled a copy of form B as the control.
* SendMessage to a finished lane resumes it (lx-cartan-a was resumed by the name reservation note).
* A peer commit becc912bd ("Import Evington--Pennig …") deleted 27762 files from main (3.8M deletions); at
  3f71a3a50 the tree was whole again.  Landing on a tip taken mid-window would build on a gutted tree.
* zsh: `"$B:path"` colon modifier eats `:P…`; quote separators.
