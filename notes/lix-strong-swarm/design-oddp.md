# Design: the reduced powers at an odd prime, for Step D mod p (lx-design, 2026-09-12)

Lane `lx-design` of the LIX strongest swarm.  This note turns the odd-primary side into
statements a Lean lane can author against.  It covers the operations, their normalisation, the
Cartan formula, and exactly what the consumers of `CharClass/LIXStepDGenReal.lean` and
`CharClass/ChernSplittingOf*.lean` use.  Throughout, `p` is an odd prime, `m = (p−1)/2`, and
`D_j u` is the cochain R1 of `notes/lix-stronger-lane-reports/lix-descent.md` (SCOPE 3).

## 0. Summary of the findings

1. **The consumers never need `P⁰ = id` on an arbitrary class, and the producers cannot give it.**
   A statement `D_{q(p−1)} = c_q · id` on every class of degree `q` is a universal-example statement.
   It holds on `K(ℤ/p, q)`, which the tree does not have, and neither a top-index cochain reading nor
   stability along `δ` proves it on singular chains.  The consumers use `P⁰` only on `1`, on Chern
   roots and their products (flag space), and implicitly on `z` (torus), where it can be avoided.
   §4 gives the narrowed interface.
2. **The primary object is the total operation `P_tot := Σ_{j even} [D_j]`.**  It is a ring
   homomorphism of the even part for every space, with no vanishing lemma.  A graded Cartan formula
   on arbitrary even classes would need a second vanishing lemma V′ (`[D_a x] = 0` for
   `a > d(p−1)`), which has no cheap proof on singular chains.  The narrowed consumers apply graded
   components only to classes whose `P_tot` has integral non-negative components, so V′ is never needed.
3. **One vanishing lemma is needed, V, at least on degree-2 classes:** `[D_j u] = 0` for `u` of even
   degree unless `j ≡ 0` or `−1 mod 2(p−1)`.  It is needed at every odd prime, `p = 3` included.  The
   route is the automorphism `T ↦ T^r` with `r` a primitive root, compared by acyclic-models
   uniqueness.  It reuses the Cartan comparison's machinery.
4. **The normalisation constant `μ` with `[D_{2(p−1)} h] = μ·h` on Euler classes is `−1`.**  It is
   computed on `T² = S¹ × S¹` from the descent constant `c₁ = m!` and the degree-(1,1) corner of the
   Cartan comparison, whose sign is `(−1)^m`.  A line bundle on `T²` with nonzero Euler class links
   `T²` to `ℂP^M`.  Wilson's theorem gives `(−1)^m (m!)² = −1`.
5. **Normalised as `P^i u := μ^{−(k−i)}·[D_{2(k−i)(p−1)} u]` on `H^{2k}`, `P¹h = h^p` on every
   degree-2 class**, so the Wu leading constant is `m = 1`, not `−1`.
6. **Nothing odd enters the operations layer except the `T²` corner.**  `P^{>0} z = 0` comes from
   dimension, since `z` is pulled back from `S¹ × S^{2n+1}`, whose cohomology vanishes above
   degree `2n+2`.  The Cartan formula for the odd classes `t`, `x` is not used.

## 1. The operations

**(R) `D_j` at class level, every index.**  For `u ∈ H^q(X; F_p)` and `0 ≤ j ≤ pq`,
`oddDClass p q j u ∈ H^{pq−j}(X; F_p)` is the class of `D_j(v)` for any cocycle `v` representing `u`.
It is well defined by R4 (cylinder) and R5 (exactness).  It is natural (R3), additive (R9), and
`F_p`-linear because `D_j(c v) = c^p D_j v = c·D_j v`.  Owners: lx-diag (R1–R3), lx-redpow (R4–R8,
and the class-level `oddDClass` at every `j`), lx-additive (R9).

**(A) Top power.**  `oddDClass p q 0 u = u ⌣ ⋯ ⌣ u` (`p` factors), in every degree.  Route: apply
`acyclicModelsHomotopy` over `Λ = ZMod p`, non-equivariantly, with source `C(−)` (free on
simplices) and target `C(−)^{⊗p}` (acyclic on models by `tupD_exists_preimage_stdSimplexTop` at
`r = p`).  Compare `f = Δ(e₀ ⊗ −)`, a natural chain map because `d_W e₀ = 0` (Δ1), with the iterated
Alexander–Whitney diagonal `g`.  They agree in degree 0 by Δ6.  Evaluating `u^{⊗p}` on `g` gives the
`p`-fold cup product at cochain level, and the homotopy term is a coboundary by E4′.  Owner: lx-toppower.

**(C) The descent constant.**  `oddDClass p 1 (p−1) t = m!·t` for degree-1 classes, at least on
`S¹`.  Discharge `EvalIsHeadCoeff` and link `eDescent_value_of_eval` to the class-level operation.
It is used only for `μ` (§3).  Owner: lx-toppower.

## 2. The Cartan comparison and the total operation

**(K) D-form comparison.**  Take cocycles `u ∈ C^q`, `v ∈ C^{q'}`, and write `ψ_W` for lix-tower's `psiW`.  Compare
`Φ_A = AW^{⊗p} ∘ Δ` with `Φ_B = R ∘ (Δ ⊗ Δ) ∘ shuffle ∘ (ψ_W ⊗ AW)`, both natural `Λ`-chain maps
`W ⊗ C(X) → C(X)^{⊗2p}`.  `Λ` acts on the target by `tupT²` (target `oddTgt p (2p) 2`).  The riffle `R`
belongs only on the `Φ_B` side, because the slotwise AW already emits the order `x₁y₁…x_py_p`.
Acyclic-models uniqueness makes them homotopic.  Evaluating `(u ⊗ v)^{⊗p}` gives, at class level,

    [D_j(u ⌣ v)] = Σ_{a+b=j} ε(a,b,q,q') · c̄(a,b) · [D_a u ⌣ D_b v]

where `c̄(a,b)` is the augmentation of the `ψ_W` coefficient: `1` when `a`, `b` are both even and
`0` when both are odd (lix-tower's `wdPhi` lemmas).  `ε` is the regroup sign `(−1)^{b·(pq−a)}` times
the riffle sign `(−1)^{qq'·p(p−1)/2}`.  For `q`, `q'` even every even-even term has `ε = 1`.
Owner: lx-cartan-b, with signed slot permutations from lx-cartan-a.

**(T) The total operation.**  For even `q`, `P_tot u := Σ_{j even ≤ pq} oddDClass p q j u`.  By (K),
`P_tot(u ⌣ v) = P_tot u ⌣ P_tot v` for all even classes on every space, with no vanishing lemma.
`P_tot 1 = 1` because only `j = 0` occurs and `1^p = 1`.  `P_tot` is natural.
So `P_tot : evenPart (ZMod p) X →+* evenPart (ZMod p) X`.  Owner: lx-pzero (packaging).

**(V) Vanishing.**  For `u` of even degree, `oddDClass p q j u = 0` unless `j ≡ 0` or `−1 mod 2(p−1)`.
Route: `r` is a primitive root mod `p`, and `θ_r : T ↦ T^r`.
* `A_r : W → W` is the `θ_r`-semilinear chain map `A_r e_{2k} = r^k e_{2k}`,
  `A_r e_{2k+1} = r^k ρ_r e_{2k+1}` with `ρ_r = 1 + T + ⋯ + T^{r−1}`.  Its augmentations are `r^k` and
  `r^{k+1}`.  This uses the tree's convention that `d : W_{i+1} → W_i` multiplies by
  `altCoeff i = if Even i then grS else grNorm`.
* `σ_r` is the slot permutation `t ↦ t ∘ π⁻¹` with `π(i) = r·i`, carrying the Koszul sign; it
  satisfies `σ_r ∘ T = T^r ∘ σ_r`.
* `σ_r ∘ Δ` and `Δ ∘ (A_r ⊗ 1)` are natural `Λ`-chain maps into `oddTgt p p r` (`T` acting by
  `tupT^r`) that agree in degree 0, so they are homotopic.
* Evaluating `u^{⊗p}`, whose Koszul sign under `σ_r` is `+1` in even degree, gives
  `[D_j u] = aug(A_r e_j)·[D_j u]`.  The factor `aug − 1` is a unit off the two residues.

Only degree-2 classes are needed, but the proof is the same in every even degree.  Owner: lx-cartan-b.

**No V′.**  A graded Cartan formula on arbitrary classes would also need `[D_a x] = 0` for
`a > d(p−1)`.  On singular chains that needs normalized chains or a carrier construction.  §4 never
uses it.

## 3. The normalisation constant

* **Euler classes.**  `H²(ℂP^M; K)` is the line spanned by `hgen`, so `oddDClass p 2 (2(p−1)) hgen = μ·hgen`
  for a scalar `μ`.  `μ` does not depend on `M` (linear inclusions), and every `e(L)` pulls back from
  `hgen` along the classifying map (`eulerOfBundleOf`).  So `[D_{2(p−1)} e(L)] = μ·e(L)`.
* **Degree-2 classes.**  For an Euler class `y`:
  * `[D₀ y] = y^p` by (A);
  * `[D_{2a} y] = 0` for `0 < a < p−1` by (V);
  * `[D_{2p} y] ∈ H⁰` vanishes, by restriction to points.
  Hence `P_tot y = y^p + μ·y`.
* **`μ = −1`.**  Take `t₁`, `t₂` the pulled-back generators of `H¹(S¹)` on `T²`.
  * By (K) at `q = q' = 1`, only `a = b = p−1` survives, because `[D_a t] ∈ H^{p−a}(S¹)` vanishes
    otherwise.  The riffle sign is `(−1)^{p(p−1)/2} = (−1)^m` and the regroup sign is `+1`
    (`b = p−1` is even), so `[D_{2(p−1)}(t₁t₂)] = (−1)^m c₁²·t₁t₂`.
  * Link: one line bundle `L` on `T²` with `e(L) ≠ 0`.  `H²(T²; K)` is a line, so `e(L) = λ·t₁t₂`.
    Candidate: `L` = the pullback of `O(1)` along a collapse `T² → ℂP¹`.  `e(L) ≠ 0` follows from the
    Step C lemma over `K`: one zero, at which the collapse is a local homeomorphism, over a base that is
    a product of odd spheres.
  * Wilson: `(−1)^m (m!)² = −1`.

  Owner: lx-pzero (with lx-toppower's `c₁` and lx-cartan-b's corner).
* **Graded components.**  On `H^{2k}`, `P^i u := μ^{−(k−i)}·oddDClass p (2k) (2(k−i)(p−1)) u`, and `0`
  when `i > k`.  Instability holds by definition.  On every class `P¹h = h^p`, so `κ = m = 1`.

## 4. The narrowed consumer interface

Every item below was checked against its consumer.

* **Flag space `F`** (`PowerData`, `ParityPWuCartan.lean:229`; `hasSplittingP_flag`).  The Wu
  induction uses `p_zero_apply` only on `1`, on roots and on root products (`p_mul_y` at `u = ∏y`,
  `p_prod`, `p_one_eq_zero`), and `cartan` only for a root times a root product.  Narrowed fields
  (lx-splitK):
  * `p_zero_prod : ∀ C, P 0 (∏ l ∈ C, y l) = ∏ l ∈ C, y l`;
  * `p_one_pos : ∀ n, 0 < n → P n 1 = 0`;
  * `cartan_y : ∀ n k C, P n (y k * ∏ y) = Σ_j P j (y k) * P (n − j) (∏ y)`;
  * `hone` with `m = 1`, and `hhigh`, `hnat` unchanged.

  Producer: `P_tot(∏ y) = ∏ (y^p + μ y)` gives integral non-negative components, and the components are
  exactly these after normalising.
* **Torus `N`** (`RealTorusModP`).  `PN_zero` feeds only `pH_z_mul_of_cartan`, whose single use is
  `ParityPData:471` on `b_{i+1}` with `pR_b_succ` (`P^i b = 0`).  Narrowed (lx-torusP, lx-slice2,
  lx-splitK):
  * drop `PN_zero`, `P_t`, `P_x`;
  * replace `pH_z_mul` / `pH_zero + cartan + pH_z` by `pH_z_mul_zero : ∀ i r, PR i r = 0 → PH i (z * ι r) = 0`;
  * keep `natural`, `PY_unstable` (by definition), `PN_even`, `PY_even`, `circle_two`, `z_inj`.

  Producer: `P_tot(z · ι b) = P_tot z · ι P_tot b` with `P_tot z = ν·z`.  The even target degrees of
  `D_j z` on `S¹×S^{2n+1}` are `0` (points) and `2n+2`.  `ν` is never used.
* **Splitting** (`HasSplittingP.hP`): naturality of every component, general.

**Landed spellings (2026-09-12, as reported by the owners):**
* lx-splitK, `CharClass/ParityPWuCartanNarrow`: `ParityP.PowerDataN` with `p_zero_y`, `p_zero_one`,
  `p_one_pos`, `cartan_y`, `p_y_one`, `p_y_high` (`p_zero_prod` derived);
  `…WuTransportNarrow.wu_field_of_splittingN` (`hP` only at `γ (i+1)`); `ParityPDataN` /
  `SplitStepDDataN` with `pH_z_mul_zero`.  The flag producer works on even parts with `hzero_root`,
  `hzero_one`, `hone_pos`, Cartan for a root times a root product, `hone` (`m = 1`), `hhigh`, and
  naturality at the Chern classes.
* lx-torusP, **verified at origin `205a479d0` (lx-review audit)**: `Gen.RealTorusModP` is on even
  parts and has `P_z` (`Gen.P_z_of_sphereFactor`, `CharClass/LIXStepDGenTorusPModel`), but it STILL
  carries `PN_zero : ∀ x, PN 0 x = x` and an unguarded `cartan`.  `z_mul_zero` is not there.  An earlier
  version of this entry recorded the planned restatement as landed; it was not.
* lx-pzero, `CharClass/OddPTotal*`: producer `TotalReducedPowers` (`D X q j`, `ptot`, `ptot_mul` on
  even classes, `top_two`, `bad_two` = V in degree 2, unit `μ`, `zero_cp`) → consumer
  `EvenReducedPowers`.  The consumer has the graded `P`, a subring `Good` of junk-free classes with
  `cartan` on it, `zero_one`, `zero` on Euler classes only (not on arbitrary degree-2 classes: a mod-`p`
  class need not reduce an integral one), `degree_two` (`κ = 1`), and `mul_single`.
  `mul_single` says `P^i(z·w) = c·z·P^i w` whenever `z` has a single `ptot` component; it gives
  `pH_z_mul_zero` for every even `w`, with no generation theorem for `H^*(∏ ℂP)`.
* lx-redpow, `CharClass/OddPRedPow`: `oddDClass p hp q j hj x`, `oddDClass_mk`, `oddDClass_natural`;
  `redPow` is `cohCast` of the same class map at `j = (q−2i)(p−1)`.

**Routing gaps on the odd-prime path (lx-review, origin `c1b23d84a`; rechecked at `205a479d0`).**  The
narrowed structures exist, but the path `LemmaTwoPowersModPData` actually runs still goes through the
strong forms:
* (a) `RealBundleModP.toModPStepDData` sets `pH_zero := T.PN_zero` and `cartan := T.cartan`, then goes
  through `ModPStepDData.toParityPData` (`LIXStepDGenModP:142`, strong `pH_z_mul_of_cartan`) to
  `ParityPData:471`.  Needed: `ModPStepDDataN` with `pH_z_mul_zero` and `toParityPDataN` into
  `ParityPDataN` (lx-slice2), then `RealBundleModP.toModPStepDDataN` (lx-torusP).
* (b) `RealTorusModP`: replace `PN_zero` and the general `cartan` with
  `z_mul_zero : ∀ i r, PY i r = 0 → PN i (evenZClass … * evenMap K pY r) = 0`, produced by
  `EvenReducedPowers.mul_single` and `P_z` (lx-torusP).
* (c) `LIXStepDGenBundleP`/`BundlePLix` consume the strong `HasSplittingP` and `realWu_of_splitting`
  (strong `PowerData`, `hP ∀ x`).  Needed: `realWu_of_splittingN` over `PowerDataN` and
  `wu_field_of_splittingN` (lx-torusP owns `LIXStepDGenReal*`), then the switch in lx-bundleP.
* Reds created by the restatements: `LIXStepDGenTorusPModel.ofEven` uses the removed `ops.zero N` and the
  now Good-guarded `ops.cartan N`, and `BundleP`/`BundlePLix` use the removed `T.PN_even`.

## 5. Model tests

`notes/lix-strong-swarm/tools/design_oddp_modeltest.py`, run on MSI.  It checks:
* the constants `c_1 = m!`, `c_2 = −1`, `c_{2k} = (−1)^k`, `(−1)^m (m!)² = −1`, and the riffle sign
  `(−1)^{p(p−1)/2} = (−1)^m`;
* `A_r` is a `θ_r`-semilinear chain map with augmentations `r^k` / `r^{k+1}` in `F_p[C_p]` under the
  tree's `altCoeff` convention (`p ≤ 13`, all `r`, degrees `≤ 12`);
* `σ_r T = T^r σ_r` for both rotation directions;
* under V, the surviving pairs of the even Cartan sum at `j = 2(k+k'−i)(p−1)` are exactly the
  standard ones, and without V there are extra pairs.

Run 2026-09-12 on acn112 (python3.11): `checks=10237 fails=0`, over `p` up to 101 for the constants and
`p ≤ 13` for the resolution.  The control passes: at `k = k' = 1`, `i = 1` there are `p` even-even pairs
without V and 2 with it.
