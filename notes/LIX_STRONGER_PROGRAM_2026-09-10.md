# STW Problem LIX, the stronger theorem: unconditional Lean program (2026-09-10, lead: session 6bb5d6d1)

USER ORDER (2026-09-10): "get opus 5 team to formalize stronger version ... make sure it is
100% unconditional, no literature inputs".  This note is the single source of truth for the
program.  Read it fully before writing a line.  It extends, and never edits, the closed
program `notes/LIX_FULL_PROGRAM_2026-09-05.md` (the mod-2 answer to LIX, verified by the
Palomar Comparator on 2026-09-10 at `f6da71566`, surface `Palomar/LIXChallenge.lean`).

## 0. The target, and the wall it stops at

The manuscript family (`research/stw59-simple-ah-factorial-unitary-torsion.md`) has, for
every `n ≥ 2`, a simple unital AH algebra `A_n` with `K₁(A_n) = 0` and a unitary `v_n` whose
component has **exact order `n!`**.  Its proof is integral (K-theory Künneth, Chern character)
and its upper bound `v_n^{n!} ∈ U₀(A_n)` is Bott's `π_{2n}(U(n)) ≅ ℤ/n!`.  Neither is
formalizable without literature input, and the user forbids literature input.  So the
program formalizes the **lower bound**, which is what mod-p characteristic classes see:

```lean
/-- The stronger theorem.  For every n ≥ 2: a separable simple unital C*-algebra with a
unitary that dies in K₁ at the first stabilisation and whose powers stay outside U₀ unless
the exponent is divisible by every prime dividing n. -/
theorem exists_simple_unital_unitary_powers_outside_U0 (n : ℕ) (hn : 2 ≤ n) :
    ∃ (A : Type) (_ : CStarAlgebra A), Nontrivial A ∧ IsSimpleRing A ∧ SeparableSpace A ∧
      ∃ v : unitary A, diagOne v ∈ pathComponent 1 (unitary (CStarMat 2 A)) ∧
        ∀ k : ℕ, v ^ k ∈ pathComponent 1 (unitary A) → ∀ p : ℕ, p.Prime → p ∣ n → p ∣ k
```

Corollary (headline instance, `n = 6`): a simple unital separable `A` and `v ∈ ker κ_A` with
`v ^ k ∈ U₀(A) → 6 ∣ k`, i.e. an element of `U(A)/U₀(A)` of order divisible by 6 (or
infinite) that is trivial in `K₁`.  Corollary (every squarefree order): for every
squarefree `N` take `n = N`.  The `n = 2` instance is the existing theorem.

**Not claimed, not attempted:** `K₁(A) = 0`, exact orders, `p² ∣ k`, nuclearity, traces,
stable rank.  Mod-p cohomology cannot see `p²` (see §1.4), so `rad(n) ∣ k` is the sharp
statement this method yields.  Anyone proposing to formalize the exact order must first
produce, on paper, an unconditional proof of `2·Ση = 0 ∈ π₄(S³)`; see
`Analysis/LIXGeneratorUnitary.lean`'s module docstring for why the obvious ansätze fail.

## 1. The mathematics, as the Lean will do it

Everything is the mod-2 program with three parameters made explicit: the rank `n`, the
prime `p`, and the exponent `k`.  Read `notes/LIX_FULL_PROGRAM_2026-09-05.md` §1 first; only
the differences are stated here.

### 1.1 Objects, generic in `n`

* `S^{2n+1} := unitVectors (Fin (n+1)) ⊂ Fin (n+1) → ℂ` (sup norm, plain product, no
  `EuclideanSpace ℂ`), `S^{2n} ⊂ EuclideanSpace ℝ (Fin (2n+1))` as the equator
  `Re (x n) = 0` (`LIXLemmaSixGenerator.equatorEmb` generalised).
* Stage `i`: `r_i = n · 2^i` (`stageRank`), `Y_i = ∏_{j<i} CP(r_j)`, `X_i = S^{2n} × Y_i`,
  `H_i = ⊕_{j<i} L_j^{⊕ r_j}`, `E_i = 1^n ⊕ H_i`, `A_i = E_i M(C(X_i)) E_i`.  `rank E_i = r_i`.
  The twisted connecting maps, the limit, simplicity and separability are the existing
  arguments with `2` replaced by `n` (`Analysis/LIXConnectingMap`, `LIXLimitAlgebra`,
  `CStarSimple`, ...).  **`p ∣ r_j` for every prime `p ∣ n` and every stage** — this is the
  only place the tower's shape enters Step D.
* `F` over `S^{2n+1}`: `Fproj = 1_{n+1} − x xᴴ` (rank `n`), the complement of the tautological
  section.  The generator `u : S^{2n} → U(n)` is the seam discrepancy of the two hemisphere
  frames of `U(n+1) → S^{2n+1}` (Householder reflections through the normalised midpoint,
  exactly as at `n = 2`), so `diag(u, 1)` contracts in `U(n+1)` for free and the projection
  clutched by `u` is `Fproj`.  No `π_{2n}(U(n))` anywhere.
* `V = 1^{n+1} ⊕ H`, rank `r = n + 1 + m`, `m = Σ d_i`, over `M = S^{2n+1} × Y`; the two
  projections are `FHmat = V − s sᴴ` and `EHmat = V − e eᴴ`.
* **Status 2026-09-10 11:56 CDT (`sp-tower`, PROBE GREEN 3040 jobs on cs-stages):** the whole C*-side is
  generic in `n` (`STW59.Gen.*`, every old name kept as the `n = 2` specialisation, `stageRank n i :=
  2 ^ i * n` so `n = 2` is a `rfl`): block projections, connecting maps, stage algebras with the
  pi-shaped `CStarAlgebra` instance, separability, the tower and limit, fullness, and
  `Gen.lixLimit_isSimpleCStar n` — **the counterexample algebra is simple at every rank, on axioms
  exactly `[propext, Classical.choice, Quot.sound]`**.  Only `Nontrivial (Gen.LIXLimit n)` carries
  `[NeZero n]`.  Four defects the gates caught were all of one family (a generalisation changes how a
  name unfolds or what it needs: `stageProj`/`stageEval`/`connectMatrix` became abbrevs, so
  unfold-by-name sites now cite `*_def` rfl lemmas); two repository-wide checkers now guard them.

### 1.2 The constant section moves to the equator (design, owner `sp-design`, then `sp-oddside`)

At `n = 2` the constant section is `e = e₃` and the transported section's single zero sits
at `(south pole of S¹, −e₃, basepoint)` (`LIXSectionManuscript`).  `−e₃` is the suspension
point of the clutching coordinate, and a degree-`k` map of the sphere that preserves the
hemispheres is a cone at the suspension points, so with `e = e₃` the `k`-th power's zeros
could never be local homeomorphisms.  **Take `e = e₁`** (any unit vector with
`Re (e n) = 0`): `EHmat` changes by a constant unitary, Lemma 2 is unchanged, and the zero
moves to `x = −e₁` on the equator.  `sp-design` must confirm from `LemmaTwoZero.lean` that
the zero of the transported section for abstract block data `(a, b, c)` is where `b = −a`.

### 1.3 Powers: Step C with `k` zeros (design, owners `sp-design`, `sp-powers`, `sp-oddside`)

For `v^k ∉ U₀(A_j)` the chain is:

1. **Eckmann–Hilton on `U(n)`-valued maps of `S^{2n}`.**  `u^k` (pointwise power) and
   `u ∘ ψ_k` are homotopic, where `ψ_k : S^{2n} → S^{2n}` is an explicit `k`-fold map (§1.3.2).
   Formal shape (as landed, `Analysis/LIXPowersGauge.lean`): the gauge lemma asks only for a BALL
   unitary (continuous and unitary on the closed ball, no basepoint condition), and the seam generator
   normalises for free: with `wallRetract` the radial retraction onto the wall, `A := U ∘ wallRetract`
   is a ball unitary, `ũ := Aᴴ U` is a ball unitary identically `1` on the wall, `U = A ũ`, and
   `clutch(u^k) ≅ clutch(ũ^k)` by the left gauge lemma with the ball-unitary factor
   `(A ũ)^k (ũ^k)ᴴ`.  **Path-connectedness of `U(n)` is needed nowhere; do not prove it.**
   (owner `sp-powers`; `Analysis/LIXPowersNormalise.lean`)
2. **Gauge lemma.**  If `a ∈ U₀` (extends over the northern hemisphere) then
   `clutch(a·b) ≅ clutch(b)` (change the northern trivialisation by the extension; this is
   `LIXClutching`'s seam trick and needs no square root).  Hence `clutch(u^k) ≅ clutch(u ∘ ψ_k)`.
   (owner `sp-powers`; check whether `LIXClutching` already has it in this generality)
3. **Naturality of clutching.**  `clutch(u ∘ ψ_k) = (Σψ_k)^* clutch(u) = (x ∘ Σψ_k)^⊥` where
   `Σψ_k : S^{2n+1} → S^{2n+1}` is the suspension (acts on the equatorial coordinates, fixes
   the clutching coordinate `Re (x n)`).  (owner `sp-powers`)
4. **Step C with `k` zeros.**  With `b = x ∘ Σψ_k` and `a = e₁` the transported section
   vanishes exactly at `{south} × (Σψ_k)^{-1}(−e₁) × {basepoint}`, which is `k` equatorial
   points at each of which `Σψ_k` is a local homeomorphism (§1.3.2).  Then
   `γ_r(W_g) = j^*(σ^* U) = Σ_i j^*(loc_i)` by excision to `k` disjoint balls, and each
   `j^*(loc_i)` is the one-zero computation already in the tree (`LIXStepCOdd*`), transported
   along the rotation `ρ^i` (§1.3.2): `j^*(loc_i) = (ρ^{-i})^*(j^*(loc_0)) = j^*(loc_0)` by
   naturality of `j` and ABSOLUTE homotopy invariance (`ρ` is isotopic to the identity).
   Hence `γ_r(W_g) = k · c₀` with `c₀ ≠ 0`, so `γ_r(W_g) ≠ 0` whenever `p ∤ k`.
   **Over `F_p` with `p` odd this is where signs would enter; the `ρ`-symmetry is what makes
   every local contribution literally equal, so no local degree is ever computed.**
   (owner `sp-oddside`, after `sp-design` signs off)

**Interface decision (2026-09-10, after sp-powers' grep).**  The live Corollary 4 never uses the
clutching layer: it glues the two hemisphere frames of `LIXGeneratorUnitary` with the null-homotopy
of `u ⊕ 1_H` into a unitary field `G` with `G e₃ = x`, so "`clutch u ≅ F`" is nobody's deliverable
and is not in the tree.  The PRIMARY export of `sp-powers` is therefore the bare homotopy
`u^k ≃ u ∘ ψ_k` through unitary maps `S^{2n} → U(n)` (no clutching), which `sp-tower`'s k-indexed
Corollary-4 chain consumes with the frames pulled back along `Σψ_k` (seam `u ∘ ψ_k`, `e₃ ↦ x ∘ Σψ_k`).
**Superseded the same day:** the endpoint WITNESS is the renormalised generator `ũ := Aᴴ u`
(`A := U ∘ wallRetract`, a ball unitary; `ũ ≡ 1` on the wall), so no path from `A` to `1` is ever
built: `ũ ⊕ 1 = (A ⊕ 1)⁻¹(u ⊕ 1)` still contracts in `U(n+1)`, `ũ ∉ U₀ ⟺ u ∉ U₀`, the frames gauged
by `A` on one hemisphere have seam `ũ` and still take `e₃ ↦ x`, and `sp-powers`'
`exists_homotopy_pow_comp_normGen` gives the explicit unitary homotopy `ũ^{k+1} ≃ ũ ∘ ψ_k` directly.
No path in `U(n)` anywhere in the program.  `sp-tower` builds the k-indexed Corollary-4 chain around
`ũ`; `FHmat_k` on the CharClass side is `FHmat` with `b = x ∘ Σψ_k` (`FHmat_eq_fromBlocks` unchanged).
The clutched statement (items 2–3 above, `LIXPowersChain.lean`) stays as the geometric form and is
off the critical path.

#### 1.3.2 The `k`-fold map `ψ_k` (AGREED 2026-09-10 by `sp-design` and `sp-powers`, independently)

Write `S^{2n} ⊂ ℂ × ℂ^{n-1} × ℝ` (equatorial coordinates) with `x₀ ∈ ℂ` the coordinate of the
`e₁`-plane.  Then
```
ψ_k(x₀, x') = (x₀^k / |x₀|^{k-1}, x')
```
is continuous (the quotient is `0` at `x₀ = 0` by Lean's convention and is `O(|x₀|)`), norm-preserving
and positively homogeneous, so it is its own cone: `Σψ_k` on `S^{2n+1}` is **literally the same formula**
with the clutching coordinate `Re (x n)` untouched (`Analysis/LIXPowersNaturality.lean`, `IsRadialMap`).
Two corrections to the first draft of this note: the rotation `ρ` of order `k` is the rotation
`x₀ ↦ e^{2πi/k} x₀` **in the `e₁`-plane** (not in a plane avoiding `e₁`), so that `ψ_k ∘ ρ = ψ_k`; and
the local identity at the `k` preimages `ψ_k^{-1}(−e₁) = {x₀^k = −1, x' = 0}` is **precomposition**:
near `ρ^i q₀` the map is the map near `q₀` precomposed with `ρ^{-i}`, and it is a local
homeomorphism there because `x₀ ≠ 0`.  The vertical slab pinch does NOT work (it jumps by 2 at every
interior interface, model-confirmed); only the angle coordinate closes, because its two ends are the
same set.  Eckmann–Hilton (`Analysis/LIXPowersEH.lean`) reduces `u^k ≃ u ∘ ψ_k` to the one named
`Prop` `PinchIdentification`, which `sp-powers` discharges through the angle family.  Renormalising
the seam generator by a disc unitary `a` is free for the whole chain, powers included
(`clutch((a·ũ)^k) ≅ clutch(ũ^k)` via `θ ↦ (A_θ ũ)^k ũ^{-k}`, no centrality needed), which removes the
basepoint obstruction.  Model tests: `scratch/sp-powers/powers_modeltest.py` on MSI (50 checks).

### 1.4 Step D mod `p`, uniform in the stage (design, owner `sp-design`, then `sp-evenside`)

Over `F_p`: `H^*(N) ⊇ H^*(Y)[z]/(z²)` in even degrees, `z = t x`, `deg z = 2n+2`,
`γ(W) = γ(V)(1 + z b)`, `b ∈ H^*(Y; F_p)` unknown.  Available relations, and ONLY these:
the total reduced power `P = Σ P^i` is a ring homomorphism (Cartan), `P(h) = h + h^p` on
degree-2 classes, `P(z) = z`, instability `P^i = 0` below degree `2i`, and the Wu relations
`P(γ_j(W)) = E_j(γ(W))` **for each `j` separately** (the universal polynomials `E_j` with
`P(e_j) = E_j(e)`; the total-class identity alone is too weak — it lost the calibration case).
The needed conclusion is `γ_r(W) = 0`, i.e. `z·(b γ(V))_{2m} = 0`.

**Model test** (`scratch/lix_modp_fast.py` on MSI, lead, 2026-09-10; source in this session's
scratchpad `sp/`): with `p ∣ n`, the relations force `γ_r(W) = 0` at every stage tested;
with `p ∤ n` they generally do not, and the controls behave as Bott requires.

| n | p | d (stages) | forced? |
|---|---|---|---|
| 2 | 2 | [2], [2,4], [2,4,8] | yes (calibration: the existing proof) |
| 2 | 3 | [3], [] | **no** (must be no: Bott gives an allowable bundle with Chern number 2) |
| 3 | 3 | [3], [6], [3,6], [3,6,12] | yes |
| 3 | 2 | [2], [6] | no |
| 4 | 2 | [2], [4], [8] | yes |
| 4 | 3 | [3], [4], [4,8] | no |
| 5 | 5 | [5] | yes |
| 6 | 2 | [6], [12], [24], [6,12], [12,24] | yes |
| 6 | 3 | [6], [12], [24], [6,12], [12,24] | yes |
| 6 | 5 | [6] yes, [12], [6,12], [12,24] | **no** |
| 6 | 7 | [6], [6,12] | no (control: 7 ∤ 6!) |
| 7 | 7 | [7], [7,14], [14,28] | yes |
| 7 | 2,3,5 | [7,14] | no |
| 10 | 2,3,5 | [10,20] | yes |
| 10 | 7 | [10], [10,20] | no |
| 11 | 11 | [11], [11,22] | yes |

Conjecture the lanes must turn into a proof: **for every prime `p ∣ n` and every stage,
the relations force `γ_r(W) = 0`.**  The expected mechanism is the mod-2 one: `p ∣ d_i`
makes `γ(V) = ∏(1 + h_i^p)^{d_i/p}` supported in degrees `≡ 0 mod 2p` (Frobenius), and the
Wu relations read on the `z`-part, with instability, kill the coefficients `b` in the
complementary residues.  `sp-design` derives the uniform argument from the model's
certificates (print which relation kills which coefficient), states it as a finite list of
lemmas over an abstract `F_p`-algebra `H^*(Y)[z]/(z²)`, and model-tests every lemma.
A proof that works stage by stage but not uniformly is NOT acceptable: the limit needs
all stages.

### 1.5 Coefficients and operations (owners `sp-coeff`, `sp-steenrod`)

* The vendored cochain layer is generic in the coefficient ring
  (`ThirdParty/.../CupProduct.lean: singularCochainGroup (R : Type) [CommRing R]`);
  `cohomologyZMod2` is an `abbrev` specialisation.  `CharClass/CohomologyBasic.lean`'s
  `Hmod2` pins `ZMod 2`, and 230 `CharClass` files name `ZMod 2`.  The plan is a
  coefficient parameter `K` (a field, or `ZMod p` with `[Fact p.Prime]`) through the layers
  that never use `1 = -1`: cohomology basic/assoc/pull, Mayer–Vietoris, relative pairs and
  excision, Leray–Hirsch, Chern classes via Leray–Hirsch, projective bundles, Thom class,
  Gysin.  Correction (sp-coeff, 2026-09-10 12:20): graded commutativity IS provided at `F₂` (`SteenrodCupOne.cup_comm`,
  unsigned, all degrees; `ChernTotalRing`'s `GCommRing` instance rests on it) but is FALSE at odd `p`
  without the sign `(−1)^{|a||b|}`, so `TotalH` over `K` is a graded RING (`DirectSum.GRing`, dropping
  exactly the `mul_comm` field) and over `F₂` a graded commutative ring; any lemma that commutes two
  classes over `K` carries an even-degree hypothesis.  Chern classes have even degree, so every
  commutation the even side performs is sign-free under that hypothesis.  **Owned item (2026-09-10 12:35; reassigned 12:45 to the new lane `sp-cupone`, since twelve files
  consume `cup_comm` and it gates LerayHirsch*/Chern*/Projective*/the chart tower):** the
  signed cup-1 coboundary formula over `K` (the 2-fold case of `sp-steenrod`'s tuple model; align sign
  conventions with their `OddP*` files) and `cup_comm_of_even` — two classes commute when one has even
  degree — also in `TotalH` vocabulary (`IsEven` predicate closed under `+`, `*`, `map`).  This is the
  only commutativity the program consumes: Step D needs exactly `z ⌣ ι(r) = ι(r) ⌣ z` (both even);
  `sp-evenside` weakens `ParityPData` to `[Ring H]` plus one field `z_comm` after the batch lands, and
  `R = H^*(Y)` is even-concentrated (`CohomologyProjectiveParity`), so a `CommRing` on its even
  subring suffices there.  Split (12:50): `sp-coeff` owns the generic `TotalH` over `K`, the `IsEven`
  predicate and its bookkeeping lemmas (closure under `*` needs no commutativity: in odd total degree
  every term of a product has an odd factor); `sp-cupone` owns the signed coboundary formula,
  `cup_comm` signed, `cup_comm_of_even`, and the one declaration `TotalH.mul_comm_of_even`.  Even-
  concentration of `H^*(∏ CP^{d_i}; K)` is ring-free (its 53-module closure never reaches `cup_comm`),
  so once even elements commute the total ring of `Y` is commutative outright: no even subring needed.
  **Inter-lane sign contract (sp-steenrod, 12:50):** the tensor differential carries the LEFT factor's
  degree as its sign; the transposition carries the product of the degrees; evaluating a tensor of
  cochains against a tensor of chains carries no sign.  The signed cup-1 formula is NOT a by-product
  of the odd-primary tuple model (that diagonal is abstract; the cut construction is retired there),
  so `sp-cupone` ports the cut-index combinatorics with signs; calibrate with both degrees one and cut
  index one on a 3-simplex, where all four terms of the coboundary formula are distinguishable.  The `F₂` instance must keep
  building at every landing: the LIX answer is a verified artifact and stays green.
* The odd-primary Steenrod powers `P^i` at cochain level, with naturality, `P^0 = id`,
  Cartan formula (total `P` multiplicative), instability (`P^i = 0` below degree `2i`,
  `P^{q/2} = p`-th power on degree `q` even), `P(h) = h + h^p` on degree 2.  The `F₂` tree
  builds `Sq` from cup-`i` products (`SteenrodSquare.lean`) and the Cartan formula by acyclic
  models (`Cartan*.lean`); for odd `p` the cup-`i` route does not exist and the construction
  is the `ℤ/p`-equivariant diagonal approximation on the `p`-fold tensor power (the
  standard `W ⊗ C(X) → C(X)^{⊗p}` over the free `ℤ[ℤ/p]`-resolution `W`), from which `P^i`
  are the classes of `u^{⊗p}` paired with the generators of `W` in the right degrees, with
  the mod-`p` normalisation.  This is the hardest lane and it is on the critical path.
  `sp-steenrod` writes the construction plan first (which acyclic-models statements are
  needed, which the tree already has, what normalisation constant appears and why it is a
  unit mod `p`) and gets it reviewed by `sp-design` before authoring.
* **The normalisation constant (decided 2026-09-10).**  An abstract equivariant diagonal gives every
  axiom except `P^0 = id`, which is the value of a universal constant `c_q` (`Q^0 = c_q · id`),
  and no other axiom pins it (the pure Frobenius satisfies all of them with `c = 0`).  Its VALUE is
  irrelevant (κ-sweep: 0 of 28 cases depended on it; a rescaling `P'^i = κ^i P^i` preserves every
  axiom), so `P̃ := c_q^{-1} Q` on even degrees; only `c_2 ≠ 0` matters.  `c_1 = ((p−1)/2)!` by
  the descent on the 1-simplex, generic in `p` (cone contraction on slot 0, `DH + HD = 1`, every
  primitive is `H(A)`, final pairing with the Alexander–Whitney diagonal), and `c_2 = κ(1,1)·c_1²` from
  the Cartan comparison on the torus, where `κ(1,1)` is the Cartan coefficient at the top splitting
  (both `W`-indices `p−1`, twist summed) — NOT pinned by the degree-0 agreement (that is the counit and
  fixes only the empty top-index case).  (`sp-steenrod`'s "coefficient 1 in even degrees" lemma was RETRACTED
  the same day: it evaluated at the bottom corner, the counit case; the constants live at the top
  corner, so the higher even constants come from the Cartan identity at the top corner with the
  explicit coproduct, `c_{q+q'} = κ_top(q,q')·c_q·c_{q'}` with **`κ_top(q,q') = (−1)^{q q' (p−1)/2}`** (derived and verified
  2026-09-10 12:30: the reduced coproduct coefficient at that corner is always 1 since both `W`-indices
  `q(p−1)`, `q'(p−1)` are even, and the rest is the riffle sign; the evaluation reordering cancels),
  so even-degree multiplicativity holds (`κ_top = 1` when `q` or `q'` is even), the odd×odd case is
  `(−1)^{(p−1)/2}`, and **`c_{2k} = (−1)^k`**, a unit in every even degree.  Moreover `c_n = (−1)^K λ_n`
  with `λ_n` the coefficient of `[0..n]^{⊗p}` in `Φ(e_{n(p−1)} ⊗ ι_n)` (Fermat on any `n`-cycle), so
  every constant is read off the model simplex; `λ_1 = ((p−1)/2)!`.)  **Model caveat (sp-steenrod,
  12:55):** sp-design's descent contraction is written on the simplicial (face) model; the tower is
  SINGULAR.  Only the pairing VALUES transfer, not the top-degree-is-one-dimensional route.  Ruling: if
  "the final pairing is independent of the choice of primitives" is a theorem on singular cochains, use
  the abstract contraction from the splitting lemma; otherwise build the singular cone operator
  (`(t₀,t') ↦ (1−t₀)σ(t'/(1−t₀)) + t₀ v` on a convex target, `∂c + c∂ = id − ηε`), ~250 lines, absent
  from Mathlib at the pin, reusable by every contractible-model argument — approved in advance.  **Resolved (sp-design, 12:55): no cone needed.** The descent never leaves the two-letter complex
  `E⁰ = ⟨f⟩, E¹ = ⟨g⟩, δf = g`; a map from it into any cochain complex (singular or simplicial) is a
  choice of 0-cochain and is a chain map for free, and the differential, the cyclic action and the
  one-slot contraction all preserve its `p`-fold tensor power, so the computation is finite linear
  algebra in `2^p` words landing in the singular tensor power by functoriality.  Primitive-independence
  is a THEOREM (a perturbation changes the next element by a coboundary the following step absorbs and
  the `N·(T−1) = 0` step kills; only the last step's boundary term survives, which vanishes on `Δ¹`).
  The top-degree route is retracted; `c_1` comes from the model-free descent and the higher constants
  from the multiplicativity factor.
  **Settled 2026-09-10 ~11:50 CDT:**
  `sp-design` solved the resolution's coproduct in closed form (three cases, verified block by block) and
  the reduced (odd,odd) coproduct coefficient is `1` (the integral pair count `p(p−1)/2` dies mod `p`);
  with the riffle Koszul sign the full Cartan coefficient is `κ(1,1) = (−1)^{(p−1)/2}`, and building the
  equivariant diagonal `Φ` itself on the models (iterated Alexander–Whitney at `e_0`, chain-map
  recursion solved by the FULL tensor contraction) and evaluating on the fundamental class of the
  torus gives **`c_2 = −1` directly** for every odd `p` computed (3, 5, 7, 11), Wilson-consistent with
  `c_1 = ((p−1)/2)!`: `κ·c_1² = (−1)^{(p−1)/2}(−1)^{(p+1)/2} = −1`.  The constant is well defined on a
  CYCLE (torus), not on a simplex, which is why `Δ²` failed.  `sp-steenrod` therefore takes the
  coproduct EXPLICITLY (the abstract route creates the unknown, the explicit one retires it and also
  discharges the vanishing below the bottom of the range), states the bridge with its Künneth
  prerequisite (two distinct degree-one classes with nonzero product, a torus), and still runs the
  independent even-degree argument as a cross-check.  The lane has no unknown constant anywhere.  A descent on `Δ²` is NOT well
  defined (the primitive ambiguity pairs against `AW(∂σ)`, edges, not points) and must not be
  attempted.  The explicit `p`-fold interval-cut diagonal is not built.
* Wu relations for `P^i` on mod-`p` Chern classes follow from the splitting principle
  exactly as `Wu.HasSplitting` does at `F₂`; the universal polynomials `E_j` are the
  elementary symmetric functions of `y + y^p`.

### 1.6 The endpoint (owner: lead, then `sp-endpoint`)

`Analysis/LIXEndpointStatement.lean`'s `HasK1InjWitness` becomes a `k`-indexed family; the
C*-side bridge `LIXLemmaSixCor4.climb_genUnitary_notMem` becomes
`climb_genUnitary_pow_notMem (k) (hk : ¬ p ∣ k)`; `LemmaTwoHolds` becomes `LemmaTwoHolds n p k`
(`¬ ContinuousMvNEquiv (FHmat_k) EHmat` at every stage, `FHmat_k` built from `x ∘ Σψ_k`).
The Palomar surface is a third configuration `Palomar/comparator-lix-strong.json` with a
Mathlib-only challenge stating the `n = 6` corollary and the general theorem.
**Ratified 2026-09-10 12:40 (sp-design's draft, in their report under "Endpoint statements"):** new
namespace `ProblemLIXStrong`, new files `Palomar/LIXStrongChallenge.lean`/`LIXStrongSolution.lean`,
the shared block byte-identical to the existing surface (`cornerDiag`, `IsK1Injective` reused, not
copied); "`v ∉ U₀`" is the `k = 1` case of the power clause, not a separate conjunct; the stabilisation
clause is the existential over a path-component element whose matrix is `cornerDiag` (no `diagOne`);
the rank `n` enters the challenge only as a natural number in `p ∣ n` (never `Fin n`, no instance to
pin); pin `Fintype (Fin 2)` and the spectral order pair as now; do NOT pin the `CStarAlgebra` instance
on the limit and never let a second pi-instance exist (`Gen.instCStarAlgebraStageAlgebraPi n` must be
the one `inferInstance` finds); `NeZero n` is solution-side from `2 ≤ n`; land
`squarefree_dvd_of_forall_prime_dvd` separately (pure ℕ).

## 2. Lanes (all `model: opus`, named; resume with SendMessage to the name)

| lane | clone / cores | owns | first deliverable |
|---|---|---|---|
| `sp-design` | spare1 / 96-103 | this note §1.2–1.4 as theorems; every model test | uniform Step D proof for `p ∣ n`; `ψ_k` design; sign-off gate for the Lean lanes |
| `sp-tower` | cs-stages / 88-95 | `Analysis/LIX*` generic in `n`; ALSO the rank parameter in the `CharClass/LIX*` shape layer (VIdx, baseM, HIdx, Vmat, sProj/eProj, FHmat/EHmat, lixDD), as `Gen` namespaces with every old name kept as the `n = 2` specialisation; never the constant-section move or the Step C geometry files | `stageRank n i`, `Fproj n`, seam generator for `U(n+1) → S^{2n+1}`, `diag(u,1) ∈ U₀`, tower, limit, simplicity, separability at general `n` with the `n = 2` instance unchanged |
| `sp-coeff` | cs-endpoint / 64-71 | `CharClass` coefficient parameter | `Hmod K`, cup/pull/MV/relative/excision/LH/Chern/Thom/Gysin over a field `K`, `F₂` instance green |
| `sp-steenrod` | cs-limit / 72-79 | odd-primary `P^i` | construction plan reviewed, then the operations with Cartan + instability + `P(h) = h + h^p` |
| `sp-powers` | cs-simplicity / 80-87 | §1.3 items 1–3 | Eckmann–Hilton over `U(n)`, gauge lemma, clutching naturality along `Σψ_k` |
| `sp-evenside` | spare1 / 96-103 | Step D mod p: `CharClass/ParityP*`, `StepDModP*` | the uniform theorem of sp-design §3.2 as pure algebra generic in p (`ParityData` shape); later the bridge to real objects over sp-coeff's Chern classes and sp-steenrod's export |
| `sp-oddside` | spare2 / 104-111 | Step C with k zeros: `CharClass/LIXK*` | the F₂, n = 2 instance first (constant section at e₁, k equatorial zeros, excision splitting, `γ_r = k·c₀`); later over F_p (needs sp-coeff's relative homotopy invariance and generic sphere/contractible) and general n (needs sp-tower's Gen shape layer) |
| `sp-cupone` | thm-e / 112-119 | signed cup-1 product over `K`: `CharClass/CupOne*` | the cup-1 coboundary formula with signs over any commutative ring (2-fold case of sp-steenrod's tuple model, same sign conventions), `cup_comm` signed and `cup_comm_of_even`, `TotalH.IsEven`/`mul_comm_of_even`; unblocks LerayHirsch*/Chern*/Projective*/Chart tower over `K` (12 files consume `SteenrodCupOne.cup_comm`) |
| later: `sp-endpoint` | | §1.6 | after both sides are green; statements drafted by `sp-design` ("Endpoint statements") |

Ownership is by file: a lane creates files under its own prefix and edits existing files
only when the table says it owns them.  Two lanes never edit one file; ask the lead.

## 3. Protocol (binding)

* **Lean only after solving.**  No Lean is authored for a statement whose proof is not
  written in this note or in the lane's report at the precision of a lemma list, and
  model-tested where it is numeric.  `sp-design` gates §1.2–1.4.
* **Builds.**  `scratchpad sp/laneprobe.sh <clone> <Module...>` (path given in the launch
  message): syncs the shared local tree into the lane's private warm clone on MSI and builds
  there on the lane's 8-core range under `nice`.  Never build locally.  Never use another
  lane's clone.  Never use `/tmp` on the node.  Do not start a second probe while one runs
  (the helper serialises with `flock`; queueing is wasted wall-clock).  A probe that takes
  more than 15 minutes is a signal to cut the import closure, not to wait.  Grep
  `notes/lix-lane-reports/FLEET_TRAPS.md` BEFORE the first probe (deprecation traps cost a whole
  probe for zero mathematical content), not only before a second failed one.
* **Built, never Replayed (fleet rule, 2026-09-10).**  Every module you are CLAIMING green must show
  `✔ [k/N] Built GroupApproximation.X (Ns)` in the log you cite; a `Replayed` line on a module you
  edited is a false green and the probe is FAILED; lake prints nothing for an up-to-date target, so
  "no Replayed line" is not evidence.  The standard way to produce the citable log is to delete your
  own modules' remote `.olean/.ilean/.trace` in your clone and re-probe once, so one log carries every
  Built line.  Second tell: an unmoved job count across a structural change means no rebuild.
  Clones hold REAL copies of artifacts (never hard links: lake writes in place and shared inodes
  corrupt every other tree); warming is artifacts-only and holds the probe lock.
  **Stale oleans (sp-oddside, 2026-09-10 12:05):** the main tree's copied artifacts include oleans
  OLDER than their sources (233 of 5478 modules) and lake replays them with no log line, so a probe
  can build against an import whose olean does not match its source (the symptom is a red in a
  correct file, e.g. names defined in a new import "unknown").  `laneprobe.sh` therefore purges,
  under the lock and before every build, every artifact set whose `.lean` is newer than its
  `.olean`, and prints `purged N stale artifact sets`; a probe run before this patch whose closure
  imports a module edited today must be re-run before it is cited.
  The dangerous case is a module that is SILENT in the log (neither `Built` nor `Replayed`): lake
  trusted a trace over a stale olean, and the importers elaborated against an environment that
  does not match the sources.  It cuts both ways (a false red when a new name is missing, a false
  green when the stale olean still elaborates).  So: absence of a module you touched from the log
  is a FAILURE, not "not yet reached"; preserving copies preserve the problem; and the definitive
  reset is to clear every artifact of the directory you are rewriting before the probe.
  Never purge or delete artifacts while a probe is running in that clone (sp-oddside): lake keeps
  building the other jobs and the log fills with `failed to open file '….olean'` on modules that are fine.
  **The purge is TRANSITIVE (sp-oddside, 13:00):** a module whose own source is untouched but whose
  IMPORT was rebuilt today is replayed from an olean compiled against the old import (SteenrodCupOne
  from 09-05 over a CohomologyBasic rebuilt at 12:10 produced the `cup_comm a b : cup = cohCast` red
  that looked like sp-coeff's code).  `laneprobe.sh` now runs `cc_clones/purge_stale.py` under the
  lock before every build: to a fixpoint, delete every artifact set whose source is newer than its
  olean, or whose olean predates the olean of any `GroupApproximation` module it imports, or whose
  import has no olean; bounded to the library.  First use costs one large rebuild per clone
  (spare1 dry run: 2876 of 4823 oleans); that is the price of a green that means something.
* **No `sorry` lands.**  Author with `sorry` only inside a file that is not imported by
  anything, and say so in the report.  `#print axioms` on every endpoint-facing theorem:
  `[propext, Classical.choice, Quot.sound]`, nothing else, ever.
* **Statements before proofs.**  Land the statement of each obligation as a `Prop` with a
  docstring saying who discharges it, then discharge.  A hypothesis used once is an over-ask.
* **Landing.**  Lanes do not commit or push.  The lead commits and pushes the shared tree
  regularly; a lane's report says which files are green and at which job count.  A landing batch
  must be green AS A TREE STATE: because lanes share one working tree and every probe rsyncs all
  of it, a lane whose files are mid-edit (a half-applied rename, a missing import) turns every
  other lane's gate red in its own directory.  So a lane keeps the shared tree in a consistent
  state between its own probes (do renames in one step; stage a new layer in new files), and
  the lead lands the union of the lanes whose closures were gated green together.
* **Reports.**  `notes/lix-stronger-lane-reports/<lane>.md`, four sections (GREEN with job
  counts / AUTHORED, UNVERIFIED / NEEDS / TRAPS), kept current.  Cross-lane traps go to
  `notes/lix-lane-reports/FLEET_TRAPS.md` (append only).  Read it before a second failed
  probe on the same error.
* **MSI.**  8 cores per lane, `nice -n 5`, warm clones only, no job spam, kill hung `lake`
  processes you started (`pkill -u sauer354 -f "lake build <your module>"`), never touch
  other users' processes.
* **Idiom.**  `notes/lix-lane-reports/FLEET_TRAPS.md` and the memory files named in the
  launch message are the accumulated Lean traps of this tree; the mod-2 files are the
  template for every construction.
