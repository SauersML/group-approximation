# Problem 1.21: fibred groups, antipodal BNSR pairs, retracts and free products

Lane `swarm-zaremsky-1-21-g-times-z-type-f`, 2026-09-16.

- Root: `zaremsky-1-21-g-times-z-type-f-implies-g-type-f`.
- Hole worked: `f-infinity-groups-of-finite-cd-are-of-type-f`.

A **counterexample** below means a group `G` of type `F_∞` with `cd G < ∞`
that is not of type F. The hole says there is none.

The results below are standard Bass–Serre and BNSR bookkeeping, and no
novelty is claimed. Their purpose is to restrict what a counterexample can
look like, and to name the retract form of the hole.

## 0. Conventions and imported facts

`K_0(ZG)` is the projective class group, and `K̃_0(ZG) = K_0(ZG)/Z·[ZG]`.
For a group `G` of type FP with a finite projective resolution `P_* → Z`:

- the **K_0 Euler class** is `χ_G = Σ_i (−1)^i [P_i] ∈ K_0(ZG)`;
- the **Wall class** `σ(G)` is the image of `χ_G` in `K̃_0(ZG)`;
- the **Euler characteristic** is `e(G) = ε_*(χ_G) ∈ K_0(Z) = Z`, where
  `ε: ZG → Z` is the augmentation.

Both `χ_G` and `σ(G)` are independent of the resolution (generalized Schanuel
lemma). This matches `fp-type-fp-group-is-type-f-iff-wall-class-vanishes`.

For a subgroup `H ≤ G`, `ind = ind_H^G = ZG ⊗_{ZH} −`. It is exact, because
`ZG` is a free right `ZH`-module on a set of left coset representatives. It
carries f.g. projectives to f.g. projectives and so induces
`ind: K_0(ZH) → K_0(ZG)`.

Standard facts (S1)–(S5) are those listed in
`g-times-z-type-f-iff-g-f-infinity-with-finite-cd-proof`:

- (S1) for `n ≥ 2`, `F_n` = finitely presented + `FP_n`;
- (S2) FP = `FP_∞` + finite cd. More precisely, `FP_d` + `cd ≤ d` gives FP;
- (S3) the Eilenberg trick: an Euler class in `Z·[ZG]` gives FL;
- (S4) finitely presented + FL gives F;
- (S5) the Bieri–Eckmann criterion.

Further imports:

- **(T1) Bass–Serre.** A group `G` acting on a tree `T` without inversions
  has an exact sequence of `ZG`-modules
  `0 → Z[E(T)] --∂--> Z[V(T)] --ε--> Z → 0`. Here `∂(e) = t(e) − o(e)`, and
  `Z[E] = ⊕_{orbits} Z[G/G_e]`, `Z[V] = ⊕_{orbits} Z[G/G_v]`. The sequence is
  exact because `T` is contractible. (Serre, *Trees*; Brown VII.9 or VIII.)
- **(T2) Comparison theorem.** A module map `M' → M` lifts to a chain map from
  any nonnegative projective complex augmented to `M'` to any resolution of
  `M`.
- **(T3) Openness.** For `G` of type `F_m`, `Σ^m(G)` is open in the character
  sphere `S(G)`. This is stated with [BNS87, Ren88] in M. Ershov and
  M. C. B. Zaremsky, *Dense and empty BNSR-invariants of the McCool groups*,
  arXiv:2505.18826, §2, fetched and read 2026-09-16.
- **(T4) Renz, Satz C.** Stated as Theorem 2.3 of arXiv:2505.18826, read
  2026-09-16. For `G` of type `F_m` and a discrete character
  `0 ≠ χ: G → R`, `ker χ` is of type `F_m` iff `[χ], [−χ] ∈ Σ^m(G)`.
- **(T5) Bieri–Renz.** For `G` of type `FP_m`, `Σ^m(G;Z)` is open, and for
  discrete `χ`, `ker χ` is `FP_m` iff `[±χ] ∈ Σ^m(G;Z)`. Source: R. Bieri and
  B. Renz, Comment. Math. Helv. 63 (1988). This is recalled and was not
  fetched in this lane. It is the same import used by the established
  `nonzero-euler-characteristic-blocks-symmetric-sigma-proof`. Remark 3.2 of
  arXiv:2505.18826 (read 2026-09-16) says their Proposition 3.1 argument
  "applies equally well to the homological BNSR-invariant", which is
  consistent with (T5).

## 1. The Euler class of a graph of FP groups

**Theorem A′ (sum formula).** Let `G` act on a tree `T` without inversions,
with finitely many orbits of vertices and edges. Choose orbit
representatives `v ∈ V_0` and `e ∈ E_0`, and suppose every stabilizer `G_v`,
`G_e` is of type FP. Then `G` is of type FP,
`cd G ≤ 1 + max(cd G_v, cd G_e)`, and

```text
χ_G = Σ_{v∈V_0} ind_{G_v}^G χ_{G_v} − Σ_{e∈E_0} ind_{G_e}^G χ_{G_e}   in K_0(ZG).
```

*Proof.*

1. For each representative choose a finite projective resolution
   `P^v_* → Z` over `ZG_v`, and `P^e_* → Z` over `ZG_e`.
2. `A_* = ⊕_e ind P^e_*` resolves `Z[E]`, and `B_* = ⊕_v ind P^v_*` resolves
   `Z[V]`. These are resolutions because `ind` is exact and
   `ind_{G_x}^G Z = Z[G/G_x]`. Both are finite complexes of f.g. projective
   `ZG`-modules.
3. By (T2), `∂: Z[E] → Z[V]` lifts to a chain map `f: A_* → B_*`.
4. Let `C = Cone(f)`, with `C_n = A_{n−1} ⊕ B_n` and
   `d(a,b) = (−d a, f(a) + d b)`. The short exact sequence
   `0 → B_* → C_* → A_{*−1} → 0` gives the long exact sequence
   `… → H_n(B) → H_n(C) → H_{n−1}(A) --f_*--> H_{n−1}(B) → H_{n−1}(C) → …`.
5. Here `H_*(A)` and `H_*(B)` are concentrated in degree 0, where they are
   `Z[E]` and `Z[V]`, and `f_* = ∂` there. So:
   - `H_n(C) = 0` for `n ≥ 2`;
   - `H_1(C) = ker ∂ = 0` ((T1): `∂` is injective);
   - `H_0(C) = coker ∂ = Z` ((T1): `ε` induces the isomorphism).
6. So `C_* → Z` is a finite resolution by f.g. projective `ZG`-modules of
   length `≤ 1 + max` of the lengths. Hence `G` is FP and `cd G` is bounded as
   stated.
7. In `K_0(ZG)`, `Σ_n (−1)^n [C_n] = Σ_n (−1)^n [B_n] − Σ_m (−1)^m [A_m]`,
   which is the displayed formula. ∎

Sanity checks:

- **Free product** `A * B` (`V_0 = {A, B}`, `E_0 = {1}`):
  `χ = ind χ_A + ind χ_B − [ZΓ]`. For `F_2 = Z * Z` this gives
  `e = 0 + 0 − 1 = −1`. Correct.
- **Genus-two surface group** `F_2 *_Z F_2`: `e = (−1) + (−1) − 0 = −2`.
  Correct.
- **`BS(1,n) = Z*_{×n}`:** `e = 0 − 0 = 0`. Correct.

**Theorem A (ascending HNN extensions).** Let `B` be of type FP, let
`φ: B → B` be an injective endomorphism, and let
`G = B*_φ = ⟨B, t | t b t⁻¹ = φ(b), b ∈ B⟩`. Then:

- `G` is of type FP with `cd G ≤ cd B + 1`;
- `χ_G = 0` in `K_0(ZG)`, so `σ(G) = 0` and `e(G) = 0`;
- `G` is of type FL;
- `G` is of type F iff `G` is finitely presented. This holds for instance
  when `B` is finitely presented, but `B` need not be.

*Proof.*

1. **The tree.** The Bass–Serre tree of the HNN extension has vertex set
   `G/B` and edge set `G/B`. The edge `gB` joins `gB` to `gt⁻¹B`. This is
   well defined because `gbt⁻¹B = gt⁻¹φ(b)B = gt⁻¹B`. The stabilizer
   inclusion is right: `tBt⁻¹ = φ(B) ⊆ B`, so `B ⊆ t⁻¹Bt`.
2. **One orbit each.** There is one orbit of vertices with stabilizer `B`,
   and one orbit of edges with stabilizer `B` (the same subgroup of `G`). So
   Theorem A′ gives `χ_G = ind χ_B − ind χ_B = 0`.
3. **Directly.** The sequence is
   `0 → Z[G/B] --∂--> Z[G/B] → Z → 0` with `∂(gB) = gt⁻¹B − gB`. The cone of a
   lift `f: ind P_* → ind P_*` of `∂` has `C_n = ind P_{n−1} ⊕ ind P_n`, whose
   alternating sum telescopes to `0`.
4. **FL.** By (S3), a finite projective resolution with Euler class
   `0 ∈ Z·[ZG]` can be converted into a finite free one, so `G` is FL.
5. **Type F.** If `G` is finitely presented, then (S4), or equivalently
   `fp-type-fp-group-is-type-f-iff-wall-class-vanishes` with `σ(G) = 0`, makes
   `G` of type F. Conversely, type F implies finitely presented. If `B` has a
   finite presentation `⟨X | R⟩`, then
   `⟨X, t | R, t x t⁻¹ = φ(x) (x ∈ X)⟩` presents `G`. ∎

**Corollary A1 (fibred groups).** Let `G` be finitely presented, and suppose
some epimorphism `χ: G → Z` has kernel `N` of type FP. Then `G` is of type F,
with `χ_G = 0` and `cd G ≤ cd N + 1`.

*Proof.* Pick `t` with `χ(t) = 1`. Then `G ≅ N ⋊_α Z`, where `α` is
conjugation by `t`. This is the HNN extension `N*_α` with `α` an
automorphism, and Theorem A applies. ∎

Sanity checks:

- **`φ = id`:** `G = B × Z`. This recovers
  `g-times-z-type-f-iff-g-f-infinity-with-finite-cd` (3)⇒(1).
- **Bestvina–Brady kernels.** For a flag complex `L` that is acyclic but not
  simply connected, `BB_L` is FP and not finitely presented, while the right-angled Artin group
  `A_L = BB_L ⋊ Z` is finitely presented. Theorem A says `A_L` is of type F,
  which is true (Salvetti complex). This shows the base need not be finitely
  presented.
- **Topological form.** This is the algebraic shadow of the mapping-torus
  identity `T(d∘s) ≃ T(s∘d)` and the Siebenmann sum theorem, both recalled in
  S. Ferry and A. Ranicki, *A survey of Wall's finiteness obstruction*,
  arXiv:math/0008070, Proposition 1.5 (read 2026-09-13 and 2026-09-16).

## 2. Antipodal BNSR pairs force type F

**Theorem B.** Let `G` be of type `F_∞` with `cd G = d < ∞`, `d ≥ 1`. Suppose
`Σ^d(G;Z) ∩ −Σ^d(G;Z) ≠ ∅`. This holds, for example, if
`Σ^d(G) ∩ −Σ^d(G) ≠ ∅`, or if `Σ^∞(G) ∩ −Σ^∞(G) ≠ ∅`. Then:

- `G` is of type F;
- `χ_G = 0` in `K_0(ZG)`;
- `G` fibres: some epimorphism `G → Z` has a kernel of type FP.

*Proof.*

1. **An open set.** Let `U = Σ^d(G;Z) ∩ −Σ^d(G;Z)`. It is nonempty by
   hypothesis. It is open by (T5), because the antipodal map is a
   homeomorphism of `S(G)`. In the homotopical variant, use (T3) with
   `Σ^d(G)`.
2. **A discrete character.** `G` is finitely generated, so `Hom(G,R) ≅ R^r`
   with rational structure `Hom(G,Q)`. The open cone over `U` contains a
   rational vector. Scale it to `χ: G → Z` with `χ(G) = Z` and `[χ] ∈ U`.
3. **The kernel is FP.** Let `N = ker χ`. By (T5), `N` is of type `FP_d`. In
   the homotopical variant, (T4) makes `N` of type `F_d`, hence `FP_d`.
4. **FP from `FP_d`.** `cd N ≤ cd G = d`. Take a free resolution `F_* → Z`
   over `ZN` with `F_0, …, F_d` finitely generated. Let
   `K = ker(F_{d−1} → F_{d−2})`. Then `Ext^1(K, M) ≅ H^{d+1}(N;M) = 0` for all
   `M`, so `K` is projective. `K = im(F_d)` is finitely generated. So
   `0 → K → F_{d−1} → … → F_0 → Z → 0` is a finite projective resolution and
   `N` is FP. This is (S2).
5. **Conclusion.** `G` is finitely presented by (S1), since it is `F_∞`.
   Corollary A1 gives type F and `χ_G = 0`. ∎

**Corollary B1 (shape of a counterexample).** Let `G` be a counterexample,
with `d = cd G`. Then:

1. `Σ^d(G;Z) ∩ −Σ^d(G;Z) = ∅`. Hence `Σ^m(G) ∩ −Σ^m(G) = ∅` for every
   `m ≥ d`, and `Σ^∞(G) ∩ −Σ^∞(G) = ∅`.
2. No epimorphism `G → Z` has a kernel of type FP.
3. `G` is not an ascending HNN extension over any base of type FP.
4. If some automorphism `α` of `G` acts on `Hom(G,R)` as `−1`, then
   `Σ^d(G;Z) = ∅`. Such an `α` exists, for example, when `G` has an
   automorphism inverting every generator of its abelianization. This uses
   `Aut(G)`-invariance of `Σ^m`, stated in arXiv:2505.18826 §2 for the
   homotopical invariant. For the homological invariant the proof is the
   same, since the invariant does not depend on the choice of complex.
5. If `G` acts on a tree cocompactly without inversions, with all vertex and
   edge stabilizers of type FP, then
   `Σ_v ind σ(G_v) ≠ Σ_e ind σ(G_e)` in `K̃_0(ZG)` (Theorem A′).

Theorem B is related to two existing results:

- **Ershov–Zaremsky Proposition 3.1** (arXiv:2505.18826). For `G` of type F
  with `e(G) ≠ 0`, `Σ^∞(G) ∩ −Σ^∞(G) = ∅`. The same argument under Theorem B's
  hypotheses shows more: for an `F_∞` group of finite cd, an antipodal pair
  kills the whole class `χ_G ∈ K_0(ZG)` and gives a finite `K(G,1)`, not just
  `e(G) = 0`.
- **`nonzero-euler-characteristic-blocks-symmetric-sigma`** is the
  `e(G) ≠ 0` contrapositive for type F groups. Theorem B covers every `F_∞`
  group of finite cd, and its obstruction is `σ(G)` rather than `e(G)`.

**Where the one-sided version dies.** A single class `[χ] ∈ Σ^d(G)` with `χ`
discrete does not give a fibration. For `m = 1`, [BNS87] (recalled) makes
`G` an ascending HNN extension with a finitely generated base. For `m ≥ 2` no
verified statement produces a base of type `FP_m`, and Theorem A needs an FP
base. Novikov-ring versions of `K̃_0` would be the natural tool, but no
injectivity statement for `K̃_0(ZG) → K̃_0(\widehat{ZG}_χ)` is available.

## 3. The retract form of the hole

**Theorem C.** The following are equivalent:

1. every group of type `F_∞` with finite cd is of type F (the hole);
2. every retract of a group of type F is of type F. A retract here means
   homomorphisms `i: G → Γ` and `r: Γ → G` with `r∘i = id_G`.

**Lemma C0.** A retract `G` of a group `Γ` of type F is finitely presented and
of type FP, hence of type `F_∞` with finite cd.

*Proof.* This is the (1)⇒(3) argument of
`g-times-z-type-f-iff-g-f-infinity-with-finite-cd-proof`, which uses only
`r∘i = id`.

1. **Finite presentation.** Let `Γ = ⟨X | R⟩` be finite and `e = i∘r`, an
   idempotent endomorphism with `ker e = ker r`. Let `N` be the normal closure
   of `{x⁻¹e(x) : x ∈ X}`.
   - `N ⊆ ker e`, because `e(x⁻¹e(x)) = e(x)⁻¹e(x) = 1`.
   - The set `S = {g : g⁻¹e(g) ∈ N}` contains `X`. It is closed under
     products, since `(gh)⁻¹e(gh) = h⁻¹(g⁻¹e(g))h · h⁻¹e(h)`. It is closed
     under inverses, since `g e(g)⁻¹ = g(g⁻¹e(g))⁻¹g⁻¹`. So `S = Γ`.
   - For `g ∈ ker e`, `g⁻¹ = g⁻¹e(g) ∈ N`.

   So `G ≅ Γ/ker r = ⟨X | R, x⁻¹e(x) (x ∈ X)⟩`.
2. **`FP_∞`.** For a family `(M_λ)` of `ZG`-modules, `r^*` commutes with
   products. The maps `i_*: H_k(G;M) → H_k(Γ;r^*M)` and
   `r_*: H_k(Γ;r^*M) → H_k(G;M)` are natural and compose to the identity. So
   the Bieri–Eckmann comparison map (S5) for `G` is a retract of the one for
   `Γ`, and `G` is `FP_∞`.
3. **Finite cd.** `cd G ≤ cd Γ < ∞`, because `i` is injective.
4. **Conclusion.** (S2) gives FP, and (S1) gives `F_∞`. ∎

*Proof of Theorem C.*

- **(1)⇒(2).** By Lemma C0, a retract of a type F group is `F_∞` with finite
  cd. Then (1) applies.
- **(2)⇒(1).** Let `G` be `F_∞` with finite cd. By the established
  `g-times-z-type-f-iff-g-f-infinity-with-finite-cd`, `G × Z` is of type F.
  `G` is a retract of it via `g ↦ (g,0)` and the projection. (2) makes `G` of
  type F. ∎

Topological reading. A retract `G` of a type F group `Γ` has a finitely
dominated `K(G,1)`. Realize `i` and `r` by maps `f: Y → X` and `h: X → Y`
between aspherical complexes, with `X` finite. Then `h∘f` induces `id` on
`π_1`, so it is homotopic to `id_Y`. So (2) is "finitely dominated aspherical
complexes are homotopy finite", which is already listed in the hole. The same
argument shows that direct factors of type F groups are the same test class.

**Where attempts on (2) die.**

- **Pushing a resolution along `r`.** For a finite free resolution
  `C_* → Z` over `ZΓ`, the complex `ZG ⊗_{ZΓ} C_*` (via `r`) consists of
  finite free `ZG`-modules. Its homology is `H_*(ker r; Z)`, not `Z`, so it
  is not a resolution unless `ker r` is acyclic.
- **Pushing classes along `r`.** `r_*: K_0(ZΓ) → K_0(ZG)` is defined on
  classes, but `σ(Γ) = 0` says nothing about `σ(G)`, because `σ(G)` is not
  `r_*σ(Γ)`.
- **`Γ = K ⋊ G` with `K` of type F.** A product formula of the form
  `σ(Γ) = e(K)·ind σ(G)` would at best give the conclusion when `e(K) = ±1`.
  For `K = Z`, `e = 0`, and this is exactly the original difficulty.

## 4. Free products and one-ended reduction

**Proposition D.** Let `Γ = A * B`.

1. `Γ` is of type F iff `A` and `B` are of type F.
2. If `A` and `B` are finitely presented of type FP, then `Γ` is too, with
   `σ(Γ) = ind σ(A) + ind σ(B)` in `K̃_0(ZΓ)`.

*Proof.*

1. **Formula.** Theorem A′ with one edge orbit (stabilizer 1) gives
   `χ_Γ = ind χ_A + ind χ_B − [ZΓ]`. `Γ` is finitely presented: take the
   union of finite presentations of `A` and `B` on disjoint generating sets.
2. **Retractions.** Let `r_A: Γ → A` kill `B`. Then
   `(r_A)_* ∘ ind_A = id` on `K_0(ZA)`, so `ind_A` is injective.
3. **Other factor.** `(r_A)_* ind_B [P]` is induced along the trivial map
   `B → A`. It equals `ZA ⊗_Z (Z ⊗_{ZB} P)`, which is free, so it lies in
   `Z·[ZA]`. Hence `(r_A)_* σ(Γ) = σ(A)` in `K̃_0(ZA)`, and likewise for `B`.
4. **Type F.** If `Γ` is of type F, then `A` and `B` are retracts, so they are
   finitely presented of type FP (Lemma C0). `σ(A) = (r_A)_*σ(Γ) = 0` and
   likewise `σ(B) = 0`, so both are of type F by
   `fp-type-fp-group-is-type-f-iff-wall-class-vanishes`. The converse is the
   formula. ∎

**Corollary D1.** If a counterexample `G` exists:

1. `G * H` is a counterexample for every nontrivial type F group `H`, with
   `cd = max(cd G, cd H)`. In particular `G * Z^k` has `cd = max(d, k)`, so the
   set of cohomological dimensions of counterexamples is upward closed.
2. `G × F_2` is a counterexample of `cd d+1`, by
   `g-times-h-of-type-f-iff-euler-char-of-h-kills-wall-class` with
   `e(F_2) = −1`.
3. The least `cd` of a counterexample is at least 2. Groups of `cd ≤ 1` are
   free (Stallings–Swan).
4. **One-ended reduction.** Some free factor of `G` in a Grushko
   decomposition is a counterexample of `cd ≤ d`, and it is one-ended. Since
   `G` is torsion-free, its Grushko factors are one-ended or `Z`. If all were
   of type F, Proposition D, applied inductively, would make `G` of type F.
   The factors are retracts of `G`, hence finitely presented of type FP with
   finite cd.
5. **`cd = 2`.** A counterexample `G` of `cd 2` with a presentation complex
   `X` has `σ(G) = −[π_2 X]`: `π_2 X = H_2(X̃)` is f.g. projective, and the
   resolution `0 → im(C_2 → C_1) → C_1 → C_0 → Z` gives the sign. So a `cd 2`
   counterexample is the same as a finite presentation of a `cd 2` group
   whose `π_2` is projective but not stably free.

**Remark (splittings over type F edge groups; recalled, not re-verified).**

- **Vertex groups.** If a counterexample `G` splits as a finite graph of
  groups with edge groups of type F, the vertex groups are of type FP: the
  established `fp-n-splittings-over-fp-n-edges-have-fp-n-vertex-groups`, plus
  finite cd. They are finitely presented, by the standard fact that
  finitely presented groups split over finitely generated edge groups with
  finitely presented vertex groups. That fact is recalled, not re-derived
  here.
- **Consequence.** Theorem A′ gives
  `σ(G) = Σ_v ind σ(G_v) − Σ_e ind σ(G_e) = Σ_v ind σ(G_v)`. So some vertex
  group has `σ(G_v) ≠ 0` and is itself a counterexample.

## 5. What remains

None of this touches a group that does not fibre, or does not split with FP
pieces whose classes cancel. The general hole is still equivalent to
`σ(G) = 0` for every finitely presented group of type FP. That is the finitely
presented case of Serre's conjecture FP ⇒ FF (W. Lück, survey,
arXiv:2507.11337v1, Conjecture 2.4, read 2026-09-16). A counterexample would
refute the Farrell–Jones prediction `K̃_0(ZG) = 0` for torsion-free `G`
(same survey, Conjecture 2.1).

The obstructions above say a counterexample:

- is one-ended;
- does not fibre over `Z` with an FP fibre;
- has no antipodal pair in its high BNSR invariants;
- has no FP tree decomposition with cancelling classes.

Status of Problem 1.21, checked 2026-09-16:

- still posed in Zaremsky's list (version of July 12, 2026);
- I. J. Leary, arXiv:1512.06609v4: "No examples are known that distinguish
  between the properties FP(Z), FL(Z) and FH(Z)";
- no 2024–2026 arXiv source found resolving it.
