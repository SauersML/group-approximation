# Păunescu's class 𝒮 is a measure equivalence invariant

Lane `ex-nonsofic-action-entropy`, 2026-09-12. Handwritten proofs, nothing run.
Supports `cordeiro-sofic-relation-permanence`, `sofic-free-actions-are-soe-invariant`
and `paunescu-class-is-measure-equivalence-invariant`. Status of the new results:
proved here, unreviewed.

## 0. Sources read from the PDFs (2026-09-12)

* **L. Păunescu**, *On sofic actions and equivalence relations*, arXiv:1002.0605
  (J. Funct. Anal. 261 (2011)). HTML fetch of the arXiv version:
  Definition 1.12 (*"An equivalence relation E is called sofic if there is an
  embedding of M(E) in some Π_{k→ω} M_{n_k} such that A ⊂ Π D_{n_k} and
  𝒩(A) ⊂ 𝒰(A)·Π P_{n_k}"*), Definition 1.13 (*Θ is sofic if Θ(A) ⊂ Π D_{n_k} and
  Θ(u_θ) ∈ Π P_{n_k} for every θ ∈ [E]*), Example 1.11 (for a free action,
  `L^∞(X) ⋊ G ≅ M(E_α)`), and Proposition 1.15 (*"Let α be a free action. Then E_α
  is a sofic equivalence relation if and only if α is a sofic action."*), which
  agrees verbatim with `free-nonsofic-action-sources-verified-2026-09-11.md`.
* **L. Cordeiro**, *An elementary approach to sofic equivalence relations*,
  arXiv:1608.05608v2, PDF pages 1 to 11.
  * p. 3, Definition 2.1 (Ozawa): *"R is sofic if for each finite subset K ⊆ [[R]]
    and each ε > 0, there exists N ∈ ℕ and π : [[R]] → [[N]] satisfying:
    (i) π(id_X) = 1_[N]; π(∅) = ∅; (ii) For all φ, ψ ∈ K,
    d_#(π(φψ), π(φ)π(ψ)) < ε; (iii) For all φ ∈ K,
    |μ({x : φ(x) = x}) − μ_#({m : π(φ)(m) = m})| < ε."* And: *"condition (i)
    above is unnecessary."*
  * p. 3, Theorem 2.2: *"R is sofic if and only if [[R]] embeds isometrically in
    Π_𝒰[[n_k]]. In fact, an embedding Φ : M → Π_𝒰[[n_k]] from any sub-inverse
    semigroup M of [[R]] containing 1_X is isometric if and only if it preserves
    the trace."* Its proof records
    `d_μ(f,g) = tr(1_dom f) + tr(1_dom g) − tr(1_dom f 1_dom g) − tr(f^{-1} g 1_dom f)`.
  * p. 4, Remark: *"If {R_n}_n is an increasing sequence of sofic equivalence
    relations, then R = ∪ R_n is also sofic."*
  * p. 5, Remark after Proposition 2.4: *"The description of soficity above is
    equivalent to the existence of a sofic embedding of vN(R) of R, as defined in
    [11], in which it is proven that this coincides with the original definition of
    soficity by Elek and Lippner."* Reference [11] (p. 11) is Păunescu, J. Funct.
    Anal. 261 (2011).
  * p. 6, Proposition 3.2: *"(a) If R is sofic and A ⊆ X is any (non-null) subset,
    then R|_A is sofic. (b) If {A_n}_n is a countable Borel partition of X by
    (non-null) R-invariant subsets, then R is sofic if and only if each R|_{A_n} is
    sofic."* Here `R|_A` carries the normalized measure `μ_A`.
  * p. 7, Theorem 3.4: *"Suppose R ⊆ S is of finite index and admits invertible
    choice functions (e.g. R is ergodic). If R is sofic, so is S."*
  * p. 8, Corollary 3.5: *"Each hyperfinite (amenable) equivalence relation R is
    sofic."* Theorem 3.6: *"(X, μ, R) and (Y, ν, S) are sofic if and only if
    (X × Y, μ × ν, R × S) is sofic."*
* **A. Alpeev**, *Weak containment and maximal sofic approximations*,
  arXiv:1706.01864v1, PDF pages 1 to 12.
  * p. 2: *"It is a folklore fact that an action weakly contained in the sofic
    action is sofic itself."* Theorem 4.2 (p. 2 summary): products of sofic
    actions are sofic.
  * p. 10, Theorem 5.1: *"Class of treeable groups is subset of 𝒮."* Theorem 5.2:
    *"Class 𝒮 is closed under taking subgroups."* (Proof by co-induction.)
* **L. Bowen, P. Burton**, *Locally compact sofic groups*, arXiv:2106.09118v3,
  PDF pages 1 to 5 and 26 to 31. Theorem 3.9 (p. 3 summary): *"If G admits a sofic
  lattice subgroup then G is sofic."* Open Problems 1 to 19 (pp. 26 to 31): none
  concerns 𝒮 or measure equivalence of discrete groups.

**Credit note.** Part 1 of `sofic-action-class-closed-under-commensurability`
(subgroups) is Alpeev's Theorem 5.2 (2017), proved there by the same co-induction.

**Bounded novelty check.** Four web searches and the four papers above. No
statement that 𝒮 is invariant under measure equivalence or under stable orbit
equivalence of the acting groups was found. This may be folklore; the proof below
is complete either way.

## 1. Conventions and the two definitions of a sofic relation

Relations are countable Borel and measure preserving. For a finite measure space
`(W, m)` "sofic" refers to the normalized measure. A p.m.p. action is sofic in
Păunescu's sense (Definition 1.4 = Kun--Thom Definition 2.2).

*Agreement of Păunescu 1.13 with Cordeiro 2.1.* Given Θ as in 1.13, write
`φ ∈ [[R]]` as `φ = ∨_n g_n 1_{A_n}` with `g_n` in a countable group generating `R`
(Feldman--Moore) and `A_n` a partition of `dom φ`. Then
`Θ(v_φ) = Σ_n Θ(u_{g_n}) Θ(1_{A_n})` is an orthogonal sum of partial permutations,
hence a partial permutation of the ultraproduct (the argument of Păunescu's
Lemma 1.6). The map `φ ↦ Θ(v_φ)` is multiplicative, and preserves traces because
`τ(v_φ) = μ(Fix φ)` in `M(R)` and the normalized trace of a partial permutation is
its fixed-point fraction. By
Theorem 2.2 it is isometric, so `R` is sofic in Cordeiro's sense. Conversely a
trace-preserving semigroup embedding `Φ : [[R]] → Π_𝒰[[n_k]]` extends linearly to
the ∗-algebra spanned by `{v_φ}`. It is multiplicative and trace preserving there,
so it extends to a normal trace-preserving embedding of `M(R)`, sending
`MAlg(X,μ)` to diagonal projections and `[R]` to permutations. This is
Definition 1.13. Cordeiro's remark quoted above says the same.

## 2. Restriction and amplification

**Lemma 2.1 (restriction).** Cordeiro Proposition 3.2(a).

**Lemma 2.2 (amplification).** Let `R` be a p.m.p. relation on a finite measure
space `(W, m)` and `V ⊆ W` a non-null Borel set meeting almost every `R`-class.
If `R|_V` is sofic, then `R` is sofic.

*Proof.* Normalize `m(W) = 1`.

1. *Sheets.* By Feldman--Moore, `R` is the orbit relation of a countable group
   `K = {k_1 = id, k_2, ...}` of `m`-preserving Borel automorphisms. For almost
   every `w` put `i(w) = min{i : k_i w ∈ V}` and `W_i = {i(w) = i}`. On `W_i` the
   map `k_i` is injective and measure preserving.
2. *Truncations are restrictions of an amplification.* Put `P_n = ⊔_{i ≤ n} W_i`
   and `ι_n : P_n → V × [n]`, `ι_n(w) = (k_{i(w)} w, i(w))`. It is injective and
   carries `m|_{P_n}` to `(m|_V ⊗ counting)` on its image. For `w, w' ∈ P_n`,
   `(w, w') ∈ R` iff `(k_{i(w)} w, k_{i(w')} w') ∈ R|_V`, so
   `R|_{P_n} ≅ (R|_V × [n]^2)|_{ι_n(P_n)}`. The full relation `[n]^2` is finite,
   hence sofic (Cordeiro Corollary 3.5). By Theorem 3.6 the product is sofic, and
   by Proposition 3.2(a) so is `R|_{P_n}`.
3. *Limit.* Let `δ_n = m(W ∖ P_n) → 0` and `c_n(φ) = 1_{P_n} φ 1_{P_n}` for
   `φ ∈ [[R]]`. Then `d_m(c_n φ, φ) ≤ 2δ_n`, `d_m(c_n(φψ), c_n(φ)c_n(ψ)) ≤ 2δ_n`,
   and `|tr c_n(φ) − tr φ| ≤ δ_n`. Normalizing `m` on `P_n` rescales traces and
   distances by `1/(1 − δ_n)`. Fix finite `F ⊆ [[R]]` and `ε > 0`, choose `n` with
   `δ_n < ε/20`, and let `F_n` be the finite set of all `c_n(φ)`, `c_n(φ)c_n(ψ)`,
   `c_n(φψ)` and their idempotents and inverses for `φ, ψ ∈ F`. An almost morphism
   `π_n` of `R|_{P_n}` that is `ε/20`-multiplicative and `ε/20`-trace-accurate on
   the words of length at most four in `F_n` is `ε/4`-isometric on `F_n`, by the
   trace formula for `d` in Theorem 2.2. Then `π = π_n ∘ c_n` is `ε`-multiplicative
   and `ε`-trace-accurate on `F`. So `R` is sofic. ∎

**Proposition 2.3 (SOE invariance).** Let `a : G ↷ (X, μ)` and `b : H ↷ (Y, ν)` be
essentially free p.m.p. actions that are stably orbit equivalent: there are
non-null Borel `A ⊆ X`, `B ⊆ Y`, meeting almost every orbit, and a Borel
isomorphism `A → B` scaling measures by a constant and carrying `R_a|_A` onto
`R_b|_B`. Then `a` is sofic iff `b` is sofic.

*Proof.* `a` sofic ⟹ `R_a` sofic (Păunescu 1.15) ⟹ `R_a|_A` sofic (Lemma 2.1) ⟹
`R_b|_B` sofic (isomorphism; scaling does not change the normalized measure) ⟹
`R_b` sofic (Lemma 2.2) ⟹ `b` sofic (1.15). The converse is symmetric. ∎

The same argument shows that Connes embeddability of `M(R)` is an SOE invariant
(corners and amplifications), so a free action that is hyperlinear but not sofic
transfers along any SOE to another such action.

## 3. Couplings

A *measure equivalence coupling* of countable groups `G`, `H` is a standard
σ-finite measure space `(Ω, m)` with commuting, essentially free, `m`-preserving
actions of `G` and `H`, each with a Borel fundamental domain of finite measure
(`D_G` for `G`, `D_H` for `H`).

**Lemma 3.1 (twisting a coupling by an action).** Let `(Ω, m)` couple infinite
groups `G`, `H`, and let `H ↷ (Z, ζ)` be any p.m.p. action. Let
`B = ({0,1}, fair)^(G×H)` with the shift of `G × H`. On `Ω_Z = Ω × Z × B` let
`g` act by `(ω, z, b) ↦ (gω, z, (g,1)·b)` and `h` by `(ω, z, b) ↦ (hω, hz, (1,h)·b)`.

1. `Ω_Z` is a coupling with fundamental domains `D_G^Z = D_G × Z × B` and
   `D_H^Z = D_H × Z × B`.
2. The quotient actions `G ↷ X_Z = Ω_Z/H` and `H ↷ Y_Z = Ω_Z/G` are essentially free.
3. `H ↷ Z` is a factor of `H ↷ Y_Z`.
4. With `E` the orbit relation of `G × H` on `Ω_Z` and `W = D_G^Z ∪ D_H^Z`:
   `R(H ↷ Y_Z) ≅ E|_{D_G^Z}`, `R(G ↷ X_Z) ≅ E|_{D_H^Z}`, and both sets meet almost
   every class of the p.m.p. relation `E|_W`.

*Proof.*
1. The actions commute: they commute on `Ω` and use different indices of `B`.
   They preserve `m ⊗ ζ ⊗ fair` and are free because they are free on `Ω`. A
   fundamental domain on `Ω` times `Z × B` is a fundamental domain on `Ω_Z`, of
   the same finite measure.
2. `h[x] = [x]` in `Y_Z` means `hx = gx` for some `g`, so `(g^{-1}, h) ∈ G × H`
   fixes `x`. On the `B`-coordinate this is the Bernoulli shift of the infinite
   group `G × H`, which is essentially free. So off a null set only `(1,1)` fixes
   `x`, and `h = 1`. A null set of `Ω_Z` has null image in the quotient. Same for
   `X_Z`.
3. The projection `Ω_Z → Z` is `G`-invariant and `H`-equivariant, so it descends
   to `Y_Z ≅ D_G × Z × B → Z`, and the normalized measure goes to `ζ`.
4. For `x, x' ∈ D_G^Z`: `(x, x') ∈ E` iff `x' = ghx` for some `g, h` iff
   `[x'] = h[x]` in `Y_Z`, and `D_G^Z → Y_Z` is measure preserving. Same for
   `D_H^Z`. `E|_W` is generated by `m`-preserving partial maps, and
   `G·D_G^Z = Ω_Z = H·D_H^Z`, so each domain meets every class. ∎

**Theorem 3.2.** If `G ∈ 𝒮` and `H` is measure equivalent to `G`, then `H ∈ 𝒮`.

*Proof.* A group measure equivalent to a finite group is finite (the coupling has
finite measure), and finite groups lie in 𝒮. So let `G`, `H` be infinite, let
`H ↷ (Z, ζ)` be arbitrary, and build `Ω_Z`.
1. `G ↷ X_Z` is sofic because `G ∈ 𝒮`, and free, so `R(G ↷ X_Z) ≅ E|_{D_H^Z}` is
   sofic (Păunescu 1.15).
2. `E|_W` is sofic (Lemma 2.2), so `E|_{D_G^Z} ≅ R(H ↷ Y_Z)` is sofic (Lemma 2.1),
   and the free action `H ↷ Y_Z` is sofic (1.15).
3. Restricting a sofic embedding of `L^∞(Y_Z) ⋊ H` to the von Neumann algebra
   generated by `L^∞(Z)` and the `u_h` gives a sofic embedding of `L^∞(Z) ⋊ H`
   (Lemma A of `sofic-action-class-commensurability-proof`). So `H ↷ Z` is sofic. ∎

**Corollary 3.3 (explicit transfer).** Let `G ↷ Z` be a nonsofic p.m.p. action and
`Ω` a coupling of `G` with `H`. Exchange the roles of `G` and `H` in Lemma 3.1.
Then `H ↷ Ω_Z/G` is an essentially free nonsofic action: its orbit relation is SOE
to that of the free action `G ↷ Ω_Z/H`, which has `Z` as a factor.

## 4. Corollaries

**4.1 Lattices.** Lattices `Γ, Λ` in a lcsc group `L` are coupled by `(L, Haar)`
with `γ·ω·λ^{-1}`; `L` is unimodular because it has a lattice, and the fundamental
domains have measures `covol(Γ)` and `covol(Λ)`. So either every lattice of `L`
lies in 𝒮 or none does. Commensurable groups are measure equivalent, which
recovers part 2 of `sofic-action-class-closed-under-commensurability`; arbitrary
subgroups (part 1, Alpeev 5.2) are not covered.

**4.2 Products of two regular trees.** Let `p, q >= 3` and `L = Aut(T_p) × Aut(T_q)`.
`Δ_p = C_2 * ... * C_2` (`p` factors) has the `p`-regular tree as Cayley graph for
its involution generators, so it acts simply transitively on the vertices of `T_p`,
and `Δ_p × Δ_q` is a cocompact lattice in `L`. The kernel of `Δ_p → (C_2)^p` is
torsion free (finite-order elements of a free product are conjugate into a factor)
and of finite index, hence free by Kurosh. Every `F_a`, `a >= 2`, is isomorphic to a
finite-index subgroup of `F_2`. With 4.1 and commensurability invariance:

> A cocompact lattice `Γ` in `Aut(T_p) × Aut(T_q)` lies in 𝒮 iff `F_2 × F_2 ∈ 𝒮`.

So `F_2 × F_2 ∈ 𝒮` would make every such lattice sofic, among them Radu's BMW
lattice, which acts simply transitively on the vertices of `T_3 × T_3`
(`radu-bmw-lattice-embeds-in-titz-witzel-kernel`) and whose soficity is open
(`radu-bmw-lattice-sofic`; Cornulier records the Burger--Mozes groups as unknown).
Conversely one nonsofic such lattice gives `F_2 × F_2`, a residually finite linear
group with the Haagerup property, a free nonsofic p.m.p. action (Corollary 3.3).
Its nonsoficity could not come from a Kazhdan subgroup.

**4.3 SL_3(Z).** By 4.1, `SL_3(Z) ∈ 𝒮` iff every lattice of `SL_3(R)` is in 𝒮,
cocompact lattices included. Remark (statement-level, not re-verified): by Furman's
measure equivalence rigidity every group measure equivalent to `SL_3(Z)` is, up to
finite index and finite kernels, a lattice in `SL_3(R)`, hence linear and sofic. So
no transfer from a nonsofic group can reach `SL_3(Z)`.

**4.4 Kun--Thom groups.** Every group measure equivalent to a group containing an
infranormal non-normal Kazhdan pair lies outside 𝒮
(`groups-containing-kun-thom-pair-have-nonsofic-actions` and Theorem 3.2).

## 5. What this gives the three action roots

* `mixing-free-nonsofic-action-of-sofic-group`. If `Λ` is a nonsofic lattice and
  `Γ` a sofic lattice in a group `L` with the Howe--Moore property, and
  `Γ ↷ L/Λ` is essentially free, then it is a mixing nonsofic action of a sofic
  group (Corollary 3.3 with `Z` trivial and Proposition 2.3). No such pair of
  lattices is known, and on products of trees the decay of coefficients for the
  product group needs its own check.
* `sl3z-admits-nonsofic-action`. A property of `SL_3(R)`; transfer from a nonsofic
  group is excluded by 4.3.
* `hyperlinear-nonsofic-free-action`. Separating examples transfer along SOE.
