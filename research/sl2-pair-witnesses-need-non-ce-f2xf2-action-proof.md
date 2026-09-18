---
rg: 2
id: sl2-pair-witnesses-need-non-ce-f2xf2-action-proof
kind: route
title: Couple SL2(Z[1/S]) with a product of free lattices, carry Connes embeddability across the twisted stable orbit equivalence by corners, and read the coset Bernoulli wreath
target: sl2-pair-witnesses-need-non-ce-f2xf2-action
requires:
  - binary-free-and-ordinary-coset-wreaths-share-hyperlinearity
  - hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower
---

"CE" means Connes embeddable. A tracial von Neumann algebra `(M, τ)` is CE if it admits a
trace-preserving embedding into `R^ω`. Equivalently, every finite tuple of `M` has matrix
microstates for all its mixed moments, with norm bounds.

Standard facts used, as stated in `tree-lattices-hyperlinear-if-f2xf2-crossed-products-proof`:
"CE passes to trace-preserving subalgebras, to corners and to `M_n(·)`." Traces on corners and
amplifications are the normalized restrictions. Rescaling a trace by a constant does not change
CE.

## Step 0. Corners with full central support

**Lemma.** Let `(M, τ)` be a finite von Neumann algebra with a faithful normal trace, and let `p`
be a projection with central support `1`. If `pMp` is CE, then `M` is CE.

*Proof.*
1. Take a maximal family of partial isometries `(v_i)` in `M` with `v_i^* v_i <= p` and pairwise
   orthogonal ranges `v_i v_i^*`. Put `q = Σ_i v_i v_i^*`.
2. Suppose `1 − q ≠ 0`. Since `p` has central support `1`, the comparison theorem gives a nonzero
   partial isometry `w` with `w w^* <= 1 − q` and `w^* w <= p`. This contradicts maximality.
   Hence `Σ_i v_i v_i^* = 1`.
3. `M` is σ-finite, so the family is countable. Put `q_n = Σ_(i<=n) v_i v_i^*`.
4. The map `x ↦ [v_i^* x v_j]_(i,j<=n)` is a `*`-isomorphism of `q_n M q_n` onto a corner of
   `M_n(pMp)`.
5. It scales traces: `τ(x) = Σ_i τ(v_i^* x v_i) = τ(p) · (Tr ⊗ τ_p)([v_i^* x v_j])`.
6. So `q_n M q_n` is CE, as a corner of the CE algebra `M_n(pMp)`.
7. For a finite tuple `x_1, ..., x_k` of contractions in `M`, the normalized mixed moments of
   `q_n x_i q_n` in `(q_n M q_n, τ(q_n)^(-1) τ)` converge to those of the `x_i` in `M`. This
   holds because `||1 − q_n||_2 → 0` and `τ(q_n) → 1`.
8. Microstates for the truncated tuples are therefore microstates for the `x_i` up to vanishing
   error, so `M` is CE. ∎

## Step 1. `𝒜` is closed under subgroups

Let `Δ <= Γ` and let `Δ ↷ (Z, ζ)` be p.m.p.

1. Coinduce: `X = { f : Γ → Z | f(γδ) = δ^(-1) f(γ) }`. Fixing a transversal `T` of `Γ/Δ`
   identifies `X` with `Z^T`, with measure `ζ^(⊗T)`, independent of `T` because `Δ` preserves
   `ζ`. `Γ` acts by `(γ·f)(x) = f(γ^(-1) x)`, and this action preserves the measure.
2. Evaluation `f ↦ f(e)` is `Δ`-equivariant: `(δ·f)(e) = f(δ^(-1)) = δ f(e)`. It is
   measure-preserving, so `Z` is a `Δ`-factor of `X`.
3. This gives trace-preserving inclusions
   `L^∞(Z) ⋊ Δ ⊂ L^∞(X) ⋊ Δ ⊂ L^∞(X) ⋊ Γ`.
   Both traces are `a u_δ ↦ δ_(δ,e) ∫ a`.
4. If `Γ ∈ 𝒜`, the right side is CE, so the left side is CE. ∎

## Step 2. Measure-equivalence invariance of `𝒜`

Let `(Ω, m)` be a coupling of `G ∈ 𝒜` and `H`, and let `H ↷ (Z, ζ)` be p.m.p. We use the twist
of `paunescu-class-me-invariance-proof` verbatim:

> "On `Ω_Z = Ω × Z × B` let `g·(ω, z, b) = (gω, z, (g,1)b)` and
> `h·(ω, z, b) = (hω, hz, (1,h)b)`.
> 1. These commute, preserve the measure, are free, and have fundamental domains
>    `D_G^Z = D_G × Z × B` and `D_H^Z = D_H × Z × B`.
> 2. `H ↷ Y_Z = Ω_Z/G` and `G ↷ X_Z = Ω_Z/H` are essentially free [...]
> 3. `Ω_Z → Z` is `G`-invariant and `H`-equivariant, so `Z` is a factor of `Y_Z`.
> 4. With `E` the orbit relation of `G × H` and `W = D_G^Z ∪ D_H^Z`:
>    `R(H ↷ Y_Z) ≅ E|_(D_G^Z)` and `R(G ↷ X_Z) ≅ E|_(D_H^Z)`, and both domains meet
>    almost every class of `E|_W`."

Here `B = ({0,1}, fair)^(G×H)`. The isomorphisms in item 4 identify `Y_Z` with `D_G^Z` and
`X_Z` with `D_H^Z` through fundamental domains, so they preserve the restricted measure `m`.

1. **Relation algebra.** `W` has finite measure, so `N = L(E|_W)` (Feldman–Moore) is a finite
   von Neumann algebra with trace `m|_W / m(W)`. For `U ⊂ W`, the corner `1_U N 1_U` is
   `L(E|_U)` with its trace rescaled.
2. **Central support.** Central projections of `N` lie in `L^∞(W)` and are indicators of
   `E|_W`-invariant sets `S`.
   - If `1_S 1_(D_H^Z) = 0`, then `S` is a union of classes that miss `D_H^Z`.
   - By item 4 almost every class meets `D_H^Z`, so `S` is null.
   - Hence `1_(D_H^Z)` has central support `1`. The same holds for `1_(D_G^Z)`.
3. **Transfer.**
   - `G ↷ X_Z` is essentially free and p.m.p. (item 2), so
     `L^∞(X_Z) ⋊ G = L(R(G ↷ X_Z)) ≅ 1_(D_H^Z) N 1_(D_H^Z)`, up to rescaling the trace.
   - `G ∈ 𝒜` makes this CE. By Step 0, `N` is CE.
   - So its corner `1_(D_G^Z) N 1_(D_G^Z) ≅ L(R(H ↷ Y_Z)) = L^∞(Y_Z) ⋊ H` is CE.
4. **Factor.** Restricted to `D_G^Z = D_G × Z × B`, the factor map of item 3 is the coordinate
   projection. It pushes the normalized measure onto `ζ`. So
   `L^∞(Z) ⋊ H ⊂ L^∞(Y_Z) ⋊ H` is trace-preserving, and `L^∞(Z) ⋊ H` is CE.

Since `Z` was arbitrary, `H ∈ 𝒜`. Subgroups (Step 1) together with ME invariance give item 1 of
the target. ∎

## Step 3. The coupling for `SL_2(Z[1/S])`

Put `A = SL_2(Z[1/S])` and `L = SL_2(R) × Π_(p∈S) SL_2(Q_p)`.

1. **The arithmetic lattice.** By Borel–Harish-Chandra, `A`, embedded diagonally, is a lattice in
   `L`. This is the same import as step 1 of `dyadic-vertex-action-sofic-from-f2xf2-paunescu-class`.
2. **The free lattice `Γ(3)`.**
   - `Γ(3) = ker(SL_2(Z) → SL_2(F_3))` does not contain `−I`, so it maps isomorphically into
     `PSL_2(Z)`, with index `|PSL_2(F_3)| = 12`.
   - It is torsion-free, with rational Euler characteristic `12 · (−1/6) = −2`, so it is free of
     rank `3`.
   - It is a lattice in `SL_2(R)`.
3. **The free lattices `Λ_p`.** Import, verbatim from
   `homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse`: "Cocompact lattices exist in
   `SL_n(Q_p)` for every `n` and `p` [...] for `n = 2` the unit groups of definite quaternion
   orders split at `p`), and Selberg's lemma gives torsion-free finite-index subgroups."
   - Let `Λ_p` be such a torsion-free cocompact lattice.
   - It acts on the `(p+1)`-regular Bruhat–Tits tree without inversions (`SL_2` preserves vertex
     types), with trivial vertex stabilizers (discrete ∩ compact is finite, hence trivial) and
     finite quotient.
   - So `Λ_p ≅ F_(r_p)` with `r_p >= 2`, because the quotient graph has all degrees `p + 1 >= 3`
     and negative Euler characteristic.
4. **Product lattice.** `P = Γ(3) × Π_p Λ_p ≅ F_3 × Π_p F_(r_p)` is a lattice in `L`.
   - `F_r` is isomorphic to a subgroup of index `r − 1` of `F_2`.
   - So `P` is isomorphic to a finite-index subgroup of `F_2^(|S|+1)`.
5. **Coupling.** `L` is unimodular. Take `Ω = L` with Haar measure, `A` acting by left
   multiplication and `P` by right multiplication by inverses.
   - Both actions are free, commute and preserve Haar measure.
   - Both have finite-measure fundamental domains, because both groups are lattices.
   - So `A` and `P` are measure equivalent.
6. **Conclusion of item 2.**
   - If `F_2^(|S|+1) ∈ 𝒜`, then `P ∈ 𝒜` (Step 1) and `A ∈ 𝒜` (Step 2).
   - Conversely, if `A ∈ 𝒜`, then `P ∈ 𝒜` (Step 2) and `F_2^(|S|+1) ∈ 𝒜` (Step 2, since
     finite-index inclusions are couplings). ∎

## Step 4. Pair transfer

Let `C <= A` and assume `F_2^(|S|+1) ∈ 𝒜`, so `A ∈ 𝒜` by Step 3.

1. **Fourier transform.** Pontryagin duality for `⊕_(A/C) C_2` gives an `A`-equivariant,
   trace-preserving isomorphism `L(⊕_(A/C) C_2) ≅ L^∞({±1}^(A/C), product of fair measures)`.
   Hence

   ```text
   L(W) = L(⊕_(A/C) C_2) ⋊ A ≅ L^∞({±1}^(A/C)) ⋊ A,   W = (⊕_(A/C) C_2) ⋊ A,
   ```

   as in `(CW2)` of `nonhyperlinear-coset-wreath-from-commutant-collapse`.
2. **Hyperlinearity of `W`.** The generalized Bernoulli action is p.m.p., so `L(W)` is CE because
   `A ∈ 𝒜`. By `hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower`, `W` is
   hyperlinear.
3. **The other statements.** Statement 1 of `binary-free-and-ordinary-coset-wreaths-share-hyperlinearity`
   holds, so statements 2–7 hold. These are hyperlinearity of `A *_C (C × C_2)`, `A *_C A`,
   `A *_C (C × Z)` and `(A × Z) *_C A`, scalar relative embeddability of `L(C) ⊂ L(A)`, and
   Connes embeddability of the Gaussian crossed product. This is item 3. ∎

## Step 5. The explicit contrapositive action

- Take `S = {2}`, `C = SL_2(Z)`, `A = SL_2(Z[1/2])`. Then `A/C` is the set of type-0 vertices of
  the 3-regular tree.
- If `G_2` is not hyperlinear, then by Step 4 `L^∞({±1}^(A/C)) ⋊ A` is not CE.
- Step 2, run with `H = A`, `G = P` and `Z = {±1}^(A/C)`, shows that the essentially free action
  `P ↷ X_Z` has a non-CE crossed product.
- Induce this action to `F_2 × F_2`. By step 5 of `tree-lattices-hyperlinear-if-f2xf2-crossed-products-proof`
  (the corner `q(L^∞(Y) ⋊ Γ)q`), the induced crossed product is not CE.
- Its step 7 (product with the Bernoulli shift) keeps the action essentially free and the crossed
  product non-CE. ∎
