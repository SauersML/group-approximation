---
rg: 2
id: leavitt-algebras-contain-no-two-variable-polynomial-ring
kind: claim
title: For every field k, the binary Leavitt algebra L_k(1,2) contains no two commuting k-algebraically independent elements
distinct_from:
  leavitt-commuting-units-are-algebraically-dependent: that is the statement for commuting units over F_2 only; this is the field-uniform statement for arbitrary commuting elements, which implies it (route commuting-units-dependence-from-field-uniform-leavitt-rank).
  laurent-tensors-reduce-leavitt-rank-to-function-fields: that reduces Z^4 embeddings through the equicontinuous factor to this kind of statement over F_2(x,y); this is the target statement itself, for all fields at once.
  leavitt-isometry-centralizers-are-monogenic: that settles the pairs one of whose members is a monomial isometry or co-isometry; this asks for all pairs.
  no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2: that is the Ara--Cortiñas Q5.7 consequence over F_2; this claim implies it for every field.
  hochschild-dimension-bounds-commuting-independent-families: that is the general statement for every algebra of Hochschild dimension at most d, in every matrix size. This is its instance d = 1, r = 1 for L_k(1,2) (route leavitt-polynomial-bound-from-hochschild-dimension).
---

**OPEN.** Let `k` be any field and `L = L_k(1,2)`. If `a, b ∈ L` commute, then `P(a, b) = 0` for some nonzero
`P ∈ k[x, y]`. Equivalently, `k[x, y]` has no embedding as a subalgebra of `L`.

**Why it matters.** This is the field-uniform statement asked for by the live need on
`decidable-algebras-embed-in-z2-sft-boundary-product-hosts` (w15, "Need a FIELD-UNIFORM statement ...").
- At `k = F_2` it gives `leavitt-commuting-units-are-algebraically-dependent`, hence the tensor-square firewall.
- At `k = F_2(x, y)` it kills mechanism (i) of the `F_2[Z^4]` test case of
  `f2-z4-embeds-in-z2-sft-boundary-product-hosts`. By `laurent-tensors-reduce-leavitt-rank-to-function-fields`
  it also kills every `Z^4` embedding supported on the equicontinuous-factor part of `B_Ω ⊗ L_2`.

**Decomposition.** The route `leavitt-rank-one-from-free-field-matrices-and-degree-reduction` splits this claim
into two prerequisites. Each one can fail without the other.
1. `matrices-over-free-fields-have-no-trdeg-two-subfields`: a pure skew-field statement. Its case `r = 1` is
   classical (Cohn, Schofield).
2. `leavitt-polynomial-pairs-move-to-the-nonnegative-part`: a statement about the Z-grading.

The established structure lemma `leavitt-nonnegative-part-is-matrix-union-over-free-algebra` glues the two
together.

## Attempts

**w16 obstruction-miner (linear-characteristic): decomposition, not a proof.**
- The nonnegative part `L_(>=0)` is a union of matrix rings `M_(2^N)(k<x_0, x_1>)`
  (`leavitt-nonnegative-part-is-matrix-union-over-free-algebra`).
- So pairs inside `L_(>=0)`, and by the involution pairs inside `L_(<=0)`, reduce to subfields of `M_r` of the
  free field.
- *Where it stops.*
  - The case `r >= 2` of the skew-field question is not in the literature I checked.
  - No reduction is known for pairs of mixed degree.
  - `L_(>=0)` is stably finite and `L` is purely infinite, so no unital endomorphism of `L` lands in `L_(>=0)`.
    The degree reduction must therefore work pair by pair.

**w18 follow-through (swarm-0917-w18-w18-bh-follow, cohomology-index): a complete route, which bypasses the
decomposition.** Route: `leavitt-polynomial-bound-from-hochschild-dimension`.
- *Lower bound.* Let `a_1, ..., a_n ∈ A` commute and be algebraically independent, and put `C = k[a]`,
  `K = k(y_1, ..., y_n)`, `R = A ⊗ K`. The Koszul complex of `z_i = a_i ⊗ 1 - 1 ⊗ y_i` over `S = C ⊗ K`, induced
  to `R`, stays exact. The reason is that `Tor^S_i(R, S/I) = Tor^C_i(A, Frac C) = 0`: flatness of `Frac C` over
  `C` replaces the flatness of `A` over `C` that stopped the earlier subfield and polynomial attempts. The top
  Tor is nonzero, so `w.gl.dim(A ⊗ K) >= n` (`polynomial-subrings-bound-transcendental-flat-dimension`).
- *Upper bound.* `gl.dim(L ⊗ K) <= pd_(L^e) L <= 1`.
- *Result.* `n <= 1`. The general form is `hochschild-dimension-bounds-commuting-independent-families`.
- *Effect on the decomposition.* Neither prerequisite of
  `leavitt-rank-one-from-free-field-matrices-and-degree-reduction` is needed. The grading half
  `leavitt-polynomial-pairs-move-to-the-nonnegative-part` becomes vacuously true, since there are no pairs.
- *Downstream.* The route `commuting-units-dependence-from-field-uniform-leavitt-rank` now closes
  `leavitt-commuting-units-are-algebraically-dependent`. Through `tensor-square-nonembedding-from-algebraic-dependence`
  that gives the root `no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2`.
- *Same method, crossed products.* `cantor-crossed-products-bound-commuting-rank-by-cd` gives
  `w.gl.dim(LC(X, K) ⋊ Γ) <= cd_k Γ`. With `f2-z4-has-no-embedding-in-z2-sft-boundary-product-hosts`, this refutes
  the `Z^4` test case and (E).
- *Maintainer note.* The body line "**OPEN.**" above predates this route. Per the contract, this worker edited
  only the frontmatter and this section.
