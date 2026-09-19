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
