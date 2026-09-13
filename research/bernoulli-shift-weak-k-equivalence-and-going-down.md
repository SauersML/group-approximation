---
rg: 2
id: bernoulli-shift-weak-k-equivalence-and-going-down
kind: claim
title: A finite-alphabet Bernoulli shift is weakly K-equivalent to the trivial algebra plus a proper algebra, and weak K-equivalences induce isomorphisms on topological K-theory with no Baum--Connes hypothesis
distinct_from:
  amenable-kernel-bc-transfer-and-ktop-half-exactness: that imports the Chabert--Echterhoff transfer along amenable kernels and half-exactness of topological K-theory; this imports the Chakraborty--Echterhoff--Kranz--Nishikawa weak K-equivalence for Bernoulli shifts, the Bönicke--Dell'Aiera going-down theorem and the generalized Green--Julg theorem.
---

**ESTABLISHED (citation)** by `bernoulli-shift-weak-k-equivalence-and-going-down-citation`. Groups are countable
and discrete.

A morphism `x ∈ KK^G(A, B)` is a **weak K-equivalence** if for every finite subgroup `H <= G` its restriction induces
isomorphisms `K_*(A ⋊ H) -> K_*(B ⋊ H)`.

1. **Bernoulli shifts.** Let `Z` be a countable `G`-set, `Λ = {0, ..., n}`, `A = C(Λ)`, `B = C(Λ \ {0})`, `ι : C -> A`
   the unit and `φ : B -> A` the inclusion. Then there is a weak K-equivalence
   `Φ ∈ KK^G(J^Z_B, C(Λ^Z))`, where `J^Z_B = ⊕_(F ⊆ Z finite) B^(⊗F)` carries the permutation action, is a
   `G`-`C_0(FIN(Z))`-algebra, and the component of `Φ` at `F = ∅` is the unit `C -> C(Λ^Z)`. No Baum--Connes hypothesis
   on `G` is needed for this part.
2. **Going-down.** If `x ∈ KK^G(A, B)` is a weak K-equivalence, then `K^top_*(G; A) -> K^top_*(G; B)` is an
   isomorphism, for every countable discrete `G`.
3. **Proper coefficients.** If `A` is a proper `G`-algebra, `mu_(G, A)` is an isomorphism.

**Reading for discrete groups.** Item 2 is the case of Bönicke--Dell'Aiera's theorem where the ample groupoid is a
countable discrete group. Its compact open subgroupoids are the finite subgroups `H`, the unit space is a point, and
`KK^H(C, D) = K_*(D ⋊ H)` by the Green--Julg theorem (context, not re-read).
