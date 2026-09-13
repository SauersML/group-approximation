---
rg: 2
id: edge-twist-moment-test-elementary-abelian-edges
kind: claim
title: The edge-twist moment test holds for arbitrary finite edge groups, with moments weighted by the twisting homomorphisms
distinct_from:
  edge-twist-extensions-of-triangle-colimits-moment-test: that states the test for cyclic edge groups of prime order p; this is the same test for any finite edge groups and any twisting homomorphisms E_e -> F_p, needed for the (Z/2)^f edges of the Kazhdan SL_2 root triangles
---

**Setting.** As in `edge-twist-extensions-of-triangle-colimits-moment-test`, except that the edge groups
`E_e` are arbitrary finite groups. `C = F_p`, and the twist is `c = (c_e)` with `c_e ∈ Hom(E_e, C)`. The
central extension `Λ_c` and, for torsion-free finite-index normal `N`, the spaces `Q = Λ/N`,
`M = F_p^Q` and

```text
Z_N = { λ ∈ F_p[Q] : Σ_{q ∈ E_e q_0} λ(q) = 0 for every right coset E_e q_0 and every e }
```

are defined verbatim.

**ESTABLISHED.** Put

```text
μ_e^{c_e}(λ) = Σ_{right cosets E_e q_0}  Σ_{x ∈ E_e}  c_e(x) λ(x q_0) .
```

Each coset is summed once. The value does not depend on the base points `q_0`, because `c_e` is a
homomorphism and `λ` sums to `0` on each coset. Then:
- **(M2')** `Λ_c` has a finite quotient injective on `C` that factors through `C^Q ⋊ Q` over `Λ -> Q` iff
  `μ_13^{c_13}(λ) = μ_12^{c_12}(λ) + μ_23^{c_23}(λ)` for all `λ ∈ Z_N`.
- **(M4')** The twists satisfying (M2') at level `N` form a subspace, and it only grows when `N` shrinks.
  So the moment subspace `I_N`, spanned by the three functionals restricted to `Z_N`, can only shrink.
- **(M5')** Covers of index prime to `p` change nothing.

For `E_e = <x_e>` cyclic of order `p` and `c_e(x_e^k) = k c_e`, one gets `μ_e^{c_e} = c_e μ_e`, which is
the original test. (M1), (M3) and (M6) of the original claim use only the extension `Λ_c`, so they carry
over unchanged.

**Computation form.** Over `F_2`, let `B` be the `F_2`-matrix of right-coset indicators, with rows the
cosets of all three edge groups and columns `Q`. Then `Z_N = ker B`. Let `R` be the matrix of moment rows
`g ↦ τ(x_g)`, where `g = x_g q_0` and `τ` runs over a spanning set of `Hom(E_e, F_2)`. Then

```text
dim I_N = rank [B; R] - rank B .
```

Proof: `edge-twist-moment-test-elementary-abelian-edges-proof`.
