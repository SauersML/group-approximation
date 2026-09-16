---
rg: 2
id: characters-living-on-m-plus-one-factors-lie-in-sigma-m
kind: claim
title: A character of a product of at least m+1 groups of type F_m that is nonzero on every factor lies in Sigma^m
---

**ESTABLISHED (citation route `characters-living-on-m-plus-one-factors-meinert-citation`: Meinert's inequality as
stated in Bieri–Geoghegan arXiv:0808.0013v2 Theorem 1.2, plus an induction; refereed 2026-09-16).** Let `G_1, ..., G_k` be groups of
type `F_m` with `k >= m+1`. Let `χ = (χ_1, ..., χ_k)` be a character of `G_1 × ... × G_k` with every `χ_i != 0`.
Then `[χ] in Σ^m(G_1 × ... × G_k)`.

**Derivation from Meinert's inequality.** The inequality reads
`Σ^m(A × B)^c ⊆ ∪_{p+q=m} Σ^p(A)^c * Σ^q(B)^c`, with the convention `Σ^0 = S`, so `Σ^0(·)^c = ∅`. A point of the
spherical join with both coordinates nonzero lies in a join of two nonempty complements, which forces `p, q >= 1`.
By induction on the number of factors, a character nonzero on all `j` factors lies in `Σ^q(product)^c` only if
`q >= j`. So an all-living character lies in `Σ^m(G_1 × ... × G_k)^c` only if `m >= k`.

**Model tests (sharpness).**

- `k = 2`, `m = 1`, `G_i = F_2`: a character nonzero on both factors lies in `Σ^1(F_2 × F_2)`, as
  `commuting-living-generators-give-sigma-one` also shows.
- `k = m = 2`: `F_2 × F_2 = A_Γ` for the 4-cycle `a_1 - a_2 - b_1 - b_2 - a_1`, with `χ(a_i) = 1` and `χ(b_i) = 0`.
  The dead edge `{b_1, b_2}` has empty living link, so `[χ] ∉ Σ^2` by the Meier–Meinert–VanWyk criterion.
  The bound `k >= m+1` cannot be lowered.

## Attempts

- **Sources to read.**
  - R. Gehrke, *The higher geometric invariants for groups with sufficient commutativity*, Comm. Algebra 26 (1998).
  - R. Bieri and R. Geoghegan, *Sigma invariants of direct products of groups*, Groups Geom. Dyn. 4 (2010). They
    prove the homological product formula over fields and discuss the homotopical Meinert inequality.
  - Theorem numbers were not read. Once they are, this becomes a `-citation` route.
- Used by `rover-nekrashevych-higher-sigma-full-via-kernel-brown`. It is not needed when every `G_i` is finitely
  generated abelian, where the kernels are free abelian.
