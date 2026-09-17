---
rg: 2
id: pointer-gated-linear-codes-are-rank-dominated
kind: claim
title: Gated linear value outputs recover at site one no more dimensions than the expected gated rank
distinct_from:
  gated-diagonal-linear-deficits-force-kaplansky-failure: that proves this inequality for monomial-diagonal gating over directly finite group rings through uniqueness of inverses; this asks for arbitrary gating matrices, where left inverses of columns are not unique.
  rokhlin-window-transport-is-dominated: that is condition (D) for all configurations; this is only the value-linear part of (D) for pointer-linear codes, and by the exact split it reduces such witnesses to their pointer codes.
  bernoulli-witness-information-is-bounded-by-code-reads: that bounds transported information by read degree times code entropy; this is a rank inequality with constant one for the linear part.
artifacts:
  - research/artifacts/pointer-gated-linear-witness-direct-finiteness-2026-09-17.md
---

**OPEN.** Let `G` be a countable group, `q` a prime power, and `psi = (J, L_J)` a pointer-linear code:
- the pointer bits `p` are iid uniform, `J` is arbitrary, and the value bits `v ∈ F_q^{k_V}` are iid
  uniform and independent of `p`;
- each `L_j : F_q^{E × k_V} -> F_q^{m}` is an arbitrary linear map.

For `f ∈ F` let the codeword at `f` output `L_{J_f}(v|_{fE})`. Put:
- `d(J_F)` = the dimension of the space of functionals on `v(1)` that lie in the row space of all
  outputs on `F`;
- `r(j) = rank L_j`.

Then

    E d(J_F) <= E r(J_1) .

**Why it matters.** By Theorem 1 of the artifact,
`gap(psi) = gap(J) + log q (E d - E r)`. So this claim for `G` reduces every value-linear Bernoulli
deficit witness over `G` to a deficit witness of its pointer code on fewer coordinates.

**Known cases.**
* **Finite groups.** Counting ranks of all outputs gives the inequality (Proposition 8 of the
  artifact).
* **Gated monomial-diagonal codes over groups with `F_q[<E ∪ F>]` directly finite.**
  `gated-diagonal-linear-deficits-force-kaplansky-failure`.
* **No pointer (`J` constant).** Proposition 4 of the transport artifact, on every pattern.
* **Abstract cancellative patterns: false.** The split parity gadget in a finite loop has
  `E d ≈ 3.87` and `E r = 1`, so the claim must use associativity.

## Attempts
- **Uniqueness of inverses (a-gs-window-transport, 2026-09-17).** It does not extend beyond diagonal
  gating.
  - Recovering `λ` means `λ = Σ_f μ_f f L_{J_f}`, a left inverse of a column over `F_q[G]`. Such
    inverses are not unique even over commutative rings.
  - For a fixed invertible `T` gated by rows, with `M_n(F_q[K])` directly finite, one gets the
    pointwise constraints `λ T^{-1}(g) ∈ F_q^{I_{J_g}}`. Turning them into a dimension bound needs a
    translation-invariant dimension.
  - The identity `id_Λ = Σ_g (Λ -> F_q^{I_{J_g}} -> Λ)` has trace equal to `dim Λ` only mod `p`.
  - Artifact Section 6.1. A Sylvester rank function on the crossed product `C(Jset^G, F_q) ⋊ G`
    compatible with translation would suffice.
