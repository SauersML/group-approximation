---
rg: 2
id: euler-class-protection-fails-for-o2-self-similar-modules
kind: claim
title: In a Hilbert C(X)-module isomorphic to its double, complements of trivial summands have vanishing Euler class at late stages
artifacts:
  - research/artifacts/lxi-o2-multiplier-reduction-2026-09-12.md
---

Let `X` be compact and connected, and let `E` be a countably generated Hilbert `C(X)`-module with
`E ≅ E ⊕ E`. Suppose `E` is exhausted by increasing complemented finitely generated projective
submodules `E_n`, and `E` contains a summand `θ^2` spanned by two orthonormal sections. Write
`E_n = θ^2 ⊕ P_n` at late stages, with `r_n = rank P_n`. Then the Euler class `e(P_n) = c_{r_n}(P_n)`
vanishes for all large `n`.

Proof: the words `S_w` in the halving isometries, applied to a unit section, give four orthonormal
sections of `E`. By strict convergence and Gram--Schmidt they lie in some `E_n`, so
`E_n ≅ θ^4 ⊕ η` with `rank η = r_n - 2`. Then `c(P_n) = c(η)`, and `c_{r_n}(η) = 0`.

Consequence: witness protections that need a nonzero Euler class of the complement at every stage are
impossible in the `O_2`-multiplier reduction of LXI. This covers the LIX parity protection and Toms's
trapped spin-bordism class.
