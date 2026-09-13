---
rg: 2
id: vaserstein-local-stable-range-normal-subgroups
kind: claim
title: Vaserstein (LNM 854, 1981) — subgroups normalized by E_n A are standard under a local stable-range or column-reduction condition
distinct_from:
  local-annihilation-makes-projective-el-simple: that criterion assumes simplicity plus local annihilation and needs no stable range; this is Vaserstein's standard normal structure theorem under localized stable-range or column-reduction hypotheses.
artifacts:
  - research/artifacts/un-stepanov-credit-2026-09-13.md
---

**ESTABLISHED (literature import).** L. N. Vaserstein, "On the normal subgroups of GL_n over a ring", Algebraic
K-theory, Evanston 1980, Lecture Notes in Math. 854 (1981), 456–465. Read from the Springer PDF on MSI, pp. 456 and
464. Statement (2) there: a subgroup `H` of `GL_n A` is normalized by `E_n A` if and only if, for a unique ideal `B` of
`A`, the image of `H` in `GL_n A/B` lies in the center and `H ⊃ [E_n A, E_n B]`.

- **Theorem 4 (p. 456).** "Suppose that n ≥ 3 and for every maximal ideal D of the center C of A there exists a
  multiplicative set S ⊂ C − D such that sr(S^{-1}A) ≤ n − 1. Then (2) holds."
- **Theorem 19 (p. 464).** "Let n ≥ 3. Suppose that for every maximal ideal D of the center C of A and any
  g = (g_{i,j}) ∈ GL_n A there exist a_i, b_i ∈ A, s ∈ C − D such that Σ_{i=1}^{n−1} b_i(g_{i,1}s + a_i g_{n,1}) = s².
  Then a subgroup H of GL_n A is normalized by E_n A if and only if H ⊃ E_n(A, J(H))."

**For a simple ring `A`,** the only ideals are `0` and `A`, so (2) says: every subgroup normalized by `E_n A` is
central or contains `E_n A`. That is the conclusion of `local-annihilation-makes-projective-el-simple` for subgroups
of `EL_n(A)`. Vaserstein's hypotheses are stable-range conditions, which local annihilation does not supply. Whether
they hold for the Steinberg algebras in `steinberg-elementary-groups-are-simple-mod-centre` is not decided here.
