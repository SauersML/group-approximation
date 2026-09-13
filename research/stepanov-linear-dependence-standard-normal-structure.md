---
rg: 2
id: stepanov-linear-dependence-standard-normal-structure
kind: claim
title: Stepanov (1997) — standard normal structure of GL(n,R) from a linear-dependence condition, via zero-divisor transvection extraction
distinct_from:
  local-annihilation-makes-projective-el-simple: that criterion assumes simplicity plus local annihilation; this is Stepanov's theorem under the commutator formula (a) and the linear-dependence condition (b), together with his extraction lemmas.
  vaserstein-local-stable-range-normal-subgroups: that is Vaserstein's localized stable-range theorem; this is Stepanov's linear-dependence theorem.
artifacts:
  - research/artifacts/un-stepanov-credit-2026-09-13.md
---

**ESTABLISHED (literature import).** A. V. Stepanov, "On the normal structure of the general linear group over a ring",
Zap. Nauchn. Sem. POMI 236 (1997) 166–182; English translation J. Math. Sci. 95 (1999) 2146–2155, doi
10.1007/BF02169976. Quoted from the page images, pp. 2151–2152; `n ≥ 3` throughout (§1.4).

- **Lemma 4.1.** "Let F be a subgroup of GL(n,R) normalized by E(n,R) and let c ∈ F. Assume that F does not contain
  elementary transvections. If for some unimodular column α ∈ R^n and some indices i, j ∈ {1,…,n}, the elements α_i and
  (cα)_j are equal to zero, then c is a central matrix."
- **Lemma 4.3.** "Let F be a subgroup of GL(n,R) normalized by E(n,R), ξ ∈ R, and c ∈ F. Assume that F does not
  contain nontrivial elementary transvections and ξc_ij = 0 for some indices i, j. Then ξ ∈ I^⊥(c)." Here I(c) is the
  smallest ideal containing all `c_ij` and `c_ii − c_jj` (i ≠ j), and I^⊥(c) is the intersection of its right and left
  annihilators (§4.2).
- **Theorem 4.4.** "Assume that for any proper two-sided ideal I in R, the following conditions hold: (a)
  [GL(n,R,I), E(n,R)] = E(n,R,I); (b) for any a ∈ GL(n,R), there exist b ∈ E(n,R/I) and α ∈ (R/I)^n (α ≠ 0) such
  that α_i = (u^b α)_j = 0 for some i, j ∈ {1,…,n}, where u = ρ_I(a) is the image of a in GL(n,R/I). Then the normal
  structure of GL(n,R) is standard."

**For a simple ring `R`,** (a) is trivial (`I = 0`), and (b) becomes: every `a ∈ GL(n,R)` has an `E(n,R)`-conjugate
`c` and a nonzero column `α` with `α_i = (cα)_j = 0`. The conclusion then says every subgroup normalized by
`E(n,R)` is central or contains `E(n,R)`.
