---
rg: 2
id: full-complementary-idempotent-elementary-full-mf-radical-proof
kind: route
title: Saturate the complementary-idempotent defect through the unit ideal and apply the normal-Kazhdan criterion
target: full-complementary-idempotent-elementary-full-mf-radical
requires:
  - one-sided-inverse-elementary-centralizer-defect
  - normal-kazhdan-defect-non-mf
artifacts:
  - research/artifacts/full-complementary-idempotent-check-2026-09-05.md
  - non_mf_groups_exist.tex
---

## Why sufficient

Write `e = 1 - st` and fix `a_j, b_j` with `Σ_j a_j e b_j = 1`.

**Finitely generated `R`.**  `G = EL_n(R)` and `L = EL_3(R)` have property
(T) by Ershov--Jaikin-Zapirain, Theorem 1.1 (literature input; `n ≥ 3`).  By
[[one-sided-inverse-elementary-centralizer-defect]] the root `d = e_{13}(e)`
lies in `D_G(L)`.  Let `N` be its normal closure.  The Steinberg relations
give

```text
[e_{41}(a), e_{13}(e)] = e_{43}(ae),      [e_{43}(ae), e_{32}(b)] = e_{42}(aeb),
```

so `e_{42}(1) = Π_j e_{42}(a_j e b_j) ∈ N`.  Signed permutation matrices
conjugate `e_{42}(1)` to every root position up to sign, and
`[e_{ij}(1), e_{jk}(r)] = e_{ik}(r)` for distinct `i,j,k` supplies every
coefficient, so `N = G`, hence `D_G(L) = G`.  The normal-Kazhdan compression
criterion ([[normal-kazhdan-defect-non-mf]], the manuscript's Theorem A with
`K = G`) makes every homomorphism from `G` to an MF group trivial.

**Countable `R`.**  Every element of `EL_n(R)` is a finite product of
elementary matrices, hence lies in `EL_n(S)` for some finitely generated
unital subring `S` containing `s, t` and the `a_j, b_j`.  The two identities
hold in `S`, so the restriction of any homomorphism `EL_n(R) → M`, `M` MF, to
`EL_n(S)` is trivial; these subgroups exhaust `EL_n(R)`.  Nothing is claimed
about property (T) or finite generation of `EL_n(R)` itself.

The reduced-algebra consequence: `C*_r(EL_n(R))` has a faithful canonical
trace, so it is stably finite, and an embedding into a norm matrix corona
would embed the nontrivial non-MF group `EL_n(R)` through its canonical
unitaries.
