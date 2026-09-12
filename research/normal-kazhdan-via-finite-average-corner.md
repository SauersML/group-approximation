---
rg: 2
id: normal-kazhdan-via-finite-average-corner
kind: route
title: Contradict the corner representation with one finite probability average
target: normal-kazhdan-defect-non-mf
requires:
  - kazhdan-projection-is-norm-limit-of-finite-averages
  - matrix-corona-projection-ideal-and-corner-calculus
artifacts:
  - research/artifacts/shorter-proofs-review-2026-09-07.md
  - non_mf_groups_exist.tex
---

## Why sufficient

A fourth complete proof of the target.  It follows
`normal-kazhdan-via-corner-trace-character` as far as the corner and then
replaces the ultrafilter trace state by a finite average, so the section
retains no ultrafilter.

Let `Theta : G -> U(Q_d)` be a corona homomorphism nontrivial on the normal
Kazhdan subgroup `K`, let `p` be the image of `e_K` under
`C*_max(K) -> Q_d`, and put `q = 1 - p`.  Normality makes `p` commute with
`Theta(G)`, and `q != 0` because `Theta` is nontrivial on `K`.  By clause
(CI1) of `matrix-corona-projection-ideal-and-corner-calculus`, `q Q_d q` is
again a norm matrix corona `Q_r` on the retained coordinates, and unitaries
of a matrix corona lift to unitaries by polar decomposition, so the
compressed representation has operator-norm asymptotic unitary lifts
`W_n : G -> U(r_n)`.  Write `pi : C*_max(K) -> Q_r` for the induced
homomorphism; `pi(e_K)` is the coordinate restriction of `qp = 0`.

The hypothesis of the target applies to `(W_n)` in its own dimensions, so
`||W_n(k) - I||_2 -> 0` for every `k in K`.

Take a probability average `a = sum_(k in F) mu(k)u_k` with
`||a - e_K|| < 1/2` and put `B_n = sum_(k in F) mu(k)W_n(k)`.  From
`|tr_(r_n)(W) - 1| <= ||W - I||_2` for unitaries,
`tr_(r_n)(B_n) -> 1`.  Then

```text
1 = lim_n |tr_(r_n)(B_n)| <= limsup_n ||B_n|| = ||pi(a)||
  = ||pi(a) - pi(e_K)|| <= ||a - e_K|| < 1/2,
```

a contradiction.  The renormalization of the trace on the complementary
corner is what makes this work: the corner may have vanishing relative rank
in the original coordinates, and the traces of `Q_d` would not see it.
