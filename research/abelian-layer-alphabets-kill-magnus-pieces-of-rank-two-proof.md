---
rg: 2
id: abelian-layer-alphabets-kill-magnus-pieces-of-rank-two-proof
kind: route
title: Iterated commutators of a_0 with its a_1-conjugate are nontrivial in the free Magnus subgroup but lie in every bounded derived term of the normal closure of a_0
target: abelian-layer-alphabets-kill-magnus-pieces-of-rank-two
requires: []
---

Date: 2026-09-18. Written proof. `[g,h] = g^(-1) h^(-1) g h`.

**(a) Nontriviality.** `n >= 2` and `W_0` involves `a_n`. By the
Freiheitssatz, `F_- = <a_0,...,a_(n-1)>` is free on these letters and embeds
in `B_0`. It contains `a_0` and `a_1`, which freely generate a free subgroup
`F = <a_0,a_1>`. Let `R_F` be the normal closure of `a_0` in `F`, which is
the kernel of `F -> <a_1>`, `a_0 -> 1`. So `R_F cap <a_1> = 1`.

Induction on `d`: `b_d in R_F \ {1}`.
* **Base.** `b_1 = [a_0, a_1 a_0 a_1^(-1)]` is a reduced nonempty word, so
  `b_1 != 1`. It lies in `R_F` because both entries do.
* **Step.** Suppose `b = b_d in R_F \ {1}`, and put `c = a_1 b a_1^(-1)`.
  If `[b,c] = 1`, then in the free group `F` both `b` and `c` are powers of
  one root: `b = r^p`, `c = r^q`. Conjugate elements have equal cyclic
  length, so `|p| = |q|`. Hence either `c = b` or `c = b^(-1)`.
  * If `c = b`, then `a_1` commutes with `b`, so `b in <a_1>` (the centralizer
    in a free group is cyclic and contains the root of `a_1`, which is
    `a_1`). Then `b in R_F cap <a_1> = 1`, which is false.
  * If `c = b^(-1)`, then a nontrivial element of a free group is conjugate
    to its inverse. That is impossible: under the abelianization, or by
    looking at a cyclically reduced conjugate, `r^p` conjugate to `r^(-p)`
    forces `p = 0`.

  So `b_(d+1) = [b,c] != 1`. It lies in `R_F`, since `R_F` is normal. ∎(a)

**(b) Killing.** Let `S` be normal in `Q_0 = <psi(a_0),...,psi(a_n)>`, with
`psi(a_0) in S` and `S^(d) = 1`. Then `psi(R_F) <= S`, since `S` is normal in
`Q_0`, which contains `psi(F)`.

By induction, `psi(b_k) in S^(k)`:
* **Base.** `psi(b_1) = [psi(a_0), psi(a_1) psi(a_0) psi(a_1)^(-1)]`, and both
  entries lie in `S`.
* **Step.** If `psi(b_k) in S^(k)`, then its `psi(a_1)`-conjugate is also in
  `S^(k)`, because `S^(k)` is characteristic in `S` and `S` is normal in
  `Q_0`. So their commutator lies in `S^(k+1)`.

Hence `psi(b_d) in S^(d) = 1`. ∎(b)

**Application to the tower.** In
[[bs12-amenable-square-chain-induced-tower-proof]], every stage has the form
`V rtimes K`. The new letter `e = x_0` lies in the abelian normal subgroup
`V`, and all other letters of the window lie in `K`. So `V cap Q_0` is an
abelian normal subgroup of `Q_0` containing `psi(a_0)`, and (b) with `d = 1`
gives `psi(b_1) = 1`. The same holds at every coordinate `j`, by the same
argument at the stage where `x_j` was prepended; inclusions preserve the
relation. For the direct limit or the ascending HNN extension, `b_1` is
killed at a finite stage, and hence everywhere. ∎

**Calibration (n = 1).** Here `F_- = <a_0>`, so `a_1 not in F_-`, and
`b_1 = [a_0, a_1 a_0 a_1^(-1)]` is **trivial** in `B_0 = BS(1,2)`, because
`a_1 a_0 a_1^(-1)` is a power of `a_0` there: `a_1 a_0^2 a_1^(-1) = a_0`,
so `a_1 a_0 a_1^(-1)` is a square root of `a_0` in `Z[1/2]`, and `Z[1/2]` is
abelian. Part (a) uses `a_1 in F_-`, which needs `n >= 2`. That is exactly
why the BG tower succeeds.
