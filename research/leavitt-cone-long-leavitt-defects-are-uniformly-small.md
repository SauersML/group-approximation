---
rg: 2
id: leavitt-cone-long-leavitt-defects-are-uniformly-small
kind: claim
title: In every unitary representation of the Cuntz-cone cover, the long Leavitt defects [x_ab(s_omega^*), x_bc(s_omega')] x_ac(delta_(omega omega'))^(-1) over all equal-length Cuntz word pairs are uniformly O(delta)-trivial (LD), which would give the cone-cover head bound (QC) by a two-step chain
distinct_from:
  leavitt-cone-head-bound-is-linear-in-shadow-dimension: that proves each generator-level Leavitt reduction costs O(delta) and gets a head bound linear in the collision depth; this asks for the accumulation-free statement, one O(delta) cost for a whole Cuntz word at once, which removes the linear factor.
  leavitt-cone-cover-far-cross-relators-are-uniformly-small: that makes the far cross and middle-coherence relator families uniformly small by Kazhdan averaging; the long Leavitt defects are adjacent-index relators with entries from opposite halves, which that averaging provably cannot reach (every Kazhdan subgroup of Gamma is conjugate into one half).
  leavitt-cone-head-bound-is-finite-congruence-gluing: that is the finite-gluing form of (QC) itself; this is a sufficient condition for (QC) that is a uniform stability statement about one explicit family of elements of K.
artifacts:
  - research/leavitt-cone-head-bound-linear-shadow-dimension-proof.md
  - experiments/leavitt-reduction-cost-2026-09-17/verify_leavitt_reduction.py
---

**OPEN** (lane swarm-0917-w20-w20-nh-last1, group-rings, decomposition; unreviewed).

**Setting** as in `leavitt-cone-head-bound-is-linear-in-shadow-dimension`. For Cuntz words `omega, omega'` of the same
length, `s_omega^* s_omega' = delta_(omega omega')` in `R`. So the element

```text
lambda_(abc)(omega, omega') = [x_ab(s_omega^*), x_bc(s_omega')] x_ac(delta_(omega omega'))^(-1)
```

lies in `K`, and it is a Leavitt defect with `x_ab` in `Delta_-`, `x_bc` in `Delta_+` and `x_ac` in `Delta_0`.

**Claim (LD).** There is a constant `C` such that for every genuine `rho : Gamma -> U(M)`, every `L`, and all
`omega, omega'` in `{1,2}^L`, with `(a,b,c) in {(4,5,6), (5,4,6)}`,

```text
|| rho(lambda_(abc)(omega, omega')) - 1 ||_2  <=  C delta .                                     (LD)
```

## What is established around it

- **(LD) implies (QC), with `||rho(z) - 1||_2 <= 2 (6 C_1 + 4 C) delta`.** Step 6 of
  `leavitt-cone-head-bound-linear-shadow-dimension-proof` records the argument. Run `(LR)` with `t = s_omega^*` and
  `s = s_omega`: the exact word identities I1–I5 need no property of `t` and `s` beyond `t in R_-`, `s in R_+` and
  `t s in {0, 1}`. That is one backward step. Then an exact swap to a colliding `s_omega'`, which exists because
  `R_+/J_+` is finite. Then one forward step with `eps = 0`. Only `r3` changes, from a generator-level defect to
  `lambda(omega, omega)` and `lambda(omega, omega')`.
- **The linear bound.** `||rho(lambda(omega, omega')) - 1|| <= L c'` for some fixed `c'`, by reducing one letter at a
  time with the same bookkeeping. `(LD)` asks exactly that this accumulation does not occur.
- **(LD) holds for ring-induced representations** in which the Leavitt relations `t_i s_j = delta_ij` hold in the
  shadow ring. There each `lambda` is exactly `1`.

## How it can fail

A family of genuine representations with `delta -> 0` and `sup_omega ||rho(lambda(omega, omega')) - 1||_2 / delta`
unbounded refutes it. By the linear bound, such a family needs word lengths `L -> infinity`.

A refutation of `(LD)` does **not** refute `(QC)`. The two are not known to be equivalent.

## Attempts

- (swarm-0917-w20-w20-nh-last1) Created as the accumulation-free hole left by
  `leavitt-cone-head-bound-is-linear-in-shadow-dimension`. Kazhdan averaging (`(U1)`–`(U3)`) cannot reach it, since
  `lambda` pairs adjacent indices across halves. That is the recorded obstruction in
  `leavitt-cone-cover-far-cross-relators-are-uniformly-small`.
