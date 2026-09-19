---
rg: 2
id: sparse-relator-defects-defeat-orbitwise-classicalization
kind: claim
title: Expanding exact actor orbits can hide sparse relator defects outside every prescribed lamp ball
distinct_from:
  orbitwise-relator-classicalization-separates-mihailova-kernel: that proves separability once relators kill the entire free-subgroup orbit; this proves that finite-ball relations, pairwise lamp moments, and vanishing average relator defect cannot supply that hypothesis.
  simple-lamp-normalizers-have-unitary-multiplicity-fibers: that hides actor classicality in a unitary multiplicity fiber; this is already permutation-valued and hides two relator defects in one growing transitive classical orbit.
  pt-rigidity-allows-nontight-regular-tails: that concerns high-dimensional approximate representations of a Kac--Moody lattice; this gives an elementary exact free-actor packet over expanding finite quotients of a property-(T) group.
---

There is a finitely presented residually finite property-`(T)` group `Q_0`
and an epimorphism from a finite-rank free group

```text
pi_0:E_0=F(S union {z})->Q_0,
pi_0(z)=w(pi_0(S)),                                    (SRD1)
```

with finite relator set containing `r_0=z w^(-1)`, for which the following
exact counterpackets exist.  For every radius `k` there is a finite transitive
`E_0`-set `Omega_k`, a basepoint `o_k`, and the binary Bernoulli matrix model
over `Omega_k` such that:

1. the rooted labelled `k`-ball at `o_k` is exactly the corresponding ball
   of `Q_0`;
2. every defining relator moves `o(|Omega_k|)` points, and `r_0` moves
   exactly two;
3. the centered lamp observables satisfy the exact canonical pairwise law

   ```text
   tr(A_x A_y)=1_(x=y),                                (SRD2)
   ```

   and exact actor covariance; but
4. no nonempty invariant subset of `Omega_k` is a branch on which all
   relators act trivially.

One may take `Q_0=SL_3(Z)` (with one redundant generator `z=w(S)`) and its
congruence quotients.  Their Cayley graphs are expanders, so this is an exact
expanding-orbit counterpacket.  Property `(T)` and its Poincare inequality do
not turn vanishing **density** of relator defects into an invariant positive
mass of defect-free branches.

Consequently the full family of lamp conjugates in any fixed word ball,
together with all canonical pairwise lamp traces, cannot imply `(ORC4)` after
an `o(1)` cut.  A successful Mihailova argument needs genuinely global
orbitwise relator control (or an additional stability theorem that forbids
this sparse surgery), not a larger finite ball or a sharper Kazhdan constant.

