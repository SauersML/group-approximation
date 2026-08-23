---
rg: 2
id: mixed-crt-iwahori-repair-is-labeled-pure-dyadic-rounding
kind: claim
title: Mixed CRT Iwahori repair is exactly odd-label-stabilized pure dyadic rounding
distinct_from:
  odd-congruence-iwahori-pairs-have-uniform-linear-repair: that removes the complement because the odd Iwahori image is the whole vertex image; at mixed level the support still need not reduce the dyadic vertex, and the exact residue is identified here.
  bounded-dyadic-conductor-iwahori-pairs-have-uniform-repair: that repairs each fixed unlabeled dyadic diagram; this identifies the stabilization, by arbitrarily many inert odd labels and odd degree weights, which is required to pass from pure dyadic packets to arbitrary mixed CRT packets.
  iwahori-cycle-packets-are-crt-tensor-closed: that is closure of one exact tensor construction; this is a decomposition of every finite-dimensional mixed congruence representation and of its quantitative multiplicity defect.
---

Let the two exact modular-vertex representations in the
Dogon--Vigdorovich Iwahori diagram factor through levels

```text
n_+=2^a m_+,       n_-=2^b m_-,             m_+,m_- odd.       (MCR1)
```

For the joint edge quotient, CRT gives canonically

```text
Q_(a,b;m_+,m_-)=D_(a,b) x O_(m_+,m_-),                    (MCR2)
```

where `D_(a,b)` is the joint image of the two dyadic Iwahori maps and
`O_(m_+,m_-)` is the joint image of the two odd vertex maps (with the
odd reduction of the commensuration included).  If `R_+^(a,b),R_-^(a,b)`
are the two pure-dyadic restriction matrices, restriction of the mixed
vertex representations to `(MCR2)` has the form

```text
R_+^(a,b) x_(+,omega),       R_-^(a,b) x_(-,omega)       (omega in Irr(O)),
                                                                  (MCR3)
```

independently in every odd label `omega`; physical rank in that fiber is
weighted by `dim(omega)`.  Labels which do not factor through the
corresponding odd vertex quotient simply have no columns on that side.
Thus odd and dyadic irreducibles can be correlated by arbitrary direct-sum
multiplicities, but there is no further mixed restriction coefficient.

Moreover there is one Selberg constant `kappa>0`, independent of all four
levels, such that edge-generator defect `epsilon` pays the full mixed
restriction mismatch

```text
L=sum_(omega,lambda) dim(omega) dim(lambda)
  |(R_+ x_(+,omega)-R_- x_(-,omega))_lambda|
  <= 2 kappa^(-2) epsilon^2 d.                            (MCR4)
```

Consequently the mixed-congruence sector has a uniform linear HS repair
constant if and only if the following **pure dyadic, inert-label-stabilized
integer Hoffman constants** are uniform in `a,b` and in the joint odd
quotient `O`: for its finite label set `Irr(O)`, with weights
`w_omega=dim(omega)`, and every pair of nonnegative multiplicity families
of equal total weighted vertex dimension, the families can be changed,
preserving both total dimensions, so that

```text
R_+ y_(+,omega)=R_- y_(-,omega)                 (every omega),   (MCR5)
```

with weighted changed physical rank at most `H` times the weighted
discrepancy in `(MCR4)`.  If `H` is such a bound, the usual change-on-small-
rank construction and a second Selberg polar alignment give a mixed linear
repair constant

```text
K_mix <= 8/kappa
  +(2 sqrt(2)/kappa+32 sqrt(2)/kappa^2) sqrt(H),          (MCR6)
```

independently of `m_+,m_-`, the number and degrees of odd types, and
dimension.  (This is a convenient bookkeeping bound, not an optimization.)
Conversely, testing a
mixed repair theorem at `m_+=m_-=1` gives the corresponding pure dyadic
bound, while testing it after adjoining arbitrary odd quotient types gives
the stabilized bound.

This is the exact CRT closure statement.  Odd Selberg averaging does fiber
uniformly and introduces no new spectral constant.  It does **not**, by
itself, reduce arbitrary mixed packets to the already recorded unlabeled
pure-dyadic theorem: the polar support commutes with
`D_(a,b) x O`, but need not reduce either full dyadic vertex, and global
dimension preservation couples the odd fibers.  The sole additional
algebraic gate is therefore label-stability of the dyadic integer Hoffman
bound, not an odd expansion or odd-irrep problem.
