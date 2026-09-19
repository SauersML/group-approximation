---
rg: 2
id: circulated-criterion-condition-iii-locus
kind: claim
title: Condition (iii) enters the circulated criterion only in the word estimate
distinct_from:
  multi-mover-collapse-criterion: That is the mathematical statement that the single-mover hypothesis can be replaced by finitely many movers; this is the source-anatomy statement locating where in the circulated proof that hypothesis is consumed, which is what makes the replacement checkable.
  matricial-mautner-fixed-subspace: That is a theorem, proved independently here; this is a statement about a document, warranted only by a second-hand relay.
artifacts:
  - research/artifacts/collapse-criterion-source-2026-08-16.md
---

In the circulated action-form criterion (Theorem 4.1 there), the hypothesis

    Gamma = <H, gamma>,     H = t Gamma t^-1 < Gamma

is used at exactly one point: writing an arbitrary `g in Gamma` as a word in
`H`-letters, which displace the witness site by zero, and `gamma^{+-1}`
letters, which displace it by `k_n`, to obtain

    delta_n(g)  <=  C_g k_n.

Every other ingredient — the involution-to-projection passage
`e_x = (1 - v_x)/2`, the commuting projection lifts, the rank distance
`d_n(x,y) = rank(e_{x,n} - e_{y,n})`, the operator-norm-to-equal-rank step,
the `k_n`-scaled Hilbert--Schmidt rescaling, the cocycle, and the final
contradiction — is independent of it.

Two further anatomy facts recorded with the same warrant.  The witness site is
`x_0 = t Gamma`, whose `Gamma`-stabilizer is exactly `H`, so the named defect
is `b = a_{gamma x_0} a_{x_0}`.  The final contradiction is a matricial
Mautner lemma: stable finiteness of the corona forces the fixed subspaces of
`Gamma` and of its conjugate copy `H` to coincide.

The concrete instance there is `Gamma = EL_3(F_2[x,y])`, Kazhdan by
Ershov--Jaikin-Zapirain, self-embedded by the ring map `x |-> x`, `y |-> xy`
with image `EL_3(F_2[x,xy])`, and condition (iii) discharged by an explicit
lemma exhibiting `Gamma = <H, e_12(y)>`.
