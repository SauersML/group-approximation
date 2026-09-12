---
rg: 2
id: weyl-overlap-coboundaries-have-joint-bernoulli-matrix-models
kind: claim
title: Every finite Weyl orbit of overlap-central coboundaries has one canonical joint Bernoulli matrix model
distinct_from:
  overlap-hecke-coboundaries-have-canonical-finite-matrix-models: that realizes the full quasi-regular orbit Gram kernel for one overlap; this realizes all mixed moments of any finite family of conjugate overlaps on one carrier, with one common source-central block swap and exact Weyl covariance.
  two-sl3-shell-charts-have-a-rotated-flip-escape: that constructs two noncommuting covariant shell PVMs and a full transporter; this keeps the overlap coboundaries themselves in a commuting Bernoulli algebra and computes their complete joint law.
  three-parahoric-weyl-triangle-has-affine-gauge-countermodel: that additionally imposes the rank-two coweight triangle by an affine F2 translation module; this proves the more general two-overlap and arbitrary finite Weyl-orbit no-go before imposing relations among the denominator lifts.
---

Let `Lambda` be finitely generated and residually finite, let
`M<Lambda` have finite index at least two, and put `X=Lambda/M`.  For every
finite subset `Y subset X` there are exact finite-dimensional
representations `pi_j` of `Lambda`, with canonical limiting character, one
unitary `U_j in pi_j(Lambda)'`, and involutions `H_(j,x)`, `x in Y`, such
that, writing

```text
W_(j,x)=[U_j,H_(j,x)],
```

one has:

```text
Ad(pi_j(g))(H_(j,x))=H_(j,gx),
Ad(pi_j(g))(W_(j,x))=W_(j,gx)                           (JBO1)
```

whenever the displayed points lie in the chosen orbit, and

```text
W_(j,x) in pi_j(Stab_Lambda(x))',
tr(product_(r=1..k) W_(j,x_r))
 = 1  if every x in X occurs an even number of times,
 = 0  otherwise.                                       (JBO2)
```

In particular, distinct Weyl-conjugate overlap coboundaries are exactly
orthogonal, trace-zero unitaries on the same finite matrix carrier.  Their
entire mixed moment table is the independent Bernoulli table, not merely an
abstract positive Gram matrix.

For the SL3 arithmetic pair, take `M=Lambda cap h Lambda h^(-1)` and let
`Y` contain the base coset and any finite collection of its simple-Weyl
translates.  Then two noncommensurate overlap subgroups, one common
`Lambda`-central source unitary, exact coboundary form, exact Weyl covariance,
canonical lattice trace, and all mixed Hecke moments coexist with maximal
projective leakage in finite matrices.

The construction imposes no multiplication relation among the separate
symbols `H_(j,x)`.  In particular it does not satisfy the rank-two coweight
triangle.  Cairn's stronger
`three-parahoric-weyl-triangle-has-affine-gauge-countermodel` shows that even
that triangle can be added by replacing independent coordinates with an
affine `F_2` translation module; and
`heisenberg-chamber-clocks-escape-until-root-gluing` adds local dyadic and
adjacent-root packets.  Consequently the first unfenced input is not a
second overlap or a mixed moment: it is the simultaneous identification of
one arithmetic root across adjacent chambers together with its dyadic depth
transport.  Any proposed two-overlap trace-square inequality is false.

