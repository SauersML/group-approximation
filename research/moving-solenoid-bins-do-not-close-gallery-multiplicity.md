---
rg: 2
id: moving-solenoid-bins-do-not-close-gallery-multiplicity
kind: claim
title: Moving solenoid bins preserve local covariance but do not close the gallery multiplicity reservoir
distinct_from:
  periodic-dyadic-root-clocks-keep-weyl-overlap: that gives an exact finite periodic clock with separate abelian root reservoirs; this gives the diffuse Haar-bin firewall even when every literal arithmetic root word and every Steinberg relation is retained.
  adjacent-a2-chambers-share-only-commuting-wall: that constructs an exact finite wall-rotation gauge; this shows why replacing spectral bins by moving solenoid coordinates still cannot identify the six gauges from tracial covariance data.
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that makes Connes embeddability of the whole crossed product the conditional matrix counterarchitecture; this proves the unconditional tracial no-go for every finite moving-root PVM window.
---

Put

```text
C=SL_3(Z) < A=SL_3(Z[1/2]),
N=L^infinity({+1,-1}^(A/C)) rtimes A.                   (MSB1)
```

Let `u_g` denote the actor unitary and let `P` be the half projection in the
base Bernoulli coordinate `C`.  For

```text
h=diag(2,1,1/2),             Q=u_h P u_h^*,             (MSB2)
```

the exact model has

```text
tr(P)=tr(Q)=1/2,        [P,Q]=0,        tr(PQ)=1/4.      (MSB3)
```

At the same time it supplies every finite root-spectral datum proposed in a
moving-solenoid-bin decoder.

Indeed, if `g in A` has infinite order, then

```text
tr(u_g^m)=0  for every m!=0.                             (MSB4)
```

The spectral measure of `u_g` is therefore Haar measure on the circle.  If
commuting root elements `g_1,...,g_r` freely generate `Z^r`, their joint
spectral measure is Haar measure on the `r`-torus.  Consequently the `q`
equal-arc spectral projections of one root have trace exactly `1/q`, and
the `q^r` joint atoms of one commuting wall have trace exactly `q^(-r)`.
For every actor word `a`, functional calculus gives the exact covariance

```text
u_a E_g(B) u_a^* = E_(aga^-1)(B).                       (MSB5)
```

All six adjacent-root Heisenberg relations and the Coxeter word

```text
(n_12 n_23)^3=1                                        (MSB6)
```

also hold exactly in `N`.  Thus equal Haar-bin ranks, wall-PVM agreement,
literal root-occurrence equality, actor covariance, the six Heisenberg
triangles, and the closed raw gallery word coexist with the forbidden
interior overlap `(MSB3)` in an exact finite tracial von Neumann algebra.

## The fixed-coordinate / moving-coordinate dichotomy

There are only two ways to use equal circle bins under a dyadic root shift.

1. **Keep one circle coordinate.**  Let `I_0,...,I_(q-1)` be the equal
   connected arcs and let `p(z)=z^2`.  Each set `p^(-1)(I_j)` is the union
   of two arcs of length `1/(2q)` separated by a half turn.  Its intersection
   with any one `I_k` has measure at most `1/(2q)`.  Hence

   ```text
   sum_j ||1_(p^-1(I_j))-1_(I_(pi(j)))||_2^2 >= 1       (MSB7)
   ```

   for every permutation `pi`.  Increasing `q` does not make the **total
   PVM transport energy** small.  For `z |-> z^(2^r)` and `q>=2^r`, the
   same calculation gives the lower bound `2(1-2^(-r))`.

2. **Move to the deeper solenoid coordinate.**  Choose at the target the
   root word whose spectral coordinate is literally the conjugate of the
   source word.  Then `(MSB5)` transports every bin exactly and all bin
   ranks agree.  But the six chambers now carry different maximal abelian
   root PVMs.  The off-wall roots do not admit one joint PVM, and pairwise
   common-wall agreement leaves precisely the Heisenberg multiplicity gauge
   exhibited by `adjacent-a2-chambers-share-only-commuting-wall`.  Nothing in
   `(MSB4)--(MSB6)` identifies those gauges on one common four-atom carrier.

The exact model `(MSB1)` is a firewall for the second case.  If moving-bin
data alone supplied supported transitions `B_i` on one common carrier with
vanishing leakage and with a product rotating `P` to `Q`, then
`six-edge-holonomy-energy-ledger-is-scale-free` would contradict `(MSB3)`
inside `N`.  Therefore at least one of common-carrier support, unitary
transition recovery, or multiplicity-gauge alignment is absent; the absence
cannot be charged to the root word, trace, PVM-rank, or covariance defects,
because all of those defects vanish in `(MSB1)`.

It follows that a successful arithmetic hexagon decoder must use a genuinely
matrix-coordinate quantity which is unavailable in the diffuse Bernoulli
model: finite atomic multiplicity, an integer-rank return, or an equivalent
same-reservoir conductor invariant.  Refining Haar bins, by itself, cannot
provide the missing normalized-HS payment.
