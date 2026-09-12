---
rg: 2
id: gapped-face-pinchings-give-same-hilbert-code-pvm-rounding
kind: claim
title: A uniform adjoint face-Hamiltonian gap gives same-Hilbert code-PVM rounding
distinct_from:
  operator-unique-neighbor-cosystolic-rounding: that states the desired conclusion as an open operator-cosystolic property; this proves it from one explicit spectral-gap hypothesis.
  sequential-pinchings-have-sharp-linear-disturbance-loss: that pinches individual coordinates in an arbitrary order; this uses whole parity-face pinchings and a global Hamiltonian gap before rounding.
  binary-face-pvm-is-determined-by-coordinate-reflections: that reconstructs bounded exact faces after coordinate correction; this supplies the coordinate correction itself.
---

Let exact bounded-width binary face PVMs have **literally shared** coordinate
reflections `Q_1,...,Q_L`, and let them generate a finite von Neumann algebra
`N subset M`.  For face `c`, let

```text
Phi_c(X)=sum_a P_(c,a) X P_(c,a)                           (GFP1)
```

be the `L_2`-orthogonal pinching onto the commutant of that face algebra, and
put

```text
H=(1/|C|)sum_c (I-Phi_c),
K=intersection_c ran(Phi_c)=N' intersection L_2(M).        (GFP2)
```

Assume the operator-valued syndrome gap

```text
<X,HX> >= gamma ||X-E_(N')(X)||_2^2                       (GFP3)
```

for one `gamma>0` independent of code length and matrix dimension.  Assume
also bounded coordinate occurrence and a classical LTC correction constant
for the scalar code.  Then complete-pair commutator energy `epsilon` rounds
on the same Hilbert space to a joint PVM supported on codewords with average
squared coordinate displacement

```text
O(epsilon/gamma).                                          (GFP4)
```

Literal sharing is an explicit hypothesis, not a consequence smuggled in
from average equality.  Passing from the repeated occurrence presentation
to this hypothesis is the separate
`repeated-ldpc-shared-face-marginal-synchronization` gate.

For an exact local face, its commuting coordinate adjoint involutions give

```text
||Q_j-Phi_c(Q_j)||_2^2
 <= (1/4)sum_(i in c)||[Q_i,Q_j]||_2^2.                   (GFP5)
```

Indeed `Phi_c` is the product of the commuting orthogonal projections
`(I+Ad(Q_i))/2`, and `I-product P_i <= sum(I-P_i)` as quadratic forms.
Bounded occurrence and averaging `(GFP5)` over `c,j` bound the Hamiltonian
energy by a universal multiple of the complete-pair energy.  Equation
`(GFP3)` therefore makes

```text
B_j=E_(N')(Q_j)
```

close on average to `Q_j`.

The crucial centrality is automatic.  Since `Q_j in N`, for `z in N'` the
conditional-expectation bimodule identities and `zQ_j=Q_jz` give

```text
B_j z=E_(N')(Q_j z)=E_(N')(z Q_j)=z B_j.                  (GFP6)
```

Thus every `B_j` lies in `Z(N')`; all their spectral signs commute.  If
`S_j=sign(B_j)`, orthogonal projection and scalar spectral calculus give

```text
||Q_j-S_j||_2^2 <= 2||Q_j-B_j||_2^2.                      (GFP7)
```

The commuting `(S_j)` have one joint classical distribution.  Their parity
defect is controlled by `(GFP7)` because the original shared face marginals
satisfy every parity exactly.  Apply the classical LTC correction
independently on each joint atom, moving its word to the code; functional
calculus of the common PVM realizes this correction inside `M` with exactly
the classical average Hamming cost.  Bounded-width face reconstruction then follows from
`binary-face-pvm-is-determined-by-coordinate-reflections`.

If the check hypergraph has bounded coloring/overlap, the detectability lemma
or alternating-projection theorem implements `E_(N')` by repeated layers of
the local pinchings, with convergence controlled by the same `gamma`.  The
gap, not the ordering, prevents disturbance accumulation.
