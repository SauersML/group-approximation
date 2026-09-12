---
rg: 2
id: b7-faithful-two-cell-retains-or3-prefix-defect
kind: claim
title: Every residually finite B7-faithful two-cell retains the oriented OR3 prefix defect
artifacts:
  - experiments/or3_cycle_raw_prefix_covariance.py
distinct_from:
  canonical-b7-or3-corner-defeats-finite-prefix-actors: that treats finite Bass--Serre actors and freely chosen transporters; this treats an arbitrary non-Bass--Serre collection of two-cell relators when the resulting relative group remains residually finite with B7 embedded.
  four-cap-two-chart-mixer-has-finite-clifford-evaluator: that constructs one Clifford evaluator for a different four-cap selector mixer; this gives the canonical obstruction for every finite total actor, and more generally every relatively residually finite actor, in the exact B7 prefix corner.
---

**ESTABLISHED RESIDUALLY FINITE TWO-CELL FIREWALL.**  Retain the notation and the
rational natural representation `rho` of
`K=B_7` from `canonical-b7-or3-corner-defeats-finite-prefix-actors`.  Let
`Pi=<K,S | R>` be any finite relative presentation, where `R` may contain
arbitrary relations among several auxiliary letters and elements of `K`.
No Bass--Serre or graph-of-groups hypothesis is imposed.

Suppose `Pi` is residually finite and the displayed map `K -> Pi` is
injective.  Since `K` is finite, residual finiteness gives finite quotients

```text
phi_n:Pi -> F_n                                             (BTF1)
```

which are eventually injective on `K` and separate an increasing exhaustion
of the nonidentity elements of `Pi`.  The left regular representations of
the `F_n` are canonical matrix microstates of `Pi`, and every two-cell in
`R` is exact.  Their restrictions to `K` are `[F_n:K]` copies of the regular
representation of `K`.  Consequently, for every `T in C[K]` and all large
`n`,

```text
tau_(F_n)(T)=tau_K(T),
tau_(F_n)(p_rho T)=tau_K(p_rho T).                       (BTF2)
```

Apply `(BTF2)` to the selected source, profile Gram, and oriented prefix
defect `D` in `(BPC2)--(BPC5)`.  In every sufficiently large quotient in
`(BTF1)`,

```text
tau_(F_n)(p_rho X^*X)=1/61440,
tau_(F_n)(p_rho P)=1/46080,
||p_rho D||_(2,tau_(F_n))^2=1/92160,                    (BTF3)
```

while every relator in `R` has zero defect.  Hence no estimate

```text
||p_rho D||_2^2 <= C E_R+o_canonical(1)                (BTF4)
```

can follow from such a two-cell.  Common amplification changes neither
side.  This covers every construction whose total relative group is a
finite Clifford, Pauli, permutation, or projective-holonomy group, and every
residually finite non-Bass--Serre attaching group.  A viable finite
presentation must therefore fail relative residual finiteness at the B7
packet; producing a nontrivial curvature relation or destroying a packet
retraction is not enough.

A single nonfaithful finite evaluator does not by itself prove the canonical
statement, because its kernel may violate canonical moment tests.  It does
refute representation-universal finite-dimensional soundness.  The stronger
claim above uses either an actually finite total actor or the asymptotically
faithful quotient sequence `(BTF1)`.

## The smallest coupled curvature cell still forgets orientation

The exact artifact also audits the most direct one-relator coupling.  Put

```text
R_2=2q_2-1,
A=A_(c_3,x_31),
B=B_(x_31).                                             (BTF5)
```

The c3 incidence row `Aq_3=q_3B` is paid and exact.  One may try to attach
the ordinary non-Bass--Serre curvature-matching cell

```text
[A,R_2]=[B,R_2].                                       (BTF6)
```

In the rational B7 witness both multiplicative commutators in `(BTF6)` are
exactly

```text
J_04=diag(-1,1,1,1,-1,1,1).                           (BTF7)
```

The natural signed-permutation representation of `B_7` is faithful, so
`(BTF6)` is an equality of group elements in `K`, not merely an accidental
block identity.  The exact relative presentation obtained by attaching
this cell is therefore still the finite group `K` itself.  Its canonical
regular representation is the smallest exact finite presentation/corner
model of the attempted coupling.

Nevertheless the prefix-compressed additive commutator is the oriented
matrix unit

```text
D=q_3[B,q_2]q_1P=|e_4><e_0|,                          (BTF8)
```

with the positive values `(BTF3)`.  Thus matching scalar, projective, or
full multiplicative curvature only transports the omitted commutator; it
does not pay its source-to-target half.

The literal minimal extra datum is instead the oriented corner row

```text
A_(c_3,x_31) q_3q_2q_1P=q_3q_2q_1P B_(x_31),          (BTF9)
```

equivalently `D=0` after the already paid incidence terms.  Imposing all
such rows as representation-universal relations on the exhaustive Fano
frame is forbidden by
`full-support-factor-refutes-exact-exhaustive-typed-cap-chain`.  Therefore
the remaining finite possibility is narrower than an ordinary Clifford
two-cell: it must authenticate the oriented source Gram in finite matrix
coordinates, fail relative residual finiteness at B7, and avoid making
`(BTF9)` an exact identity in the marked full-support completion.
