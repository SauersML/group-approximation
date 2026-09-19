---
rg: 2
id: role-multiplexing-is-minimax-max-selection
kind: claim
title: Orthogonal role multiplexing is minimax-equivalent to selecting one maximal forbidden type
distinct_from:
  independent-address-capacity-cannot-drive-selected-atom-growth: that proves a trace-capacity ceiling for copies of one payload in independent address cylinders; this computes the optimal worst-case mass of an arbitrary finite noncommuting type menu placed in orthogonal role atoms.
  simultaneous-character-packing-removes-max-loss: that assumes literal orthogonal conjugates of the full forbidden family and would retain every atom at full trace; this shows why an independent role tensor cannot supply that hypothesis without paying the inverse number of roles.
  finite-cocycle-select-forces-one-common-lcu-gauge: that wordizes a structured payload homomorphism by one controlled finite-group operator; this uses no controlled word and permits the payload projections to be completely noncommuting.
---

**ESTABLISHED.**  Let `(M,tau)` be finite tracial and let

```text
P_1,...,P_M in M
```

be arbitrary projections; they need not commute.  Let `R_1,...,R_M` be
pairwise orthogonal projections in a finite-dimensional role algebra `D`
with normalized weights

```text
r_i=tau_D(R_i),             sum_i r_i<=1.              (ORM1)
```

In `D tensor M` the role-multiplexed forbidden operator

```text
B=sum_i R_i tensor P_i                              (ORM2)
```

is a projection and

```text
(tau_D tensor tau)(B)=sum_i r_i tau(P_i).             (ORM3)
```

Thus a finite role packet really does remove the cross-context
noncommutativity of the `P_i`: every type occupies an orthogonal physical
block and no nonlinear SELECT word is needed to form `(ORM2)`.

It does **not** improve the representation-uniform mass bound.  If only

```text
sum_i tau(P_i)>=V                                      (ORM4)
```

is known, the best constant `c` for which `(ORM3)>=cV` holds for every
projection family is

```text
c=min_i r_i<=1/M.                                      (ORM5)
```

The upper bound is attained by concentrating all of `(ORM4)` in a type of
minimum role weight.  Equal weights `r_i=1/M` attain equality in `(ORM5)`.
Consequently

```text
tau(B)=M^(-1) sum_i tau(P_i)                           (ORM6)
```

is minimax-optimal and has exactly the same guaranteed lower bound as the
pigeonhole choice

```text
max_i tau(P_i)>=M^(-1) sum_i tau(P_i).                 (ORM7)
```

This conclusion persists for a fixed finite-group role packet.  For
example, take an extraspecial `2`-group with central involution `J_R` and
unique `J_R=-1` irreducible of dimension `2^k>=M`.  Its diagonal Pauli
atoms are pairwise orthogonal and equally weighted.  If the shared BCS
tuple commutes with the packet, finite Stone--von Neumann exactification
puts the marked sector in the form

```text
C^(2^k) tensor H,
```

with the BCS tuple in the multiplicity commutant.  Hence `(ORM2)--(ORM3)`
hold there, up to a dimension-independent `O(sqrt(E))` error in an
approximate representation.  Using only `M` atoms and discarding the rest
gives weight `2^(-k)<=1/M`; no finite-packet correction improves `(ORM5)`.

Therefore orthogonal role copies are useful bookkeeping, but they cannot
replace the payload-sensitive escape cell.  Separate typewise transporters
may now act on genuine orthogonal sources, yet their total guaranteed source
mass is still only `V/M`.  Any supercritical recurrence must additionally
move that mass into capacity not already charged to the role tensor.  By
`independent-address-capacity-cannot-drive-selected-atom-growth`, merely
adding more independent role or address atoms cancels the gain by the same
trace partition.

**Proof.**  Orthogonality gives

```text
B^2=sum_i R_i^2 tensor P_i^2=B,
```

which proves `(ORM2)--(ORM3)`.  Under `(ORM4)`, positivity gives

```text
sum_i r_i tau(P_i)>=(min_i r_i) sum_i tau(P_i)
                   >=(min_i r_i)V.
```

Conversely choose an index `j` of minimum weight, take `P_j` of trace `V`
and all other `P_i=0` (or use the evident scaled/direct-sum version when a
particular ambient trace range is prescribed).  Then `(ORM3)=r_jV`, so no
larger uniform constant is possible.  Finally
`min_i r_i<=M^(-1)sum_i r_i<=1/M`.  Equal weights prove sharpness.  The
finite-group assertion is the standard unique-spin decomposition followed
by the same calculation in its multiplicity commutant.
