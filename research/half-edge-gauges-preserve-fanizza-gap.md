---
rg: 2
id: half-edge-gauges-preserve-fanizza-gap
kind: claim
title: Half-edge gauge duplication preserves the Fanizza game gap and costs only fixed packet mass
distinct_from:
  private-gauges-close-fanizza-triangle: that constructs the exact HALT packet and closes its triangle torsor; this proves that the added gauge copies do not weaken finite-dimensional logical soundness or dilute the Pauli carrier.
  gauge-doubling-gives-selector-flip-symmetries: that proves semantic preservation for one share pair per context incidence; this treats several half-edge share pairs with one common logical product and the simultaneous packet PVM.
  capacity-gated-common-source-gram-word-cell: that still has to put all decoded contexts on one Gram state; this proves that, once such a state is supplied, the refined gauge/menu packet has the original static game gap.
---

The half-edge refinement used to close the exact Fanizza triangle does not
create a new finite-dimensional cheating strategy, provided two finite rows
are included explicitly:

1. every half-edge share pair is tied to the **same global logical word**;
2. all private Pauli pairs form one fixed central product with common sign
   `J`, rather than unrelated packet copies.

The first row preserves semantics.  The second preserves one joint spin
scale and makes the incidence-private tensor model a fixed finite group type.

## Exact decoder equivalence

Let `B` be a finite BCS with logical involutions `X_x`.  For every half-edge
`h=(c,e,x)`, introduce commuting involutions `A_h,B_h` and impose

```text
A_h B_h=X_x.                                             (HEG1)
```

In every lifted context, replace each use of `X_x` by any one of its products
`A_hB_h`, and include all half-edge shares incident to that context in the
commuting context algebra.

Given an exact representation of the refined system, forgetting all shares
leaves a representation of `B`: `(HEG1)` identifies every lifted logical
product with the original `X_x`, and each lifted predicate is the original
predicate evaluated on those products.

Conversely, every exact representation of `B` extends to the refined system.
For each graph edge use the incidence-private Pauli factor in
`private-gauges-close-fanizza-triangle`, put the endpoint `A` shares in its
`Z` and `X` charts, and set `B_h=X_xA_h`.  Hence the forgetful map has a
section and

```text
the original and half-edge-refined systems have exactly the same
finite-dimensional perfect logical models.                       (HEG2)
```

The statement fails if `(HEG1)` uses an edge-private logical copy `X_(e,x)`
instead of one global `X_x`.  Then each context can choose its allowed
logical assignment independently and the gauge bridges compare only private
shares.  This is the minimal new escape introduced by careless duplication.

## PVM coarsening preserves the static game energy

After exactifying a fixed context packet, let

```text
P_(c,S,r,epsilon),       r in S subset R_c             (HEG3)
```

be its joint PVM on the sum of selected menu types, where `r in R_c` is an
original allowed assignment, `S` is the active support-menu type, and
`epsilon` records all half-edge gauge signs.  Define the coarsened PVM

```text
Pbar_(c,r)=sum_(S containing r,epsilon)
                 P_(c,S,r,epsilon).                    (HEG4)
```

These projections are orthogonal and sum to the same selected carrier.  No
forbidden original assignment is introduced.  Moreover the decoded logical
observable is

```text
Abar_(c,x)=sum_r r_x Pbar_(c,r)
           =sum_(S,r,epsilon) r_x P_(c,S,r,epsilon),    (HEG5)
```

which is exactly the packet product observable `A_hB_h`, independently of
which half-edge `h` at `(c,x)` is used.

Let `G` be any common Gram matrix on which the packet rows are evaluated.
If the approximate product ties satisfy

```text
sum_h ||(A_hB_h-X_x)G||_2^2 <= E_tie,                  (HEG6)
```

then, after the fixed packet exactification error `E_pkt`,

```text
sum_(c,x)||(Abar_(c,x)-X_x)G||_2^2
 <= C_B(E_tie+E_pkt).                                  (HEG7)
```

Here `C_B` is only the maximum finite half-edge multiplicity in the compiled
instance.  Predicate rejection is unchanged by `(HEG4)`, since the lifted
support projects into `R_c`.  Therefore the original one-Gram BCS inequality
applies with the **same game gap**:

```text
(1-omega^*(B))||G||_2^2
 <= C_B(E_tie+E_pkt+E_anchor+E_hol).                   (HEG8)
```

Half-edge duplication changes only the fixed comparison constant; it does
not change `omega^*(B)` and introduces no dimension-dependent loss.

## One joint Pauli packet has no exponential mass dilution

Let `M` be the total number of private gauge bits on all graph edges.  Impose
the cross-edge commutation relations and common central sign which make them
one extraspecial Pauli group

```text
E_M=<J,Z_1,X_1,...,Z_M,X_M>.                            (HEG9)
```

On the `J=-1` sector it has one irreducible spin type of dimension `2^M`,
while

```text
|E_M|=2^(1+2M).                                        (HEG10)
```

Its Plancherel mass is therefore

```text
(2^M)^2/|E_M|=1/2.                                     (HEG11)
```

Thus adding incidence-private gauge qubits does **not** multiply the selected
spin density by `2^(-M)`.  All gauges occupy one spin simple whose canonical
mass is always one half.  Fixed finite-group exactification also has constants
independent of the eventual matrix dimension.

For the support-adaptive context menu of
`private-gauges-close-fanizza-triangle`, let

```text
q_menu=sum_(empty != S subset R_c) q_(rho_S).          (HEG12)
```

Every summand has dimension `D`, so

```text
tau(q_menu)=N_c D^2/|K_(R_c)|>0,                       (HEG13)
```

where `N_c=2^|R_c|-1`.  Combining it with the joint spin type costs the fixed
factor `tau(q_menu)/2`.  This number may be tiny, but the compiled Fanizza
instance is fixed; it is positive, computable, and independent of matrix
dimension.  Every positive Gram/capacity lower bound is merely multiplied by
the finite minimum of these packet masses.

## Remaining escape is not caused by duplication

The preceding decoder starts from one common `G`.  Finite packet restriction
tables still do not force the selected Schur carriers of different contexts
to accept that same `G`; that is the pre-existing
`capacity-gated-common-source-gram-word-cell` problem.  Half-edge duplication
neither solves nor worsens it.

If the compiler omits the common product ties `(HEG1)`, independent logical
copies destroy shared consistency.  If it includes `(HEG1)` but omits the
cross-edge Pauli relations, the logical decoder `(HEG4)--(HEG8)` still works,
but the exact tensor-factor description and the uniform spin-mass certificate
`(HEG11)` are no longer forced by one finite packet.  The minimal robust
packet is therefore precisely

```text
all half-edge products tied to the original X_x
  + one common extraspecial group E_M
  + the already required triangle two-cell.            (HEG14)
```

No additional mixed logical relation is required.
