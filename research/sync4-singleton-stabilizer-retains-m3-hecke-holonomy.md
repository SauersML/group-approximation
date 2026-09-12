---
rg: 2
id: sync4-singleton-stabilizer-retains-m3-hecke-holonomy
kind: claim
title: A SYNC4 singleton equality leaves a full but verifier-blind three-by-three Hecke holonomy
distinct_from:
  one-binary-marginal-block-escape: that constructs an escape for an arbitrary binary marginal with a repeated sign fiber; this specializes the construction to the SYNC4 atom reflection, computes its complete block stabilizer, and gives an explicit two-piece Laurent group-ring holonomy.
  three-chart-loop-retains-free-multiplicity-holonomy: that gives the abstract multiplicity-unitary freedom for full chart transports; this identifies the exact M3 Hecke block left by one coordinate-reflection equality.
  literal-sync4-c2-amalgam-has-zero-selected-meet: that proves the direct atom amalgam gives zero packet meet before a common carrier is selected; this computes the residual collision algebra conditional on such a carrier.
  sync4-coordinate-atom-groupifier-cell: that asks for a common carrier on which the selected atoms agree; this proves complement holonomy survives in transport implementations but need not be killed once those selected equalities hold.
---

**ESTABLISHED.**  Let `H` be a unital star algebra and work in `M_4(H)`
with coordinate projections `e_0,...,e_3`.  Put

```text
R_0=1-2e_0.                                             (SSH1)
```

For a unitary `U in M_4(H)`, the following are equivalent:

```text
U R_0 U^*=R_0,
U e_0 U^*=e_0,
U=diag(u,V) with u in U(H), V in U(M_3(H)).             (SSH2)
```

Indeed the first two conditions are equivalent because of `(SSH1)`, and
`Ue_0U^*=e_0` implies `Ue_0=e_0U`; the two off-diagonal blocks therefore
vanish.  Conversely every displayed block unitary fixes `e_0` and `R_0`.
Thus a singleton edge removes only the collision blocks joining the selected
atom to its complement.  It leaves the **entire** `M_3(H)` unitary group on
the three unselected atoms.

This residual block has an explicit finite-support group-ring realization.
Take

```text
H=Q[z,z^(-1)] subset Q[Z]
```

with `z` the generator of `Z`, and set

```text
V(z)=1/2 [[1+z, 1-z, 0],
          [1-z, 1+z, 0],
          [0,   0,   2]],
U(z)=diag(1,V(z)).                                      (SSH3)
```

The upper `2 x 2` block of `V(z)` is

```text
H_2 diag(1,z) H_2,
H_2=2^(-1/2)[[1,1],[1,-1]],
```

so direct multiplication, with no square roots left in `(SSH3)`, gives

```text
V(z)V(z)^*=I_3.                                        (SSH4)
```

It mixes two complementary coordinate projections, has Laurent support
`{1,z}`, and fixes the selected atom exactly.  In the matrix-over-Hecke
normal form of a finite packet corner, `(SSH3)` is therefore a genuine
two-piece algebraic Hecke unitary, not merely an abstract multiplicity
operator.

Gauge the **full-chart transports** of a connected SYNC4 incidence graph
along a spanning tree.  After fixed coordinate permutations bring the atom
selected by a non-tree edge to `e_0`, the return on that chord is allowed to
be any unitary of `(SSH2)`.  Taking every tree return to be the identity and
the chord return to be `U(z)` gives a nontrivial exact cycle holonomy while
preserving every selected-atom equality.  The determinant of its
complementary block is `z`, so it cannot be gauged to the identity by a
gauge already fixed on the tree.

This is a transport-level freedom, but it is **not a semantic obstruction
for SYNC4**.  Every verifier row sees only the selected atom `e_0`, so the
whole `U(M_3(H))` block is invisible after the required atom equalities have
been installed on one common carrier.  Unlike a generic BCS atlas, the
compiler need not synchronize the complementary atoms or kill this
holonomy.  Thus singleton synchronization does not algebraically eliminate
collision blocks in a full-chart implementation, but it demotes them to
harmless gauge freedom.  The remaining load-bearing problem is creation of
the common canonical carrier and equality of the selected atoms on it.
