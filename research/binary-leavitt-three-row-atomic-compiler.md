---
rg: 2
id: binary-leavitt-three-row-atomic-compiler
kind: claim
title: Compile three bounded prototype rows into one returned binary Leavitt atom
distinct_from:
  opnorm-leavitt-coarse-fine-return-row: that authenticates a coarse M2 packet, a fine M4 packet and a support row; this may bypass both packet exactifications and must output only the two inverse rows and completeness row on the prescribed root atom.
  leavitt-steinberg-bounded-area-carmichael-lift: that seeks uniformly bounded fillings for an unbounded Thompson Carmichael family; this permits a coordinate-dependent address of arbitrary length but insists that the three semantic discrepancies be literal conjugates of finitely many prototypes.
artifacts:
  - research/binary-leavitt-atomic-return-via-three-row-compiler.md
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

**OPEN.** In the finite presentation of
`St_20(L_(F_2)(1,2))`, find finitely many fixed prototype discrepancy words
`q_1,...,q_N`, a constant `C`, and a finite-matrix selection rule with the
following property.  Each `q_j` must lie in the normal closure of the fixed
defining relators and must be supplied with one fixed expression as a product
of conjugates of those relators and their inverses.  In particular, every
prototype has a fixed relator-area bound independent of matrix dimension,
selected address and coefficient window.

Whenever the rounded nontrivial spectral atom `p_U` of `z=x_13(s_1t_1)` is
nonzero, the rule may inspect the matrix coordinate and select an arbitrary
Leavitt address and finite coefficient window.  It must then produce four
operators in `p_U M_d(C)p_U` for which each of

```text
t_0s_0-p_U,
t_1s_1-p_U,
s_0t_0+s_1t_1-p_U
```

has operator norm at most

```text
C max_j ||q_j(U)-1||_op.                               (BAC1)
```

Every check at the selected address must be a literal unitary conjugate of a
prototype, so its defect is independent of address length.  This formulation
allows the depth and window to depend on the actual matrix dimension without
asking for a full multiplication table or a coherent inverse-limit module.

The phrase "finite presentation" need not assume a separate finite-
presentation theorem for the literal Steinberg group.  By
`finite-saturated-table-cover-removes-literal-group-presentation`, the
finitely many prototypes, every finite coefficient identity used by the
compiler, and finite normal-generation certificates for `z` define a
finitely presented cover surjecting onto the literal group.  It is enough to
prove `(BAC1)` for that cover: collapse of its normally generating lift of
`z` descends through the surjection.  This finite-cover formulation is the
input intended here.

## Attempts

The obvious depth-one prefix word does not work: its exact typed rectangular
model swaps equal minimal corners while leaving the two packet identities
unidentified.  Adding fixed typed Steinberg triangles, PI tests, Reynolds
ranks, or finite semisimple packet multiplicities still admits the same
escape.  The nearest operator-norm tools are
`conjugacy-addressed-opnorm-challenges-are-lossless` and
`opnorm-coordinatewise-capacity-diagonal`; neither currently constructs the
cross-typed additive completeness row.  A concrete next probe is to close
off-diagonal loops through the depth-one chart and test whether finitely many
loop discrepancies control the operator sum of the returned range
projections on `p_U`.

Nodewise recursion of the two inner Morita branches does not provide the
missing capacity by itself.
`local-morita-sibling-cells-have-a-two-qubit-periodic-absorber` assigns the
two tensor-factor Pauli groups alternately by address parity.  Every parent
has two conjugate commuting marked children and every local sibling cell is
exact at every depth, but cousins reuse the same two factors and the ambient
dimension remains four.  Thus a viable off-diagonal loop must use the
coefficient range-sum/parent-generation occurrence to detect cousin reuse;
another locally conjugated sibling Pauli check cannot control the
completeness row in `(BAC1)`.

There is a sharper language boundary for the prototype list.  By
`finite-positive-root-fragments-have-marked-regular-models`, every finite
collection of positive-root addition, multiplication, shared-occurrence and
range-sum-fold rows has an exact finite regular model with the mark
surviving.  By `partial-whitehead-cell-has-marked-finite-model`, adjoining
one complete non-scalar prefix Whitehead cell still has an exact marked
finite model.  Therefore the finitely many prototypes in `(BAC1)` cannot all
belong to either class.  At least one prototype must simultaneously couple
both binary branches through a mixed/opposite-root occurrence and attach that
occurrence to the packet payload on the prescribed `p_U` corner.  Merely
adding the scalar range-sum fold to one Whitehead actuator is below the known
finite-model firewall.

The exact finite-dimensional collapse of the full signed occurrence system
shows that such a two-branch fragment exists algebraically, but its proof
intersects coordinate-dependent additive root kernels.  Turning that
intersection into `(BAC1)` without a depth-dependent word-area loss is now
the precise operator-norm task: the selected kernel coefficient may depend
on the matrix coordinate, while every return check must still be a literal
conjugate of one of finitely many fixed prototype discrepancies.

The first literal mixed-loop completion of the private-column geometry is
also below this boundary.  In
`tagged-whitehead-two-branch-loop-has-a-three-qubit-marked-model`, adjacent
Whiteheads transport the tagged marked commutator from one branch to the
other and close a genuine null loop.  Three Pauli factors and tensor swaps
realize that loop, every crossed-zero row, and the Whitehead braid exactly
with the mark equal to `-1`.  Thus the required prototype cannot merely
return the same payload commutator through both branch charts.  It must make
the coefficient range-sum/parent-generation occurrence act on the selected
atom, thereby ruling out Pauli-factor reuse.
