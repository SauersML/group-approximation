# Controlled nested reset chain: exact local content and promotion audit

Date: 2026-08-20

This note records the controlled nested reset chain (CNRC) proposal against
the current constant-depth Schur frontier.  It preserves the useful finite
calculation and separates it from the two additional theorems needed for an
ordinary-group normalized-Hilbert--Schmidt obstruction.

## 1. The local model

On a selector corner `c`, the proposed next-level generators have the form

```text
c (fresh operator) + (1-c).
```

The reported two-level model on `C^64` verifies a distinguished exact
representation in which the first marked sign is globally negative, the
second marked sign is negative exactly on the selected corner, all next-level
operators preserve that corner, and the corner-restricted endpoint forgets
the old selector.  This is valuable completeness evidence: it avoids literal
nesting of the old selector center, type-preserving HNN stationarity, and the
branch-flip cancellation fence.

On the balanced reset ray the proposed bookkeeping is also arithmetically
consistent.  If the two ray parameters are `K_0,K_1`, then

```text
n_next/n = 2(K_0+K_1)/(2K_0+K_1),
lambda   = (2K_0+K_1)/(2K_0+2K_1)<1.
```

For `K_0=K_1=1`, this gives `n_next/n=4/3` and `lambda=3/4`.

The computation should be retained as a candidate finite incidence, but it
does not yet prove the universal type-vector assertion `(A1)`: the repository
does not contain a finite ordinary-group presentation or a replay script from
which all exact `J=-1` irreducibles can be enumerated.  More strongly,
`finite-packet-cannot-realize-absorbing-contraction` proves that no finite
packet table can satisfy `(A1)--(A3)` through the full absorption depth.  Its
negative regular summand is an exact finite-dimensional counterrepresentation.

## 2. First promotion gate: the controlled block is additive

The expression `c u+(1-c)` is a group-algebra operator, not a group word.
`central-corner-block-is-not-a-group-word` proves this already for one binary
control and one commuting payload involution by evaluating the four joint
characters.  Naming the controlled block as a generator proves nothing about
its unwanted sectors unless ordinary group relations force the graph of this
operator identity in every relevant representation.

The `C^64` witness therefore establishes one exact completeness model, not
soundness for arbitrary exact or approximate group representations.  The
missing finite problem is stronger than character enumeration: first produce
an explicit group presentation whose complete irreducible table realizes the
claimed controlled incidence, including every complementary type.  The
finite-selector induction and controlled-phase barriers predict extra sectors
for a standalone finite gadget, so a successful construction must couple them
to a proper corner, an infinite payload, or an energy-paying holonomy.

There is now a narrower finite-group escape from this gate. If the control
and payload are completed to Pauli pairs, the same operator is `CZ`, and
`controlled-pauli-corner-has-clifford-groupification` realizes its conjugation
action by a finite semidirect product. In every marked representation the new
stable letter has form `CZ tensor V`, with `V` an arbitrary multiplicity
involution. Hence this promotes the CNRC cell exactly if its incidence table
uses the block only through Pauli conjugation. It does not promote any step
which reads the stable-letter sign, trace, or spectral projection. The finite
replay and holonomy obligation is recorded as
`controlled-nested-reset-needs-clifford-holonomy`.  Covariance alone is not
enough: `clifford-covariance-atlases-have-regular-flow` identifies the finite
graph-of-groups Plancherel countermodel for every covariance-only chain.

## 3. Second promotion gate: fixed-depth rank mesh is not a density gap

Corner-normalized rank is just as continuous in matrices as in a finite
corner of a `II_1` factor once the corner has positive trace.  If the corner
has small trace, `corner-renormalization-cost` charges the inverse square root
of that trace when converting ambient normalized-HS error to the corner norm.

More decisively, `fixed-depth-rank-mesh-has-zero-hs-density` shows that a
rank-lattice quantum at fixed depth has size only

```text
O(lambda^(-m)/d).
```

Tensor amplification refines this to `O(lambda^(-m)/(kd))` without changing
any normalized-HS microstate data.  Thus the proposed phrase "quantization
amplification at constant depth" cannot supply the positive floor required
by `finite-depth-contractive-computation-ladder`.

This does not invalidate the constant-depth strategy.  It says that `(A1)`
must be a genuine positive-density restriction/capacity inequality, not a
rounding residue.  Such an inequality would survive amplification.  Its
finite-matrix-only asymmetry must then enter through a non-functorial
exactification or cross-context theorem which fails for the exact tracial
model, as required by `trace-functorial-bcs-signal-groupification-impossible`.

## 4. Corrected CNRC target

The proposal contributes a concrete candidate to
`q-masa-to-fresh-packet-morita-bridge`, with four obligations:

1. give the controlled two-level cell as an explicit ordinary group, not
   only as block matrices; the current candidate is a Clifford semidirect
   product whose stable letters are used only through covariance;
2. enumerate every local marked type, while retaining a genuinely global
   two-cell or holonomy constraint not reducible to a finite restriction
   graph;
3. prove an amplification-stable positive-density functional with
   `lambda<1`, rather than an integer mesh discrepancy; and
4. robustify that fixed finite cell by the existing packet exactification and
   shared-overlap estimates while retaining the marked tracial completeness
   representation.

The reported local model makes obligation 1 sharply falsifiable.  A full
finite restriction graph necessarily has the regular stationary ray, so a
rational separating functional on that graph alone cannot exist.  A positive
certificate is meaningful only after an explicit two-cell acts on the edge
intertwiner multiplicities or an infinite ambient relation supplies the
nonlocal density inequality.  Once such a certificate exists, the
fixed-depth analytic robustification is already available.
