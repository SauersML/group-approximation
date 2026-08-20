# Reverse Kleene and finite-dimensional multiplicity holonomy

Date: 2026-08-20

## Status

This audit does **not** prove the existence of a non-hyperlinear group.  It
integrates the supplied continuation into Cairn, removes one unnecessary
completeness demand, proves a new canonical-trace carrier obstruction, and
reduces the reversible-predicate alternative to cancellation of one explicit
external multiplicity commutator.

Several headline observations in the supplied continuation were already
present in the graph and were not duplicated:

| Observation | Existing Cairn claim |
|---|---|
| Reverse-Kleene diagonal with index-dependent constants | `kleene-halting-mark-collapse-diagonal`, `instance-modulated-kleene-microstate-diagonal` |
| Fanizza projection `D_m=(1-x_(D,m))/2` is the native mark | `fanizza-signal-involution-is-native-mark` |
| Group-word skeleton loses only projection overlap | `fanizza-doubling-carriers-form-orthogonal-flag`, equation `(FOF5)` |
| V4 has five failure occurrences but only four effective characters | `clifford-radical-antiphase-routing-has-character-capacity` |
| Dummy radical bits preserve the fatal ratio | the same claim, equation `(CRAC4)` |
| A4 packet has four rectangle holonomies | `atlas-a4-packet-four-rectangle-normal-form` |
| All `9,999,360` GL5 positions were screened; 202 packet models all fail collision | `atlas-a4-gl5-packet-collision-screen` |
| The remaining A4 scalar target is the `3/512` ellipse | `atlas-a4-root-energy-ellipse-ceiling` |

The three new mathematical points are below.

## 1. HALT completeness is representation-theoretic, not tracial

The reverse-Kleene theorem needs

```text
m halts  =>  w_m!=1 in Gamma_m.                         (1)
```

To prove (1), one representation `pi_m` with `pi_m(w_m)!=I` suffices.  If the
word were algebraically trivial, every representation would send it to the
identity.  No trace on `pi_m(Gamma_m)` is used in the diagonal.

If the Fanizza GNS witness acts on `H`, its countable amplification acts on

```text
H_infinity=H tensor ell2(N),
```

still detects `x_(D,m)`, and satisfies

```text
H_infinity ~= H_infinity directSum ... directSum H_infinity
```

for any fixed finite number of summands.  Thus a completion gadget may absorb
finite Schur/Clifford packet multiplicities on the HALT side.  It does not
follow that a proposed gadget extends: that exact representation still has to
be constructed.  What disappears is the stronger demand that the original
trace, or every BCS representation, extend.

This is formalized by
`kleene-completeness-needs-only-a-nontrivial-exact-representation`.  The open target
`fanizza-native-signal-groupification` was changed accordingly.  Its
finite-matrix decoder remains fully quantitative.

## 2. A single involution cannot carry a nonlinear selector

Let `A<=Gamma` be a finite elementary abelian selector subgroup.  Its minimal
character projections are

```text
e_chi=|A|^(-1) sum_(a in A) chi(a)a.
```

For an involution `d`, put `p=(1-d)/2`.

If `d notin A`, no term `da`, `a in A`, is the identity.  Therefore the
canonical group trace gives

```text
tau(d e_chi)=0,
tau(p e_chi)=1/(2|A|),
||p e_chi||_2^2=1/(2|A|).                              (2)
```

The norm identity uses
`tau(e_chi p e_chi)=tau(p e_chi)` and does not require `d` to normalize `A`.
An exact left-regular representation has zero defining-relator energy, so no
universal relator inequality can make this carrier vanish on a prescribed
nonlinear set of selector atoms.

If `d in A`, then

```text
p e_chi = ((1-chi(d))/2)e_chi.                         (3)
```

Its support is one affine parity half-space.  Equations (2)--(3) prove the
two-way obstruction in
`single-involution-cannot-be-a-nonlinear-selector-carrier`.

This does not rule out the native Fanizza word as the **final mark**.  It
rules out asking its negative projection to double as the nonlinear local
predicate carrier.  The predicate information must live in a
higher-dimensional packet, a signed Hecke block, or finite-dimensional
multiplicity holonomy.

## 3. Reversible commutators compute AND exactly

Let `P,Q` be commuting control projections, commuting also with a Pauli pair
`X,Z`, and suppose `[X,Z]=J` is central.  Define

```text
U_P=(1-P)+PX,
V_Q=(1-Q)+QZ.
```

On the four joint control sectors, the two gates fail to commute only on
`PQ`.  Hence

```text
[U_P,V_Q]=(1-PQ)+J PQ.                                  (4)
```

The left side is a group word once the controlled gates are introduced as
implementers.  Equation (4) therefore compiles a Boolean conjunction into a
noncommutative group commutator without expanding the controlled gates as
group-ring sums.

The exact obstruction appears on the multiplicity space.  On one irreducible
finite packet isotypic component, Schur's lemma gives

```text
U=C_U tensor R,       V=C_V tensor T,
```

and direct multiplication gives

```text
[U,V]=[C_U,C_V] tensor [R,T].                           (5)
```

Covariance fixes `C_U,C_V` but leaves `R,T` arbitrary.  The unwanted
commutator in (5) can completely alter the Boolean phase.  If `R,T` commute,
or if both implementers use the same multiplicity unitary, it vanishes
exactly.

This is `controlled-pauli-commutator-is-and-times-multiplicity-commutator`.
The new open cell
`fanizza-shared-multiplicity-predicate-circuit-cell` asks for precisely this
cancellation for the three fixed nonlinear predicate shapes in the Fanizza
compiler, while keeping their selector actions different.

## 4. Quantitative endpoint

Suppose the cell gives a group presentation and, for a finite-dimensional
tuple of squared relator energy `E_group`, a BCS strategy satisfying

```text
epsilon_BCS <= A_m E_group,
||U(d_m)-X_(D,m)||_2 <= B_m sqrt(E_group).              (6)
```

On a NONHALT instance, the Fanizza estimate gives

```text
||X_(D,m)-I||_2 <= 2 sqrt(C_m epsilon_BCS).
```

Combining with (6),

```text
||U(d_m)-I||_2
 <= (B_m+2sqrt(C_m A_m)) sqrt(E_group).                 (7)
```

Write `K_m=B_m+2sqrt(C_m A_m)`.  Any computable positive threshold

```text
delta_m < 1/(4 K_m^2)                                   (8)
```

makes the right side of (7) less than `1/2`, hence uniformly below
`sqrt(2)`.  The constants may be arbitrarily bad functions of `m`; they are
fixed before the recursion theorem is applied and need no relation to matrix
dimension or eventual runtime.

Together with one HALT representation detecting `d_m`, equations (7)--(8)
meet `kleene-halting-mark-collapse-diagonal`.  Therefore the only open input
on the new route is the fixed shared-multiplicity predicate-circuit cell.

## 5. Relation to the other live lanes

- The V4 character router is closed negatively: `5>4`, and dummy radical
  coordinates multiply both sides by the same factor.
- The projection recurrence is already multiplicative at the level of
  symmetric difference, but `(FOF5)` shows that the overlap `tau(AB)` is the
  sole nonlinear residue.  A universal exact overlap-zero relation is
  forbidden by the canonical trace; only finite-dimensional holonomy may pay
  it.
- The signed-Hecke projection-atlas route remains separate.  It would give an
  exact canonical-corner model and needs no Kleene argument.
- The A4/Leavitt lane remains the most finite alternative.  It is reduced to
  the established four-holonomy normal form and the open root-energy ellipse
  inequality; the GL5 screen is strong finite evidence, not a proof of the
  dimension-independent inequality.

The current machine route is therefore accurately summarized as

```text
Fanizza native mark
 + reverse Kleene
 + one arbitrary infinite HALT completion
 + finite-dimensional multiplicity-commutator cancellation.
```

The last line remains open; no non-hyperlinear group is claimed here.
