---
rg: 2
id: fanizza-product-gram-reduces-to-one-state-holonomy
kind: claim
title: A rooted product Gram reduces the native Fanizza incidence to one state-holonomy moment
distinct_from:
  one-gram-vector-decodes-a-finite-bcs-strategy: that turns one Gram operator with low full game energy into a finite-dimensional strategy; this proves how context bridges can manufacture all of its consistency rows from rooted transports.
  common-source-hnn-bridges-need-one-gram-saturation-identity: that asks four selected Hecke compressions to accept one common projection; this permits a nonprojective Gram state and isolates the single residual cycle moment.
  gauge-weyl-fanizza-incidence-rounding: that asks for a complete packet incidence compiler; this proves the state-dependent analytic gluing theorem and audits the existing bridges against it.
---

Let `B` be a finite constraint-variable BCS game.  For every context `c`,
let `P_(c,a)` be a PVM, and put

```text
A_(c,x)=sum_a a_x P_(c,a),
F_c=sum_(a forbidden for c)P_(c,a).                    (FPG1)
```

Let `Y` be a connected context-incidence graph.  An oriented incidence edge
`e:c->d`, labelled by a variable `x`, carries a unitary `U_e` and the
state-dependent covariance defect

```text
D_e,x(K)=||(A_(d,x)U_e-U_eA_(c,x))K||_2.              (FPG2)
```

Choose a root context `r`, a spanning tree `T`, and orient its edges away
from `r`.  Define the rooted transport unitaries recursively by

```text
V_r=I,
V_d=U_e V_c                  if e:c->d lies in T.      (FPG3)
```

Pull every context PVM back to the root gauge:

```text
P-hat_(c,a)=V_c^*P_(c,a)V_c,
A-hat_(c,x)=V_c^*A_(c,x)V_c,
F-hat_c=V_c^*F_cV_c.                                  (FPG4)
```

These are honest PVMs and involutions on the whole matrix space; no common
corner or polar rounding is being assumed.

For every incidence `(c,x)`, choose an anchor context `a(x)` containing `x`
and a path transporter `W_(c,x)` made only from edges carrying `x`, from
`a(x)` to `c`.  Define its rooted holonomy

```text
H_(c,x)=V_c^* W_(c,x) V_(a(x)).                        (FPG5)
```

For the anchor, take `W=I`, so `H=I`.  Let `G` be one nonzero matrix and let
`B_x` be Bob involutions.  Set

```text
e_pred=sum_c ||F_cV_cG||_2^2,

e_anchor=sum_x ||A_(a(x),x)V_(a(x))G
                         -V_(a(x))G B_x||_2^2,

e_hol=sum_(c,x) ||(H_(c,x)-I)G||_2^2,                 (FPG6)
```

and let `e_edge` be the sum of the squared covariance defects in `(FPG2)`
along the selected variable paths, applied to the corresponding transported
copies of `G`.  All paths are fixed and finite.

## Rooted Gram decoder

There is a constant `K_Y`, depending only on the finite incidence graph and
question distribution, such that the game energy of
`one-gram-vector-decodes-a-finite-bcs-strategy` satisfies

```text
E_G(P-hat,B)
 <=K_Y(e_pred+e_anchor+e_edge+e_hol).                  (FPG7)
```

Indeed, forbidden-answer energy is exactly

```text
||F-hat_cG||_2=||F_cV_cG||_2.                          (FPG8)
```

Iterating `(FPG2)` along the fixed `x`-path gives

```text
||(A-hat_(c,x)H_(c,x)
       -H_(c,x)A-hat_(a(x),x))G||_2
 <= path covariance error.                            (FPG9)
```

Writing `A=A-hat_(a(x),x)`, `A'=A-hat_(c,x)`, `H=H_(c,x)`
and using the anchor row gives

```text
||A'G-GB_x||_2
 <=2||(H-I)G||_2
   +||(A'H-HA)G||_2
   +||AG-GB_x||_2.                                    (FPG10)
```

The last holonomy term is legitimate because
`||(H-I)GB_x||_2=||(H-I)G||_2`.  Squaring `(FPG10)`,
summing the finitely many incidences, and using `(FPG8)` proves `(FPG7)`.
Together with the finite game gap, this yields

```text
(1-omega^*(B))||G||_2^2
 <=K_Y(e_pred+e_anchor+e_edge+e_hol).                 (FPG11)
```

Thus products of context transports really can build the one Gram state,
but only after their state holonomies are charged.  No source projection is
needed.

## Specialization to the native Fanizza triangle and leaf

Use the context graph in
`fanizza-native-additive-incidence-is-one-triangle` and root at `C_D`.
Take the spanning tree

```text
C_D--C_X  labelled O_Q,
C_D--C_Z  labelled O_Q,
C_D--C_R  labelled O_P.                               (FPG12)
```

Anchor `O_Q,O_P` at `C_D`, anchor `Z_tilde` at `C_Z`, and anchor every
private variable at its unique context.  All tree holonomies are literally
the identity.  The only nontrivial term in `(FPG6)` is

```text
H_triangle
 =V_R^* U_(Z->R) V_Z,

e_triangle=||(H_triangle-I)G||_2^2.                   (FPG13)
```

Changing the spanning tree merely moves this one defect to another side of
the triangle.  The attached `C_X` leaf creates no holonomy.  Consequently
the whole state-dependent incidence problem is not a four-way common-corner
problem: after local predicate and anchor rows, it is one scalar cycle
moment.

Gauge doubling is compatible with this reduction.  It makes every logical
overlap invariant under the private selector resets, so the edge covariance
rows can be imposed without changing the Fanizza words.  It does **not** by
itself control `(FPG13)`, because it acts on the finite packet coordinate,
whereas the cycle also has a free multiplicity coordinate.

## Exact multiplicity-holonomy countermodel to the present bridges

Let an exact finite packet graph model have vertex representations `pi_c`
and exact edge intertwiners `u_e`.  Amplify every vertex by the same
nonzero finite multiplicity space `M`:

```text
pi_c'(g)=pi_c(g) tensor I_M,
u_e'=u_e tensor h_e,                                   (FPG14)
```

where the `h_e` are arbitrary unitaries on `M`.  Every amalgam/HNN edge
relation remains exact, since the edge groups act trivially on `M`.  Set
`h_e=I` on the tree and choose `h_(Z->R)=-I_M` on the chord.  On any flat
packet sector of the classically flat native triangle, the rooted holonomy
is

```text
H_triangle=I tensor (-I_M).                            (FPG15)
```

Therefore for every nonzero Gram matrix supported on that sector,

```text
||(H_triangle-I)G||_2^2=4||G||_2^2,                   (FPG16)
```

while every finite packet, edge, and gauge-bridge relator has zero defect.
This persists under arbitrary common amplification.  Finite gauge-orbit
covariantization changes only the packet factor and leaves `(FPG15)` free.

Hence the established two-sided gauge bridges and ordinary HNN incidence
cannot imply a bound

```text
||(H_triangle-I)G||_2^2<=K E_rel.                     (FPG17)
```

The missing relation must couple the **product around the triangle** to the
same Gram state.  Separate edge saturation, equal restriction
multiplicities, and exact logical covariance do not do so.

## The minimal literal repair is one triangular two-cell

With the orientations in `(FPG12)`, write the three edge words as

```text
U_DZ:C_D->C_Z,
U_DR:C_D->C_R,
U_ZR:C_Z->C_R.
```

Then `(FPG13)` is the evaluation of the literal group word

```text
h_triangle=U_DR^(-1) U_ZR U_DZ.                       (FPG17a)
```

Consequently the single two-cell relator

```text
U_ZR U_DZ=U_DR                                        (FPG17b)
```

kills the entire state-holonomy row, in every matrix model and for every
`G`.  This is the minimal group-word repair of the exact countermodel above:
it constrains the multiplicity product around the cycle rather than any one
finite edge restriction.

The relation passes the exact-witness audit **provided the full packet edge
intertwiner torsors close**.  In one common countably amplified perfect BCS
representation, if one can choose for every context a unitary packet
identification `V_c` from the same global source, set

```text
U_cd=V_d V_c^*.                                       (FPG17c)
```

Each `U_cd` has the required shared-logical covariance, and

```text
U_ZR U_DZ
 =V_R V_Z^* V_Z V_D^*
 =V_R V_D^*
 =U_DR.                                               (FPG17d)
```

Gauge-orbit covariantization supplies all private gauge types while fixing
the logical BCS words.  At the separator-sign level the native triangle is
classically flat, so this construction is compatible with the exact marked
model and does not force a forbidden Boolean assignment.

There is nevertheless a genuine developability audit for the **full**
private Weyl/gauge packet.  Countable amplification makes each edge
intertwiner space nonempty, but does not prove that the product of the
`D->Z` and `Z->R` intertwiner torsors meets the `D->R` torsor.  This exact
double-coset condition is isolated in
`fanizza-triangle-two-cell-has-an-intertwiner-torsor-obstruction`.  Until it
is checked, `(FPG17b)` is a candidate relation, not a proved exact HALT
extension.  That node also gives an explicit positive construction when the
three private gauge registers are incidence-private tensor factors: unused
register actions can absorb the third reset and make the cocycle flat.  What
remains in that audit is the simultaneous realization of this factorization
inside the full Schur/Pauli context packets.

This repair is not the completed backend.  It pays `e_hol`, but it does not
produce a nonzero `G`, make the selected packet predicates accept `V_cG`, or
prove the anchor covariance rows in `(FPG19)`.  Its value is that it removes
the global incidence coherence problem with one ordinary relator **once the
full-packet torsor condition is verified**, leaving the state-dependent
Gram-production/acceptance problem.

## Product-of-Hecke-compressions warning

Replacing `(FPG13)` by a bare product of selected Hecke compressions does
not avoid the issue.  Even with nonzero consecutive overlaps, a product can
vanish.  For example in `C^3`, with

```text
p_0=projection onto span(e_1),
p_1=projection onto span(e_1,e_2),
p_2=projection onto span(e_2),                         (FPG18)
```

both `p_1p_0` and `p_2p_1` are nonzero, but
`p_2p_1p_0=0`.  This is the finite-dimensional form of changing the Gram
state at every edge.  A useful product cell must prove state-dependent
saturation along the chosen chain and `(FPG13)` on its closing chord.

## Reduced construction target

The projection-free Fanizza backend may now target the finite row

```text
||G||_2^2>=gamma q-o(1),

sum_c||F_cV_cG||_2^2
+sum_x||A_(a(x),x)V_(a(x))G-V_(a(x))GB_x||_2^2
+e_edge
+||(V_R^*U_(Z->R)V_Z-I)G||_2^2
 <=K E_rel+o(1).                                      (FPG19)
```

By `(FPG11)`, `(FPG19)` pays the marked mass with the fixed finite game gap.
The final term is the sole new triangle datum.  It is strictly weaker than a
common reducing corner and strictly stronger than all currently established
edgewise gauge/HNN relations.

Alternatively, after the incidence gauges have been fixed, one may replace
the separate predicate and anchor rows in `(FPG19)` by the single cyclic
acceptance return of
`finite-game-gap-makes-the-cyclic-acceptance-compressor-strict`.  That
product is a strict contraction in finite matrices and has a fixed vector in
the exact perfect commuting model.  The remaining construction problem is
then one positive-norm Gram block and one finite Hecke return equation.
