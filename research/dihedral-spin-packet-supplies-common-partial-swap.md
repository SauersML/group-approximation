---
rg: 2
id: dihedral-spin-packet-supplies-common-partial-swap
kind: claim
title: One dihedral spin packet supplies the common partial-swap source for every Gram row
distinct_from:
  partial-isometry-swap-wordizes-one-bcs-gram-row: that starts from the literal reflection attached to a partial isometry; this constructs the partial isometry and a sufficient common reflection from two ordinary involutions and one central commutator mark.
  controlled-swap-wordizes-matrix-corner-without-adjoint-dilution: that treats a controlled copy swap whose support projection has already been named; this recovers the support as the odd dihedral spin sector and never names its projection by a group word.
  finite-selector-gadget-induction-barrier: that rules out nonlinear pruning of a commuting selector cube by a finite packet; this packet does not prune selectors and uses the noncommuting dihedral pair only to authenticate one common Gram source.
  finite-role-packet-cannot-supply-hybrid-predicate-row: that proves the hybrid row isolated here cannot be universally oriented by any ordinary word of a finite role packet, even when the common swap cancels every external multiplicity commutator.
  shared-multiplicity-commutator-builds-selected-hybrid-row: that constructs the row on one selected hyperoctahedral type by leaving one common multiplicity commutator on both roles and cancelling it only in the final commutator with the common swap.
  perfect-tracial-bcs-has-one-common-module-swap: that constructs the exact full standard-form swap in the perfect infinite model; this authenticates a positive-density partial swap in every finite marked packet and proves the dimension-free row estimate.
---

Let

```text
D_8=<z,j,y | z^2=j^2=y^2=1, y central, zj=yjz>.       (DSP1)
```

Thus `y=[z,j]=zjzj`.  The unique irreducible on which `y=-1` is the
two-dimensional Pauli representation.  The other irreducibles are the four
characters on which `y=1`.

This smallest nonabelian packet already authenticates the common nonlinear
source needed by the partial-isometry Gram-row construction.  It does not
encode a Boolean predicate and therefore does not run into the commuting
selector induction barrier.

## Exact partial-swap extraction

Let `Z,J,Y` be an exact unitary representation of `(DSP1)` on a finite
Hilbert space `H`.  Split

```text
H=H_+ directSum H_-                                  (DSP2)
```

according to the two eigenspaces of `Z`, and write

```text
J=[[a,S],[S^*,d]].                                    (DSP3)
```

Put `P_spin=(I-Y)/2`.  Since `Y` is central, `H_spin=P_spin H` is reducing.
On `H_spin`, `(DSP1)` says

```text
ZJ=-JZ.                                               (DSP4)
```

Consequently `J` exchanges the two `Z`-eigenspaces of `H_spin` unitarily.
On `(I-P_spin)H`, `Z` and `J` commute, so `J` is block diagonal.  It follows
that the off-diagonal block in `(DSP3)` is a partial isometry with

```text
SS^*=P_spin|_(H_+),
S^*S=P_spin|_(H_-).                                   (DSP5)
```

In particular the same literal group generator `j` supplies one and the
same partial isometry `S` in every later commutator row.

The diagonal complement of `J` need not have the particular signs used in
the displayed Julia reflection of
`partial-isometry-swap-wordizes-one-bcs-gram-row`.  Those signs are not
needed for soundness.  If `D=diag(A,B)` is any block-diagonal self-adjoint
unitary, then

```text
[D,J]_add=[[[A,a]_add, AS-SB],
           [-(AS-SB)^*, [B,d]_add]].                  (DSP6)
```

Hence the two off-diagonal blocks give the dimension-free lower bound

```text
2 Tr((AS-SB)^*(AS-SB))/dim(H)
 <= ||[D,J]_add||_(2,H)^2.                            (DSP7)
```

Let `D_0=max(dim(H_+),dim(H_-))`.  Pad the smaller space by a zero source and
arbitrary involutions, so that `S,A,B` are regarded as `D_0 by D_0`
matrices.  Since

```text
1/2 <=D_0/dim(H)<=1,                                  (DSP8)
```

`(DSP7)` implies

```text
||AS-SB||_(2,D_0)^2<=||[D,J]_add||_(2,H)^2.           (DSP9)
```

Thus every ordinary commutator relator `[d,j]=1`, with `[d,z]=1`, pays the
entire corresponding Gram-row energy: for involutions, the multiplicative
word `djdj-I` has exactly the same `2`-norm as `[D,J]_add`.  No formula for the diagonal
complement of `J` is required.

## Mark mass is source mass

Write

```text
q=tau_H(P_spin).
```

If the two spin halves have common dimension `r`, then

```text
q=2r/dim(H),
||S||_(2,D_0)^2=r/D_0>=r/dim(H)=q/2.                 (DSP10)
```

Equivalently,

```text
||S||_(2,D_0)^2>=1/8 ||Y-I||_(2,H)^2.                (DSP11)
```

This is exactly the common-source estimate: a separated central commutator
mark forces a positive Gram source at fixed normalized-Hilbert--Schmidt
scale.  In the canonical trace of a group in which `y` is nonidentity,
`tau(Y)->0`, hence `q->1/2` after exactification and `(DSP10)` gives a
uniform source floor.

## Exact completeness by polar support

The dihedral packet does not demand that a perfect game state be maximally
entangled.  Suppose an exact perfect model supplies a nonzero Gram operator
`G` with

```text
A_r G=G B_r,
F_c G=0                                                (DSP12)
```

for all consistency and predicate rows.  Let

```text
G=S|G|                                                 (DSP13)

```

be its polar decomposition.  From the first identity in `(DSP12)`,
`G^*G` and hence `|G|` commute with every `B_r`.  On the support of `|G|`,

```text
A_r S=SB_r.                                           (DSP14)
```

The second identity in `(DSP12)` gives `F_cS=0` on the same support.  Define

```text
J_S=[[I-SS^*, S],
     [S^*, -(I-S^*S)]],
Z=diag(I,-I).                                         (DSP15)
```

Then `Z,J_S,[Z,J_S]` satisfy `(DSP1)`, and every desired row commutator is
exact.  Since `G` is nonzero, so is the spin support; therefore `y` is
nonidentity in this representation.  The exact-witness firewall is
preserved.

The same proof works in a tracial von Neumann algebra: polar decomposition
is internal, and the support equations follow by spectral approximation on
the support of `|G|`.

## Robust finite-packet form

The packet is fixed and finite.  Gowers--Hatami exactification, followed by
block compression against the exact involution `Z`, gives a computable
dimension-independent modulus with the following consequence.  From an
approximate table for `(DSP1)` and approximate relators

```text
d_r^2=1, [d_r,z]=1,                                   (DSP16)
```

one obtains exact block involutions

```text
D_r=diag(A_r,B_r)
```

and one common partial isometry `S` such that, for a fixed finite row list,

```text
||A_rS-SB_r||_2^2
 <= ||d_r j d_r j-1||_2^2+o(1),                      (DSP17)

||S||_2^2>=1/2 tau((I-Y)/2)-o(1).                    (DSP18)
```

Here the harmless normalization/padding convention is the one in
`(DSP8)--(DSP10)`, and `o(1)` depends only on the fixed packet and row list,
not on matrix dimension.  One may equivalently exactify the complete
eight-element multiplication table before extracting the blocks.

## Consequence for the common-swap route

The nonlinear common-swap part of
`common-partial-isometry-swap-game-compiler` is therefore not open.  The
literal Julia signs in its old clause `(CPS3)` were stronger than the game
gap uses.  The sufficient ordinary-group syntax is just

```text
D_8(z,j,y),
[d_r,z]=1,
[d_r,j]=1                                             (DSP19)
```

for every already-compiled hybrid row involution `d_r`.

What remains is a different packet problem: manufacture the **hybrid row
involutions** whose two `Z`-blocks are the required context and global
variable/predicate reflections, coherently across all rows.  A finite
packet may not impose the predicate relations on both blocks, and separate
row packets may not change which multiplicity representation appears in a
shared block.  The dihedral construction solves common source alignment; it
does not solve that row-role coherence.

## Audit of literal shared variable words

There is a useful further separation.  Giving one literal involution `d_x`
to every global BCS variable and imposing

```text
[d_x,z]=1                                              (DSP20)
```

does produce

```text
d_x=diag(A_x,B_x)                                      (DSP21)
```

with the same negative-block observable `B_x` in every row.  Imposing
`[d_x,d_x']=1` only when `x,x'` share a context does **not** force variables
from unrelated contexts to commute.  The same context commutation is legal
on both blocks of the exact tracial BCS model.  Thus common Bob naming is
not, by itself, the remaining obstruction.

The obstruction appears at a nonlinear predicate.  From the commuting
positive-block involutions one can form the rejection projection `F_c` in
the matrix algebra, but the required row reflection is

```text
E_c=diag(I-2F_c,I).                                    (DSP22)
```

An ordinary word in the global `d_x` evaluates the same Boolean word on
both blocks; it gives

```text
diag(I-2F_c(A), I-2F_c(B)),                            (DSP23)
```

not `(DSP22)`.  A new controller must therefore implement the role-labelled
truth table

```text
z=+1 : e=1-2f_c(a),
z=-1 : e=+1.                                          (DSP24)
```

This is where controller orientation returns.

There is an exact finite-packet firewall.  Let `K` be any finite packet in
which the central mark `y`, the role bit `z`, the context selectors, and the
candidate controller `e` generate an abelian subgroup `A`.  If the packet
tries to enforce `(DSP24)` merely by retaining the central marked sector
`y=-1`, then every character of `A` compatible with `y=-1` occurs in some
`y=-1` representation of `K`, by induction from `A` to `K`.  In particular
the wrongly oriented characters excluded by `(DSP24)` still occur.  A
hyperoctahedral selected irreducible can realize `(DSP24)` locally, but the
central marked regular sector also contains the other selected types unless
one proves an additional type/source-saturation theorem.

Therefore the exact division of labor is

```text
D_8 spin packet       -> common partial-isometry source, solved;
literal d_x words     -> common variable naming, compatible;
nonlinear E_c row     -> oriented selected-type/Hecke return, open. (DSP25)
```

This also explains why tensoring the dihedral packet with the existing
hyperoctahedral predicate packet is not automatically enough.  Tensoring
leaves arbitrary external multiplicity actions on the selected predicate
type, while the row controller must act with the fixed orientation
`(DSP24)` on the very same partial source.

## Attempts and firewalls

- **Require the exact diagonal signs in `(DSP15)` in every representation.**
  The other two even dihedral characters change those signs.  They are
  irrelevant to `(DSP6)--(DSP11)`, so excluding them would add a needless
  nonlinear selector problem.
- **Use only commuting involutions.**  Then the off-diagonal block is zero.
  The central commutator `y=[z,j]` is precisely the nonabelian bit which
  measures the paired source.
- **Select one hyperoctahedral predicate type first.**  That can encode a
  local truth table, but it does not align the external multiplicity across
  rows or orient `(DSP24)` on the marked source.  The dihedral spin packet is
  orthogonal to that job and may be tensored/amalgamated with any successful
  row packet only after that selected-type return is supplied.
- **Give each row its own dihedral pair.**  This recreates the direct-sum
  Gram escape.  The generator `j` in `(DSP19)` must be literally common.
- **Claim the full game compiler is finished.**  It is not.  Ordinary words
  still have to name each hybrid block involution without imposing the
  Alice-context relations on the Bob block or losing the common Bob action.
- **Cancel the external multiplicity commutator with role-covariant gates.**
  This is useful on a selected type but cannot make the row universal on the
  whole marked D8 spin.  The finite regular-sector calculation in
  `finite-role-packet-cannot-supply-hybrid-predicate-row` forces any such
  universally scalar ordinary word back into the abelian role-selector
  subgroup, where its phase is affine (and a nontrivial upper-only phase is
  impossible even for an affine predicate).
- **Keep one common multiplicity commutator on both roles.**  This is the
  valid projective loophole.  The final commutator with `j` cancels the common
  factor exactly.  `shared-multiplicity-commutator-builds-selected-hybrid-row`
  gives an explicit doubled signed-permutation commutator for every truth
  table on one selected type.  The remaining issue is promoting that selected
  type to a common carrier across the BCS contexts, not orienting its row.
