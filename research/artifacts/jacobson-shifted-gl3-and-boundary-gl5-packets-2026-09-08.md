# Shifted finite packets and a boundary linearity cell

2026-09-08. This note makes two additional literal finite subgroups
explicit. It distinguishes relations imposed by a whole finite packet
from relations already deduced in `Gamma_2`. It establishes no matrix
gap or non-MF conclusion.

Use the notation of
[the universal pair analysis](jacobson-gamma2-universal-pair-structure-2026-09-08.md):
`F=G_Q x G_P`, `G=GL_3(F_2)`, `c=x_13,P`, `k=x_31,P`,
`r=x_23,P`, `s=h c h`, `u=[s,k]`, and `K_Q=GL(<e_1,e_3>)_Q`.
All statements involving natural matrices below are over `F_2`.
The resulting finite-group relations can subsequently be imposed on
complex unitary representations; the two representation categories
are not identified.

## 1. A whole shifted copy of GL_3(F_2)

In the literal Jacobson module, the basis is `e_(i,n)` with
`1<=i<=3`, `n>=0`. The head acts naturally at level zero; the tail
acts naturally at every positive level. The involution `h` exchanges
`e_(2,n)` with `e_(1,n+1)` and fixes `e_(1,0)` and every `e_(3,n)`.

For every `n>=1` put

```text
U_n=span{e_(1,n), e_(2,n-1), e_(3,n)},                 (1)
```

using the displayed order as coordinates. These spaces are disjoint
coordinate blocks, with only `e_(1,0),e_(3,0)` left over. On every
`U_n`, the three operators `c,k,h` are respectively

```text
x_13, x_31, w_12.                                    (2)
```

They fix the two leftover coordinates. The matrices in (2) generate
`G`: conjugation by `w_12` supplies roots `x_23,x_32`; their
commutators with `x_31,x_13` supply the other two roots. Consequently

```text
G_*:=<c,k,h> ~= GL_3(F_2).                            (3)
```

In this copy, `s=x_23,*`, `u=x_21,*`, and `v=u s` are the
three nonidentity elements of its row-two four-group. In particular
`u^2=1` is a literal finite-packet relation. The head subgroup `K_Q`
acts only on the two leftover coordinates, so it centralizes `G_*`.

The quartic relation alone is weaker data than (3). If it is added to
`Gamma_2`, then `(s k)^4=1`. The previously proved identity that
`(s k)^3` centralizes the head parabolic `P_Q` implies that `s k`
centralizes `P_Q`, since `s k=((s k)^3)^3`. As `k` already
centralizes the head, so does `s`. This argument does not establish
all the relations of the finite group (3).

### Consequences once the whole shifted packet is imposed

There is a stronger simplification than the quartic observation.
Assume the exact packets `F,G_*` with their stated common elements,
the commutation `[h,K_Q]=1`, and the TS relation `W=1`.
The relation `R=1` need not be assumed. Retain
`a_i,z_i,B_i` from the universal pair analysis. Conjugation by
`K_Q` gives all three equations

```text
[u,B_i]=z_i.                                         (3a)
```

Both `u` and `B_i` are now involutions. Because `z_i` is also
an involution, the dihedral calculation gives `[u,z_i]=1`.
Since `z_1 z_2 z_3=r` and `z_i z_j=a_k` for distinct indices,
`u` centralizes `r` and `A_Q`. Inside the shifted packet,

```text
c u c=u s=v,
```

while the original tail packet has `[c,r]=1`. Thus `v` also
centralizes `r`, and so does `s=u v`. This proves `R=1` from
the shifted packet and `W=1`. Neither braid was used.

For an exact unitary realization of the two packets and of
`[h,K_Q]=1`, put `eps_W=||W-I||`. The same dihedral argument
with an error gives `||[u,z_i]-I||<=2 eps_W`. Hence

```text
||[u,r]-I|| <= 6 eps_W,
||[v,r]-I|| <= 6 eps_W,
||R-I||=||[s,r]-I|| <= 12 eps_W.                     (3b)
```

These estimates use only exact finite-packet identities and the
triangle inequality. They apply to arbitrary complex unitary
representations of the packets.

The whole shifted row four-group `A_*={1,s,u,v}` centralizes
the head parabolic `P_Q=A_Q K_Q`. Indeed, `K_P=<c,k>` commutes
with the head and permutes the three nonidentity elements of `A_*`.
The centralization just proved for `u` therefore holds for all of
`A_*`. Also `A_*` centralizes the original tail row four-group
`A_P=<x_21,P,r>`: first all three elements centralize `r`, and
then conjugation by `K_P` gives the assertion for every element of
`A_P`. This gives an actual derived finite subgroup

```text
P_Q x D_tail,
D_tail=(A_P direct-sum A_*) semidirect K_P,
|D_tail|=96,             |P_Q x D_tail|=2304.         (3c)
```

Here `K_P` acts in the same way on the two row-covector modules.
The relations give a quotient of the finite group in (3c). The
literal model proves it embeds: `A_P` and `A_*` have independent
row coefficients `P` and `T`; after passing to Laurent symbols,
these become the independent monomials `1` and `t^(-1)`. The
nontrivial `K_P` component is distinguished by its `1,3` matrix
block. Thus no element of `D_tail` has trivial Laurent symbol
unless it is the identity. Every head element has trivial Laurent
symbol, so the direct product with the faithful `P_Q` is injective.

For every nonidentity `a in A_Q`, its stabilizer under conjugation by `G_*`
contains `A_* K_P`, a subgroup of index seven. The orbit of `a`
therefore has at most seven elements. In the literal model these
are the seven transvections with one common source and the seven
nonzero target vectors of `U_1`. Their Fano-plane addition
relations have not been derived from the orbit-size assertion.
The boundary packet below supplies those additional relations.

## 2. The finite group generated by the head and the shifted packet

The only block in (1) meeting the head is `U_1`, along the line
spanned by `e_(2,0)`. Define the five-dimensional boundary block

```text
V=span{e_(1,0),e_(2,0),e_(3,0),e_(1,1),e_(3,1)}.     (4)
```

The group generated by `G_Q` and `G_*` is exactly

```text
C=<G_Q,G_*> ~= GL_5(F_2) x GL_3(F_2).                (5)
```

Here the first factor acts on `V`, and the second acts identically
on all the blocks `U_n`, `n>=2`.

To verify surjectivity onto the first factor, take the normal closure
of `G_Q` in `<G_Q,G_*>`. It is supported on `V`. The shifted
permutation matrices move `e_(2,0)` to either of `e_(1,1),e_(3,1)`
while fixing `e_(1,0),e_(3,0)`. Conjugating the head transvections
therefore provides both directions of elementary transvections between
`e_(1,0)` and each other basis vector in (4). Commutators provide
all remaining off-diagonal transvections. These generate `GL_5(F_2)`.
An arbitrary shifted matrix can then have its `V` component cancelled
by this first factor, leaving its diagonal action on all `U_n`,
`n>=2`. The two coordinate supports are disjoint, which also proves
injectivity of the direct-product description.

There is a completely finite description of the embeddings in (5).
Give `V` the coordinate order in (4). Let

```text
eta:G -> GL_5(F_2)
```

act naturally on the ordered triple `(e_(1,1),e_(2,0),e_(3,1))`
and trivially on the other two coordinates. Then

```text
G_Q -> C:  g |-> (diag(g,I_2),1),
G_* -> C:  g |-> (eta(g),g).                           (6)
```

Write `K_P=GL(<e_1,e_3>)_P`. The precise intersection with the
original packet is

```text
F intersect C = L := G_Q x K_P.                       (7)
```

Indeed, a matrix acting in the shifted blocks and also in the original
positive-level blocks must preserve the second coordinate separately
from the first and third coordinates. Any mixing between them changes
the level in one of the two decompositions. Over `F_2` its action on
the second coordinate is then the identity, leaving exactly `K_P`.
The head factor is unrestricted. Under the descriptions `L=G x GL_2(F_2)`
and (5), its embedding is

```text
(g,k_0) |-> (diag(g,k_0), k_0),                       (8)
```

where the last `k_0` is embedded in coordinates `1,3` of `G`.

## 3. A boundary relation absent from the seven-ray model

Put `a=x_23,Q` and `D=h a h`. The finite packet `C` has the relation

```text
[u,D]=a,     equivalently [h u h,a]=h a h.             (9)
```

This is an elementary calculation entirely inside `GL_5(F_2)`.
On `V`, the operator `D` adds `e_(1,1)` to `e_(3,0)`, whereas
`u` adds `e_(2,0)` to `e_(1,1)`. Their commutator therefore adds
`e_(2,0)` to `e_(3,0)`, which is `a`. In the far-tail component
of (5), both `D` and `a` are the identity. The same relation holds
with any of the three nonidentity head row transvections in place of `a`, by
conjugation with `K_Q`.

The improved amenable seven-ray model already satisfies every relation
of `G_*`. To see this, partition its ray basis into the seven-element
blocks

```text
Y_n={A_(2,n-1)} union {X_n : X != A_2},   n>=1.        (10)
```

The remaining six boundary vectors are fixed by `c,k,H`. On (10),
these three operators are the seven-point permutation representations
of `x_13,x_31,w_12`. Thus `<c,k,H>` is again a faithful copy of
`G`, and in particular satisfies the quartic relation.

Nevertheless the seven-ray image violates (9). Its `D` adds
`A_(1,1)` to `A_(3,0)`, while `u` sends the label `A_1` to the
distinct label `B_3`. Consequently, with `E_(v;y)` denoting a
rank-one map on the ray basis,

```text
L_a := [u,D] a
    = I + E_(A_(1,1)+B_(3,1)+A_(2,0); A_(3,0)) != I. (11)
```

The vector in (11) is exactly the previous seven-ray TS defect vector.
Its three summands are independent ray basis vectors, even though the
labels satisfy `A_1+B_3+A_2=0` in `F_2^3`. This distinction is the
missing boundary linearity in that model.

### Reconstructing the boundary root module from one cell

In fact the whole group `C` is unnecessary for the following smaller
reconstruction. Assume the original and shifted packets, `W=1`,
and the single additional boundary relation (9). By (3c), the
stabilizer of `a` in `G_*` contains the point stabilizer
`P_*=A_* K_P`. For each nonzero vector `v in F_2^3`, define

```text
a_v=g a g^(-1) whenever g e_2=v.                      (11a)
```

This is well-defined: two choices differ on the right by `P_*`.
It satisfies `g a_v g^(-1)=a_(g v)`. The relation (9) is precisely

```text
a_(e_1+e_2) a_(e_1)=a_(e_2).                         (11b)
```

Every `a_v` is an involution. Equation (11b) makes the product of
`a_(e_1)` and `a_(e_2)` an involution, so these two commute.
The group `G` is transitive on ordered pairs of distinct nonzero
vectors. Conjugating (11b) therefore gives, for all such pairs,

```text
[a_v,a_w]=1,       a_(v+w)=a_v a_w.                   (11c)
```

With `a_0=1`, the map `v |-> a_v` is a homomorphism from the
additive group `F_2^3`. The literal representation makes it
injective in the abstract presentation. Thus this one cell supplies
the entire natural three-dimensional elementary abelian root group,
not merely a restriction on its conjugacy-orbit size.

Conjugation by `K_Q` supplies (9) for all three nonidentity
elements of `A_Q`. Write their reconstructed families as
`a_(1,v),a_(2,v),a_(3,v)`, with

```text
a_(3,v)=a_(1,v) a_(2,v).                              (11d)
```

Each family separately satisfies (11c). Comparing (11d) at `v+w`
with its values at `v,w` yields

```text
(a_(1,v) a_(1,w))(a_(2,v) a_(2,w))
    =(a_(1,v) a_(2,v))(a_(1,w) a_(2,w)).
```

Cancel the leftmost `a_(1,v)` and rightmost `a_(2,w)` to get
`[a_(1,w),a_(2,v)]=1`. For `v=w` this commutation already follows
from the original head four-group. Hence all six root coordinates
commute, and their group is the additive matrix space
`Hom(F_2^2,F_2^3)`. Its injectivity again follows from the literal
boundary action. Together with `K_Q` and `G_*` this gives the
derived finite subgroup

```text
Hom(F_2^2,F_2^3) semidirect (GL_2(F_2) x GL_3(F_2)),
of order 2^6 * 6 * 168 = 64512.                       (11e)
```

The two linear factors act on the source and target coordinates,
respectively. In the literal model their intersection with the root
group is trivial: the shifted factor is detected on the far tail,
and the head `GL_2` is detected on the two source coordinates.
This establishes (11e) from one boundary cell, without assuming all
of `C`. It remains a finite-group reconstruction. In a complex
unitary representation its abelian normal subgroup is represented
by its characters; no three-dimensional complex defining module is
being asserted.

For clarity, that finite character decomposition is also explicit.
The dual of the normal subgroup in (11e) is the matrix space
`Mat_(2 x 3)(F_2)`, using the pairing `(-1)^(trace(lambda X))`.
Its orbits under the two linear factors have matrix ranks zero, one,
and two, and sizes `1,21,42`. There are `3*7=21` rank-one
matrices; the remaining `64-1-21=42` have rank two. In any complex
unitary representation of (11e), let `m_1,m_2` be the common
dimensions of the character spaces in the two nonzero orbits, and
let `d_0` be the dimension of the zero-character space. Then

```text
d=d_0+21 m_1+42 m_2,
rank_-(a)=8 m_1+24 m_2.                              (11f)
```

To count the second formula, view `a` as a matrix with one fixed
nonzero target vector and one fixed nonzero source covector.
For a rank-one dual matrix `lambda=alpha f`, four of the seven
nonzero `f` evaluate to one on that target, and two of the three
nonzero `alpha` evaluate to one on the source covector. This gives
eight characters. For rank-two `lambda`, there are twelve maps
taking the target to each specified nonzero vector of `F_2^2`:
the kernel can be any of the six lines different from the target
line, and there are two quotient isomorphisms with the specified
image. Two of the three nonzero images pair to one with the source
covector, giving twenty-four characters. These multiplicity formulas
are feasible; they do not force the head action to vanish.

There is also an intrinsic finite-group comparison. In the seven-ray
model, the group `<G_Q,G_*>` is

```text
GL_9(F_2) x GL_3(F_2),                               (12)
```

with the first factor supported on `Y_1` together with
`A_(1,0),A_(3,0)`. The proof is the same transvection argument as
for (5), because `G` permutes the seven elements of `Y_1` transitively.
The far-tail factor acts by its seven-point permutation representation
on every `Y_n`, `n>=2`. Thus the head--shifted interaction is different
even though both individual finite `GL_3` packets are faithful.

The quantitative exclusion is model-specific. Inside the seven-ray
group,

```text
[x_12,Q,L_a]=x_13,Q=w.                               (13)
```

Indeed, `x_12,Q` fixes the source coordinate in (11) and changes its
target vector by `A_(1,0)`. Hence every unitary representation of
this particular group satisfies

```text
||rho(w)-I|| <= 2 ||rho(L_a)-I||.                     (14)
```

This excludes head-retaining seven-ray representations satisfying (9).
Equation (13) is not asserted in an arbitrary group with the two
finite packets: in the literal Jacobson image, `L_a=1` and `w!=1`.

## 4. A precise stronger finite presentation, and its remaining gap

The common subgroup (7)--(8) gives an unambiguous finite-packet
amalgam `F *_L C`. Both finite factors survive in a finite quotient
of this amalgam: choose a finite set on which both act by sufficiently
many copies of their regular actions. Their restrictions to `L` are
then isomorphic free `L`-sets, so relabel one action to make those
restrictions agree. The two faithful actions define the required
homomorphism to a finite symmetric group. Thus the finite packets
by themselves cannot supply a marked obstruction.

One can impose the remaining mixed cells to obtain the explicit
candidate

```text
Theta = < F,C | the two copies of L agree,
                 (h b)^3=1, W=1 >.                   (15)
```

where `h=(eta(w_12),w_12)` is already in `C`, and `b,R,W` have
their previous definitions. Every factor can be specified by its
finite multiplication table. The relations `h^2=1`, `[h,K_Q]=1`,
and `(h d_P)^3=1` already hold in `C`. Hence (15) is a quotient
of `Gamma_2` with additional finite boundary-packet relations.
The literal representation proves its head mark remains nontrivial.
The relator `R` has been omitted because of (3a)--(3b).

Neither the full packet `C` nor its boundary relation (9) has been
derived here from `Gamma_2` plus the shifted packet alone. They are
honest additional relations in (15). Conversely, the finite symmetric
quotient for `F *_L C` was not shown to satisfy the mixed cells in
(15). It is not a countermodel to this stronger candidate.

The unresolved issue is simultaneous finite-dimensional coherence
with these mixed cells. The faithful regular trace of the literal
group still gives consistent positive trace data on every finite
packet above. Its restriction to `C` is the regular character of
`C`, not its five-dimensional defining representation over `F_2`.
Thus one may not impose the defining representation's dimension or
coordinate addition on arbitrary complex unitary representations of
the finite packet. Any operator-norm obstruction must address those
arbitrary representation types explicitly.
