# Universal coupled-pair consequences of the Jacobson TS cell

2026-09-08. These identities hold in the strengthened presentation
`Gamma_2`, and the norm estimates hold for arbitrary exact finite-packet
matrices with the specified relator errors. They do not assume that a
representation factors through the seven-ray quotient. No non-MF
conclusion is established here.

## 1. The three coupled pairs

Retain the presentation and notation from
[the TS-cell artifact](jacobson-ts-cell-after-seven-ray-countermodel-2026-09-08.md).
For clarity use

```text
c=x_13,P,       r=x_23,P,       k=x_31,P,
a_1=x_21,Q,    a_2=x_23,Q,     a_3=a_1 a_2,
A_Q=<a_1,a_2>,                 A_P=<x_21,P,r>,
s=h c h,       u=[s,k]=s k s k,
v=u s=s k s k s,
z_i=a_i r,     B_i=h z_i h       (i=1,2,3).             (1)
```

The subscripts `Q,P` mean the two factors of
`F=GL_3(F_2)_Q x GL_3(F_2)_P`. Both `A_Q` and `A_P` are four-groups.
The head subgroup `K=GL(<e_1,e_3>)_Q` normalizes `A_Q` and permutes
its three nonidentity elements transitively.

The head factor of the original constant `x_31(1)` drops from `u`:
it belongs to `K`, and `s` commutes with `K`. Thus the `k` in (1)
is only the tail root, with no change to the TS word.

Each of `h,c,r,k,s,v,z_i,B_i` is an involution. In particular

```text
v=(s k) s (s k)^(-1),                                  (2)
```

so this assertion about `v` needs no TS relation. The following
commutations also precede the TS relation:

```text
[s,K]=[u,K]=[v,K]=1,
[z_i,z_j]=[B_i,B_j]=1,
[s,B_i]=1.                                             (3)
```

For the last equality, `c` commutes with every `z_i`: the head factor
commutes with the tail, while `x_13,P` commutes with `x_23,P`.
Conjugate this equality by `h`.

The TS relation is `[u,B_2]=z_2`. Conjugating by `K`, which
centralizes `u` and `h`, gives all three equations

```text
u B_i u^(-1)=z_i B_i.                                  (4)
```

Since `s` commutes with every `B_i`, replacing `u` by `v=u s`
leaves the commutator unchanged:

```text
[v,B_i]=z_i.                                          (5)
```

## 2. Finite dihedral pairs and new centralizers

For two involutions `v,B`, their commutator is `(vB)^2`. If that
commutator is itself an involution, it commutes with both `v` and `B`:
conjugation by either reflection replaces `(vB)^2` by its inverse.
Applying this observation to (5) gives

```text
[v,z_i]=[B_i,z_i]=1.                                  (6)
```

Thus each pair `<v,B_i>` is a quotient of the dihedral group of order
eight, with central involution `z_i`. In the abstract `Gamma_2`, the
literal Jacobson image makes `z_i` nonidentity, so these subgroups are
indeed dihedral groups of order eight. A particular representation may
kill some of their elements.

The common `v` is essential for the next step. Products of two distinct
`z_i` are the third nontrivial head element:

```text
z_i z_j=a_k       when {i,j,k}={1,2,3}.
```

Consequently (6) implies

```text
[v,A_Q]=[v,r]=1.
```

Together with (3), this says that `v` centralizes the whole head
parabolic

```text
P_Q=<K,A_Q> ~= (C_2 x C_2) semidirect GL_2(F_2) ~= S_4. (7)
```

The additional relator `R=1` says `[s,r]=1`. Since `u=v s`, we
obtain `[u,r]=1`. Also `s u=k s k`, so `[k s k,r]=1`, or
equivalently `[s,k r k]=1`. The exact tail-packet identity is

```text
k r k=x_21,P r.
```

Cancelling the commuting factor `r` therefore gives

```text
[s,x_21,P]=1,
[s,A_P]=1.                                             (8)
```

The tail element `k` normalizes `A_P`. Hence `k s k` centralizes
`A_P` as well, and so do `u=s(k s k)` and `v=u s`. In summary,

```text
s,u centralize K x A_P,
v centralizes P_Q x A_P.                               (9)
```

No claim that `u` is an involution is needed or made. One exact
consequence illustrating the distinction is

```text
(s k)^3=v k centralizes P_Q.                           (10)
```

The fact that the cube centralizes `P_Q` does not, by itself, say
that `s k` centralizes it. A cube can identify three different unitary
spectral values. Thus (10) is not a license to assert `[s,P_Q]=1`.

## 3. Uniform propagation of matrix errors

Let `pi:F->U(d)` be any exact unitary representation and let `H` be
an exact self-adjoint unitary commuting with `pi(K)`. Define all words
in (1) from these matrices, and write

```text
eps_R=||[s,r]-I||,
eps_W=||[u,B_2] z_2-I||.
```

All statements in (2)--(3) are then exact, even if neither added
relator holds. The three `K`-conjugate TS defects have the same norm:

```text
||[v,B_i]-z_i||=||[u,B_i]-z_i||=eps_W.                 (11)
```

For the commutator `C_i=[v,B_i]`, conjugation by `v` replaces
`C_i` by `C_i^(-1)`. Since `z_i=z_i^(-1)`, (11) and the
triangle inequality imply

```text
||[v,z_i]-I|| <= 2 eps_W.
```

The same argument with `B_i` gives
`||[B_i,z_i]-I||<=2 eps_W`. Alternatively, `z_i B_i` is within
`eps_W` of the involution `u B_i u^(-1)`, so
`||(z_i B_i)^2-I||<=2 eps_W`.

For unitaries, commutator error with a product is at most the sum of
the errors with its factors. Apply this to `a_k=z_i z_j` and
`r=a_i z_i`. Then

```text
||[v,a_i]-I|| <= 4 eps_W,
||[v,r]-I|| <= 6 eps_W.                               (12)
```

Every element of `P_Q` is `a g` with `a in A_Q`, `g in K`.
Thus its commutator with `v` has norm at most `4 eps_W`.
Using `u=v s` and `k s k=s u` gives successively

```text
||[u,r]-I|| <= 6 eps_W+eps_R,
||[k s k,r]-I|| <= 6 eps_W+2 eps_R.
```

Conjugate the last inequality by `k`, then use
`x_21,P=(k r k)r`. The result is the fixed numerical estimate

```text
||[s,x_21,P]-I|| <= 6 eps_W+3 eps_R.                   (13)
```

These constants do not depend on `d`. This is propagation of explicit
word errors; no almost-invariant-vector-to-invariant-vector principle
enters the proof.

## 4. Exact finite-dimensional rank constraints

In an exact finite-dimensional representation of `Gamma_2`, equations
(4) and `B_i=h z_i h` make `z_i`, `B_i`, and `z_i B_i` conjugate.
Because `z_i` and `B_i` commute, let `n_i(e,f)` be their joint
eigenspace dimension for signs `e,f in {+1,-1}`. Equality of the
three negative ranks gives

```text
n_i(-,+)=n_i(+,-)=n_i(-,-)=rank_-(z_i)/2.               (14)
```

The remaining joint sector has dimension
`d-3 rank_-(z_i)/2`. In particular `rank_-(z_i)` is even.

The two braid relations make `h` conjugate to both `b` and `d_P`.
Inside `F`, `z_i` is conjugate to `b`, while `c` and `r` are
conjugate to `d_P`. Therefore all of

```text
rank_-(z_i), rank_-(B_i), rank_-(v), rank_-(c), rank_-(r)
```

are equal. Denote their common value by `m`. On the dihedral group
`<v,B_i>`, the two-dimensional irreducible consequently has
multiplicity `m/2`. If the four linear characters have multiplicities
`l_(++),l_(+-),l_(-+),l_(--)`, indexed by their values at `v,B_i`,
then

```text
l_(+-)=l_(-+),
l_(+-)+l_(--)=m/2.                                    (15)
```

These conditions allow nonzero multiplicities; they are not a vanishing
argument.

There is also a relative finite-type identity. By (2),

```text
v=J c J^(-1),       J=(s k)h.
```

Every factor in `J` centralizes `K`. Thus `J` identifies the negative
spaces of `c` and `v` as `K`-representations, not merely as vector
spaces. The negative space of `v` is a `P_Q x A_P`-module by (9),
whereas that of `c` is a `G_Q`-module. Their restrictions to `K`
must agree. This is an additional branching constraint with the same
common operator `v` throughout.

## 5. Cross commutators and a finite model with nonzero cross terms

For `i!=j`, conjugation by `u` preserves the commutation of
`B_i,B_j`. By (4),

```text
(z_i B_i)(z_j B_j)=(z_j B_j)(z_i B_i).
```

Multiply on the left by `z_j z_i` and on the right by `B_i B_j`,
using the commutations already proved. The resulting equality is

```text
z_j B_i z_j B_i=z_i B_j z_i B_j.
```

Therefore the cross commutators satisfy

```text
C_ij:=[z_i,B_j]=[z_j,B_i].                            (16)
```

The pair of generators `{z_i,B_j}` commutes elementwise with the pair
`{z_j,B_i}`. Both expressions in (16) thus show that `C_ij`
centralizes all four generators. Conjugation of `[z_i,B_j]` by
the involution `z_i` inverts it. Centrality then implies

```text
C_ij^2=1.                                             (17)
```

This does not prove `C_ij=1`. The following finite example shows that
nonzero cross terms are compatible with the common involution `v`,
the common conjugator `h`, the simultaneous `K`-action, and all three
coupled-pair equations.

Let `M` be the three-by-three matrix over `F_2` with zero diagonal
and ones off the diagonal. On the set

```text
P={(a,b,e): a,b in F_2^3, e in F_2}
```

define multiplication by

```text
(a,b,e)(a',b',e')=(a+a',b+b',e+e'+b^T M a').           (18)
```

The bilinear central term verifies associativity directly. This is a
group of order `128`. Put

```text
x_i=(e_i,0,0),       y_i=(0,e_i,0),       zeta=(0,0,1).
```

The `x_i` commute with one another, as do the `y_i`; they are all
involutions. Directly from (18),

```text
[x_i,y_i]=1,       [x_i,y_j]=zeta!=1 when i!=j.         (19)
```

Define `Q(b)=sum_(i<j)b_i b_j`. Its polarization is
`Q(b+b')+Q(b)+Q(b')=b^T M b'`. The following maps are automorphisms
of `P`:

```text
h(a,b,e)=(b,a,e+a^T M b),
v(a,b,e)=(a+b,b,e+Q(b)).                               (20)
```

For `v`, the polarization identity checks multiplication; for `h`,
symmetry of `M` does so. Both maps square to the identity. Simultaneous
permutation of the three coordinates of `a,b` gives an action of
`K=S_3`, commuting with both maps in (20). In the finite semidirect
product `P semidirect <h,v,K>`, the displayed automorphisms satisfy

```text
h x_i h=y_i,
v y_i v=x_i y_i,
[v,x_i]=1.                                            (21)
```

The formulas also give `(hv)^3=1`; their linear parts on `(a,b)`
show that `hv` has order three. Thus `<h,v>` has order six and
commutes with `K`. The displayed semidirect product has order at most
`128*36=4608`.
To put this in the notation of the coupled pairs, set

```text
p=x_1 x_2 x_3,       q_i=x_i p,
z_i=x_i=q_i p,       B_i=y_i.
```

The `q_i` are precisely the three nonidentity elements of a
four-group, and `K` permutes them transitively. Equations (19)--(21)
give all three coupled-pair equations, both commuting families, the
diagonal commutations, the common `h,v`, and the simultaneous `K`
action. Every cross commutator in (19) is nevertheless nontrivial.
The finite group's regular complex unitary representation realizes
these statements by actual finite matrices.

This example concerns the derived coupled-pair system only. It does
not supply the full packet `G_Q x G_P`, the definitions
`s=h c h`, `u=[s,k]`, `v=u s`, or both original braids. It is
therefore not a finite model of `Gamma_2`. It does rule out deleting
the cross terms using the coupled-pair equations and common conjugators
alone.

## 6. What the rank ledger can and cannot prove

These fixed-word trace and branching identities have a positive tracial
model. The literal Jacobson homomorphism proves the head mark nontrivial
in `Gamma_2`; therefore the left regular representation of `Gamma_2`
has its faithful group von Neumann trace `tau` and

```text
tau(P_-(w))=1/2.
```

Each embedded finite subgroup has its regular trace. In particular the
four joint spectral projections of `z_i,B_i` have trace `1/4`, and
the finite-packet and relative branching constraints have the regular
positive profile. Equations (14)--(15) are satisfied by the regular
dihedral profile: `d=8`, `m=4`, two copies of the degree-two
irreducible and one copy of each linear character. This last example
checks the dihedral marginal, not the entire `Gamma_2` presentation.

For any finite collection of these finite-subgroup trace coordinates,
the regular values are rational. A common denominator gives integer
marginal multiplicities satisfying their rank and restriction equations.
This does not construct a single finite-dimensional representation
realizing all the operators and relations simultaneously.

Consequently a contradiction from these trace and branching equations
alone is unavailable. The unresolved issue is coherence of the common
operators in finite matrices, or a selection operation whose validity
specifically uses finite dimension. A faithful finite von Neumann trace
is not a norm-matrix-corona embedding, so this observation establishes
neither MF nor non-MF for `Gamma_2`.
