# The coherent quotient is the faithful literal group

2026-09-08. The completed triangle identifies the entire Laurent
quotient, and the known kernel comparison then identifies the entire
coherent group with its literal bilateral action. In particular, the
single new relator normally generates the previous literal kernel.
This is an algebraic identification, not a proof of a positive matrix
gap. It sharpens that gap question to the MF status of one explicit
group.

Write

```text
Gamma=Theta_shift,             Gamma_triangle=Gamma/<<E>>_Gamma,
R=F_2[z,z^(-1)],               N=ker(pi).
```

The notation and earlier facts used below are proved in:

- [the full finitary-kernel calculation](jacobson-recursive-packets-generate-finitary-linear-kernel-2026-09-08.md);
- [the literal Laurent quotient and kernel comparison](jacobson-stable-letter-laurent-quotient-and-local-inner-action-2026-09-08.md);
- [the coherence word and its boundary factor](jacobson-missing-laurent-coherence-word-and-finite-cell-countermodel-2026-09-08.md);
- [the complete third packet and four-error criterion](jacobson-coherent-quotient-and-four-word-matrix-gap-2026-09-08.md);
- [the affine quotient separating the old word](jacobson-laurent-cover-has-a-noncentral-affine-quotient-2026-09-08.md).

All group homomorphisms below are algebraic homomorphisms, and
`[a,b]=a b a^(-1)b^(-1)`.

## 1. The three specified rank-one nodes

Recall the exact presentation

```text
Gamma/L=Lambda x Z,          L=GL_fin(F_2^(Z x {1,2,3})).
```

The two finite factors of `Lambda` are

```text
G_02=<c,k,q> ~= GL_3(F_2),
G_01=<c,k,h> ~= GL_3(F_2),
```

with their full common `K_P=<c,k> ~= GL_2(F_2)` identified.
In the first factor `c=x_13`, `k=x_31`, `q=w_23`; in the
second factor `c=x_13`, `k=x_31`, `h=w_12`, in that factor's
own finite coordinates. Set

```text
s=c k c,
r=[q k q,c],               u=[h c h,k],
v=h u h,                   d=h r h.
```

The remaining defining relations of `Lambda` are

```text
(h q)^3=1,                 [u,d]=r.
```

The image of the decorated word `E` is `(e,0)`, where

```text
e=(q v q)d.
```

Put `Lambda_triangle=Lambda/<<e>>_Lambda`. The completed
third-packet proof gives

```text
G_12=<h,u,q,r> ~= GL_3(F_2)
```

inside `Lambda_triangle`. Its six roots are

```text
X_12=v,       X_21=u,       X_23=r,
X_32=q r q,   X_13=d,       X_31=q u q.
```

The relevant rank-one subgroups, with their chosen positive and
negative roots, are therefore precisely

| Node | Weyl element | Positive root | Negative root |
| --- | --- | --- | --- |
| 0 | `s` | `k` | `c=s k s` |
| 1 | `h` | `v` | `u=h v h` |
| 2 | `q` | `r` | `q r q` |

Each node is `SL_2(F_2)=GL_2(F_2)`. Each pair of nodes
generates the indicated `G_ij=SL_3(F_2)=GL_3(F_2)` with
the usual two simple-root embeddings. For example, the positive
roots for `G_01` are `x_31,x_12`, and those for `G_02`
are `x_31,x_23`; either pair is a simple system of its finite
type-`A_2` root system. The third pair has positive roots
`v=X_12,r=X_23`.

These are fixed embeddings, not arbitrary abstract identifications
of three copies of `GL_3(F_2)`.

## 2. The universal colimit is exactly Lambda_triangle

Let `U` be the universal colimit of the three groups `G_01`,
`G_02`, `G_12`, identifying their prescribed rank-one nodes
from the table. Its diagram is the three-node affine diagram
`A_2 tilde`, with Cartan matrix

```text
 2 -1 -1
-1  2 -1
-1 -1  2.
```

There are homomorphisms in both directions

```text
U -> Lambda_triangle -> U.                              (1)
```

For the first map, the two old finite tables hold by construction,
and the entire third finite table was derived from the old mixed
relations and `e=1`. The common node maps agree literally on
their displayed generators. Thus the universal property defines
the first map in (1).

For the second map, the first two tables in `U` give the prescribed
amalgam defining `Lambda`, including the defining words for
`r,u,v,d`. In `G_12`, the standard finite table gives

```text
(h q)^3=1,       [u,h r h]=r,       q v q=h r h.
```

Hence the two old mixed relators and the new relator `e` hold
in `U`, defining the second map in (1). The two composites fix
`c,k,h,q`, which generate `Lambda_triangle`. They also fix
all three node groups, which generate `U`: the remaining node
generators `s,v,r` are the displayed words in `c,k,h,q`.
Both composites are identity. Consequently

```text
Lambda_triangle ~= U.                                  (2)
```

This argument proves equality with the colimit presentation; it
does not infer equality merely from the existence of the three
finite subgroups in a matrix image.

## 3. The affine presentation theorem and the exact Laurent map

Daniel Allcock's *Presentation of affine Kac-Moody groups over
rings*, Theorem 1 and Corollary 2, pp. 3--4, identifies the
rank-one/rank-two colimit with the corresponding simply connected
affine group for an irreducible affine diagram with at least three
nodes, over any commutative ring. Its group version applies here:
the diagram has three nodes, every edge has type `A_2`, and the
coefficient field is `F_2`. There is no excluded small-field case
in this theorem. [Primary paper](https://web.ma.utexas.edu/users/allcock/research/affkmg.pdf).

Thus (2) identifies `Lambda_triangle` with the simply connected
affine group of type `A_2 tilde` over `F_2`. We use the
group version of the theorem; no assertion about stable or
unstable algebraic `K_2` is needed.

To identify the particular map to Laurent matrices, the established
map `kappa:Lambda->SL_3(R)` sends the node roots to

```text
k -> x_31(1),        v -> x_12(z),        r -> x_23(1).
```

Conjugate these matrices by the invertible diagonal matrix

```text
P=diag(z^(-1),1,1) in GL_3(R).
```

They become

```text
x_31(z),            x_12(1),             x_23(1),       (3)
```

respectively. These are the standard three positive simple root
elements of the untwisted affine `A_2` loop realization. The
negative roots become `x_13(z^(-1)),x_21(1),x_32(1)`;
the Weyl elements are the corresponding root-pair Weyl words.
Thus this identifies the given node maps, including orientation,
with the standard affine-to-Laurent map. Conjugation by `P`
is an automorphism of `SL_3(R)`, even though `P` itself need
not have determinant one.

Capdeboscq--Kirkina--Rumynin, *Presentations of Affine Kac-Moody
groups*, Forum of Mathematics, Sigma 6 (2018), e21, p. 2 and
Section 6, p. 31, describes the simply connected affine
`A_(n-1) tilde(F_q)` group as a central extension of
`SL_n(F_q[z,z^(-1)])` with kernel `F_q^times`. At `q=2`
this kernel is trivial. [Primary published paper](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/8837F5546EA4ADFC1A9ECFBFF5194756/S2050509418000191a.pdf/presentations_of_affine_kacmoody_groups.pdf).

Combining this fact with the exact node matching (3), the map
induced by the original `kappa` is an isomorphism:

```text
bar(kappa):Lambda_triangle ~-> SL_3(R).
```

Equivalently, the entire old kernel is normally generated by the
one coherence word:

```text
ker(kappa)=<<e>>_Lambda.                               (4)
```

This does not make `e` trivial in the old group. The previously
constructed affine quotient still proves that the old kernel is
infinite and noncentral, and that `e!=1`. Equation (4) is a
statement about normal generation, not generation as an abstract
group.

## 4. Transfer of the full kernel to Gamma

Let `p:Gamma->Lambda x Z` be the quotient by `L`. The
earlier literal-kernel calculation gives

```text
p|N:N ~-> ker(kappa) x {0},
E in N,                  p(E)=(e,0).                  (5)
```

Put `M=<<E>>_Gamma`. Since `N` is normal and contains `E`,
we have `M<=N`. Since `p` is surjective, images of all
conjugates of `E` give all conjugates of `(e,0)`. Therefore

```text
p(M)=<<(e,0)>>_(Lambda x Z)
    =<<e>>_Lambda x {0}
    =ker(kappa) x {0}=p(N).                           (6)
```

The middle equality uses only that the displayed `Z` factor is
central. Injectivity of `p|N` in (5) now gives `M=N`.
Hence

```text
<<E>>_Gamma=ker(pi),
pi_triangle:Gamma_triangle ~-> pi(Gamma).              (7)
```

In particular `Gamma_triangle` is exactly the group of literal
bilateral operators generated by the authenticated packets and
the shift, with the finite presentation already given. Its normal
finitary subgroup remains faithful and its quotient is exactly

```text
Gamma_triangle/L ~= SL_3(R) x Z.                       (8)
```

No section or splitting of (8) is supplied by this calculation.

## 5. Every head-retaining homomorphism is faithful

The group `L` is simple, as proved using a fresh-coordinate
commutator in
[the amenable-target calculation](jacobson-recursive-head-dies-in-amenable-targets-2026-09-08.md).
Its centralizer inside the literal group is trivial. For
completeness, if an invertible `F_2`-linear operator `A` on
the finite-support space `V_Z` commutes with every finitary
transvection `I+E_ij`, then it commutes with every `E_ij`.
For `i!=j`, evaluating `A E_ij=E_ij A` on `e_j` gives

```text
A e_i=(coefficient of e_j in A e_j) e_i.
```

Varying `i,j` shows that every basis vector has the same scalar
eigenvalue. Invertibility makes this scalar nonzero, and over
`F_2` it equals one. Thus `A=I`. By (7),

```text
C_(Gamma_triangle)(L)={1}.                            (9)
```

Let `rho:Gamma_triangle->H` be any group homomorphism to
any group, and suppose it retains the head involution
`w=x_13,Q`. Simplicity of `L` implies

```text
ker(rho) intersect L={1},
```

since this intersection is normal in `L` and does not contain
`w`. Both `ker(rho)` and `L` are normal in `Gamma_triangle`,
so their commutators lie in the intersection. Therefore
`ker(rho)` centralizes `L`, and (9) proves

```text
rho(w)!=1  ==>  rho is injective.                     (10)
```

This is an exact statement about homomorphisms. It is not a
dimension-independent estimate on approximate representations.

## 6. The matrix question is exactly MF, and the radical dichotomy

Use the four-error infimum `gamma_triangle` and its identical
admissible finite-packet domain from
[the coherent matrix criterion](jacobson-coherent-quotient-and-four-word-matrix-gap-2026-09-08.md).
That criterion proves

```text
gamma_triangle=0
 iff some homomorphism Gamma_triangle->U(Q_d) retains w,
```

where

```text
Q_d=product_n M_(d_n)(C) / directSum_n M_(d_n)(C)
```

is the operator-norm corona. Combining it with (10) gives

```text
gamma_triangle=0  iff  Gamma_triangle is MF.            (11)
```

Here MF means that the group admits a faithful homomorphism into
such a norm corona. Thus a positive value is equivalent to
non-MF for this particular group. Neither possibility is decided
by the present proof.

There is also an exact description of the possible MF radical.
Define `Rad_MF(G)` as the intersection of the kernels of all
homomorphisms from `G` into all such norm-corona unitary groups.
First the quotient in (8) is residually finite, by the following
explicit specializations.

For a nonidentity `A in SL_3(R)`, choose a nonzero Laurent
entry of `A-I`. Multiplying by a power of `z` gives a nonzero
polynomial `f(z) in F_2[z]`. Choose a finite extension
`F_(2^a)` with `2^a-1>degree(f)`. A nonzero polynomial
has at most its degree many roots, so some nonzero element
`alpha in F_(2^a)` satisfies `f(alpha)!=0`. Evaluation
`z->alpha` defines a ring homomorphism on all of `R` and
sends `A` to a nonidentity element of the finite group
`SL_3(F_(2^a))`. A nonzero integer in the other factor of
(8) is separated by reduction modulo a positive integer not
dividing it. Thus finite quotients separate every nonidentity
element of `SL_3(R) x Z`.

These finite quotients give a faithful norm-corona map directly.
Enumerate the nonidentity elements of the countable quotient and
choose one finite quotient separating each. At stage `n`, take
the product of the first `n` finite quotients and its complex
left regular representation. Each fixed nonidentity element is
nonidentity at all sufficiently late stages. Its regular matrix
has distance at least `sqrt(2)` from identity, as witnessed by
the basis vector at the identity of that finite group. The
resulting norm-corona homomorphism is faithful. Pulling it back
through (8) gives

```text
Rad_MF(Gamma_triangle)<=L.                             (12)
```

If any norm-corona homomorphism retains `w`, (10) makes it
faithful and the radical is trivial. If none retains `w`, all
such maps kill its normal closure, which is `L`. Together
with (12), this proves the precise alternatives

```text
Rad_MF(Gamma_triangle) is either {1} or L,

Rad_MF(Gamma_triangle)={1}  iff gamma_triangle=0,
Rad_MF(Gamma_triangle)=L    iff gamma_triangle>0.        (13)
```

The normal closure of `w` remains `L` after passing from
`Gamma` to `Gamma_triangle`, because it was `L` before
the quotient and that subgroup embeds by (7).

## 7. Which representation transfers preserve the mark

The isomorphism (7) identifies representations of
`Gamma_triangle` and of the literal group, preserving `w`
exactly in every target, including a norm corona. This is a
valid transfer in both directions.

By contrast, pulling any representation of `SL_3(R) x Z`
back through (8) kills `L` and therefore kills `w`.
Residual finiteness of this quotient does not produce a marked
model of `Gamma_triangle`, and does not prove that the
extension (8) is MF.

A representation of the original `Gamma` descends to
`Gamma_triangle` exactly when it kills `E`. The new relator
is not automatic in the old presentation. The affine quotient
already gives old representations with `E` nontrivial. Thus
the four-error infimum is a question about the new quotient,
and the earlier inequality

```text
0<=gamma_shift<=gamma_triangle<=2
```

does not become an equality from the algebraic identification.
The remaining task is to decide (11), using the full decorated
finite-packet and shift relations of this faithful literal group.
