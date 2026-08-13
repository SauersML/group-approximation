# An explicit finitely presented non-MF group

Date: 2026-08-12

## 1. Outcome

The general mechanism needs only a finitely presented group `G`, a finitely
generated property `(T)` subgroup `Gamma<G`, and an element `t in G` with

```text
t Gamma t^(-1)<Gamma.
```

Choose `a in Gamma-t Gamma t^(-1)`.  Adjoin an involution `c` centralizing
`Gamma`, put

```text
d=t c t^(-1),
w=[d,a d a^(-1)],
```

and impose that `w` is a central involution.  If the inclusion of `Gamma`
and the element `t` are given by finite words, the resulting group `E` is
finitely presented.  Then `w!=1`, but every norm-matrix-corona
representation kills `w`.

A uniform source of such pairs starts with a finitely presented property
`(T)` group `Gamma` having a proper injective endomorphism

```text
alpha:Gamma->Gamma.
```

Form the ascending HNN extension

```text
G=<Gamma,t | t gamma t^(-1)=alpha(gamma), gamma in Gamma>.
```

Choose `a in Gamma-alpha(Gamma)` and apply the general construction.  Then

```text
w!=1 in E,
```

but every homomorphism

```text
Theta:E->U(product_n M_(d_n)(C) / directSum_n M_(d_n)(C))
```

kills `w`.  Consequently `E` is not weak/operator-norm MF.

Taking

```text
Gamma=Z^3 semidirect SL_3(Z),
alpha(v,A)=(2v,A),
a=(e_1,I),
```

gives a completely explicit finitely presented example.  This is a
group-level non-MF theorem, not merely a proof that one chosen group
`C*`-algebra is non-MF.  It follows in particular that neither the full nor
the reduced group `C*`-algebra of `E` is MF.

This theorem does not decide whether `E` is hyperlinear, and it does not
complete the active hyperlinear-versus-sofic goal.

## 2. A finite presentation

For the ascending-HNN source, fix a finite presentation
`Gamma=<S | R>` and words `alpha(s)` in `S` for the endomorphism.  The group
`E` has the finite presentation

```text
< S,t,c |
    R,
    t s t^(-1)=alpha(s)                 (s in S),
    c^2=1,
    [c,s]=1                             (s in S),
    w^2=1,
    [w,s]=[w,t]=[w,c]=1                 (s in S)
>,
```

where

```text
w=[t c t^(-1), a t c t^(-1) a^(-1)].
```

Thus finite presentability follows directly from finite presentability of
`Gamma`; no finite presentation of an infinite lamp group is being used.

For the explicit choice, `Z^3 semidirect SL_3(Z)` is finitely presented and
has property `(T)`.  One standard proof of the latter combines relative
property `(T)` for

```text
(Z^3 semidirect SL_3(Z), Z^3)
```

with property `(T)` of `SL_3(Z)`.  The map `(v,A)|->(2v,A)` is an injective
endomorphism with image of index eight, and `(e_1,I)` is not in its image.

## 3. The marked involution is nontrivial

Let `X=G/Gamma`.  Define the Clifford lamp group `C(X)` by generators

```text
z, c_x  (x in X)
```

and relations

```text
z^2=c_x^2=1,
z central,
c_x c_y=z c_y c_x                    (x!=y).
```

The group is consistent, for example as the direct limit of its finite
Clifford subgroups, and `z!=1`.  The permutation action of `G` on `X`
acts on `C(X)`.  In `C(X) semidirect G`, send

```text
c |-> c_Gamma.
```

The root coset is fixed by `Gamma`, so the centralizer relations hold.  We
have

```text
d |-> c_(t Gamma),
a d a^(-1) |-> c_(a t Gamma).
```

The two cosets are distinct: equality would imply

```text
a in t Gamma t^(-1)=alpha(Gamma),
```

contrary to the choice of `a`.  Therefore

```text
w |-> [c_(t Gamma),c_(a t Gamma)]=z!=1.
```

The defining central-involution relations for `w` hold in this target, so
this is a homomorphism from `E`.  Hence `w!=1` in `E`.

## 4. The norm-matrix corona is stably finite

Put

```text
Q=product_n M_(d_n)(C) / directSum_n M_(d_n)(C).
```

The following proof avoids coordinate-rank shorthand.  If `v in M_k(Q)`
is an isometry, choose matrix lifts `v_n`.  Then

```text
||v_n^* v_n-I||_op->0.
```

For all sufficiently large `n`, `v_n^*v_n` is invertible and

```text
u_n=v_n(v_n^*v_n)^(-1/2)
```

is a square unitary matrix with `||u_n-v_n||_op->0`.  It follows that
`vv^*=1`.  The same argument works in every matrix amplification, so `Q`
is stably finite.  In particular, if projections `p,q in M_k(Q)` satisfy

```text
p<=q,  p Murray--von Neumann equivalent to q,
```

then `p=q`.

Corners obtained from lifted projections are again norm-matrix coronas and
are therefore stably finite as well.

## 5. Every norm-matrix representation kills `w`

Let `Theta:E->U(Q)` be a homomorphism.  Suppose `Theta(w)!=1`.  Since `w`
is a central involution of `E`,

```text
e=(1-Theta(w))/2
```

is a nonzero projection commuting with `Theta(E)`.  It need not be central
in all of `Q`; relative centrality is exactly what is required to cut the
representation.  Lift `e` to matrix projections, pass to a subsequence on
which they are nonzero, and restrict to the corresponding corner.  The
corner is another norm-matrix corona, its unit is `e`, and now

```text
Theta(w)=-1.                                           (NMF1)
```

Choose unitary lifts `U_(g,n)` of the corner images.  On

```text
K_n=L2(M_(r_n),tr_(r_n))
```

define

```text
beta_n(g)(x)=U_(g,n)xU_(g,n)^*.
```

Operator-norm multiplicative defect of the lifts gives operator-norm
multiplicative defect of the adjoint maps.  Hence they define a genuine
homomorphism

```text
beta:G->U(B),
B=product_n B(K_n)/directSum_n B(K_n).
```

The algebra `B` is another stably finite norm-matrix corona.

Let `p_Gamma in C*_max(Gamma)` be the Kazhdan projection and put

```text
P=beta|Gamma(p_Gamma).
```

In every Hilbert-space representation, `P` projects onto the
`Gamma`-fixed vectors, while `beta(t)Pbeta(t)^*` projects onto the
`alpha(Gamma)`-fixed vectors.  Since `alpha(Gamma)<Gamma`,

```text
P<=beta(t)Pbeta(t)^*.                                  (NMF2)
```

The two projections are unitarily equivalent.  Stable finiteness of `B`
upgrades `(NMF2)` to

```text
P=beta(t)Pbeta(t)^*.                                   (NMF3)
```

To make the vector argument completely literal, fix a free ultrafilter and
let `K_omega` be the Hilbert-space ultraproduct of the `K_n`.  The norm
corona `B` acts on `K_omega`, and `P` is the orthogonal projection onto the
`Gamma`-fixed vectors for this representation.

The vector represented by the unitary lifts of `Theta(c)` is
`Gamma`-fixed because `[c,Gamma]=1`.  Equation `(NMF3)` therefore says that
the vector represented by

```text
D_n=U_(t,n)U_(c,n)U_(t,n)^*
```

is also `Gamma`-fixed.  For the selected `a in Gamma`, put

```text
A_n=U_(a,n).
```

Then

```text
||D_n-A_nD_nA_n^*||_(2,omega)=0.                      (NMF4)
```

For unitaries `D,E`,

```text
||[D,E]-1||_2<=2||D-E||_2.
```

Taking `E=A_nD_nA_n^*`, equation `(NMF4)` makes the matrix word
representing `w` converge to `1` in normalized Hilbert--Schmidt norm.  On
the other hand `(NMF1)` says that the same word converges to `-1` in
operator norm.  Its normalized Hilbert--Schmidt distance from `1` therefore
converges to `2`, a contradiction.

Thus every such `Theta` satisfies

```text
Theta(w)=1.
```

Since `w!=1`, no norm-matrix-corona homomorphism of `E` is injective.  This
proves that `E` is not weak/operator-norm MF.

## 6. Scope and novelty audit

The proof uses the group notion of MF: embedding in the unitary group of a
norm quotient of matrix algebras.  This is the notion in Shulman's 2026
Definition 3.  It is weaker than requiring either full or reduced group
`C*`-algebra to be MF, so the obstruction applies to both stronger
properties as well.

The construction is distinct from the universal compression projection in
`C*_max(G)`.  That older observation only proves a `C*`-algebraic
non-finiteness statement and does not obstruct a group embedding.  The new
generator `c` and the nontrivial marked group word `w` convert the Kazhdan
projection obstruction into a group-level kernel theorem.

The theorem also explains why the same proof does not settle
hyperlinearity.  In an HS microstate the adjoint maps need not be
multiplicative in operator norm and do not define a representation in the
stably finite norm corona `B`.  In an exact tracial representation the
adjoint algebra acts on an infinite Hilbert space and its Kazhdan projection
may be infinite.  Hence non-MF does not imply nonhyperlinear here.

Before a public novelty claim, the result should receive specialist review
focused on:

1. the group-MF versus `C*`-MF terminology;
2. the Kazhdan projection order `(NMF2)` in an arbitrary target
   `C*`-algebra;
3. the passage from the norm corona to the Hilbert ultraproduct in
   `(NMF4)`;
4. prior appearances of this marked-commutator conversion of an infinite
   Kazhdan projection.

The internal audit above resolves the mathematical details of items 1--3.
The remaining uncertainty is principally literature priority, not an
identified gap in the proof.
