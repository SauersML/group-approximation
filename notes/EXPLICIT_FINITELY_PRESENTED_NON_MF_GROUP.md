# An explicit finitely presented non-MF group

Date: 2026-08-12

> **Historical design note.** This snapshot is retained only as research
> history.  Its formal-status sections are superseded by the repository
> README, `NON_MF_ADVERSARIAL_AUDIT_RESOLUTION_2026-08-13.md`, the generated
> numbered-claim manifest, and the current manuscript; they are not release
> evidence.

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

and impose that `w` is central.  Since `c^2=1`, both `d` and
`a d a^(-1)` are involutions.  Centrality of their commutator gives
`w=w^(-1)`, hence `w^2=1`.  If the inclusion of `Gamma` and the element `t`
are given by finite words, the resulting group `E` is finitely presented.
Then `w!=1`, but every norm-matrix-corona representation kills `w`.

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

The defining centrality relations for `w` hold in this target; the
involution relation is derived as above.  Thus this is a homomorphism from
`E`, and `w!=1` in `E`.

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

For completeness, the last implication is algebraic.  If
`v^*v=p`, `vv^*=q`, and `p<=q`, put

```text
s=v+(1-q).
```

The corner relations give

```text
s s^*=1,
s^*s=1-(q-p).
```

Direct finiteness forces `s^*s=1`, hence `q-p=0`.  Thus the proof is not
silently assuming cancellation in an abstract ordered `K_0` group.

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

### Formal endpoint at the time of this snapshot

`GroupApproximation/Sofic/NormMFResidualDetector.lean` defines
`NormMFInvisible x` by quantifying over the repository's actual
operator-norm matrix ultraproducts `UniversalWeakMF`.  It proves that these
elements form `normMFResidual G` and establishes the one-element criterion

```text
not_isWeakMF_of_normMFInvisible.
```

It also defines the exact word `markedCompressionWord t a c` and packages
the required output as `MarkedCompressionNormCertificate`; the theorem

```text
MarkedCompressionNormCertificate.not_isWeakMF
```

is the machine-checked final logical reduction from that certificate to
non-MF.

The mutable source-state inventory that originally followed this paragraph
has been removed.  The generated claim manifest and current manuscript are
the authoritative declaration map.

The analytic proof above was written for the sequential norm corona.  The
formal predicate `NormMFInvisible` instead quantifies over every operator-norm
matrix ultraproduct and every ultrafilter, including principal ultrafilters;
it is therefore not definitionally the paper's cofinite-corona radical.  The
proof works for those targets by taking limits, polar correction, and the
Hilbert-space ultraproduct along the same ultrafilter.  For countable groups,
`coronaMFResidual_eq_normMFResidual` proves equality with the unitary-sequence
cofinite-corona radical, while `isOperatorMF_iff_normMFResidual_eq_bot`
supplies the standard operator-MF bridge.

The fixed-rank marked-group consequence is formalized in
`Sofic/OperatorMFLocalNormalization`, `Sofic/MarkedMFClosed`, and
`Sofic/MarkedGroupWordBall`: the MF locus is closed, its complement is open,
and every non-MF marked group has a finite reduced-word-ball certificate.
This is recorded as a standard consequence, not a new priority claim:
[Dadarlat, Proposition 3.2 and Remark 3.3(i)](https://doi.org/10.1016/j.aim.2021.107722)
gives the local MF criterion and local-embedding permanence, while
[Fournier-Facio--Gerasimova--Spaas, Theorem 2.16](https://doi.org/10.1016/j.jalgebra.2024.08.042)
records that a marked limit locally embeds in its approximating groups.

## 7. Kun--Thom specialization: the same word is in the full sofic radical

Assume now that `Gamma<G` is one of the Kun--Thom pairs: `Gamma` and `G`
are Kazhdan, `G` is sofic (in the explicit constructions it is residually
finite), and `Gamma` is infranormal in `G`.  Their centralizer-normalization
theorem says that for every sofic representation `sigma` of `G`,

```text
C(sigma(Gamma)) is normalized by sigma(G).
```

For the group `E` above, let

```text
r:E->G
```

be the retraction which is the identity on `G` and sends `c` and `w` to
`1`.  Then

```text
w in Rad_sof(E).                                      (NMF5)
```

Indeed, let `psi:E->S` be any homomorphism to a sofic group.  The paired
map

```text
Psi=(r,psi):E->G times S
```

has sofic target and is injective on the distinguished copy of `G`.
Realize its restriction to `G` as a sofic representation.  Since `c`
centralizes `Gamma`, centralizer normalization says that

```text
d=t c t^(-1)
```

also centralizes `Gamma`.  In particular it commutes with the chosen
`a in Gamma-t Gamma t^(-1)`, and hence

```text
Psi(w)=Psi([d,a d a^(-1)])=1.
```

The second coordinate gives `psi(w)=1`.  Since `psi` was arbitrary,
`(NMF5)` follows.  Together with `w!=1`, this proves that `E` is nonsofic.

Thus any Kun--Thom pair for which the displayed construction is finitely
presented supplies a finitely presented group which is simultaneously
nonsofic and non-MF.  This still does not prove hyperlinearity.

## 8. Minimal Connes-embeddable character endpoint

The Kun--Thom specialization sharply reduces the active FALSE problem.  It
is enough to construct a Connes-embeddable finite tracial algebra `(M,tau)`,
a homomorphism

```text
pi:G->U(M),
```

and an involution

```text
C in pi(Gamma)'
```

such that, with

```text
D=pi(t) C pi(t)^*,
A=pi(a),
```

one has

```text
[D,A D A^*]=-1.                                      (NMF6)
```

Then the presentation gives a homomorphism `E->U(M)` sending `w` to
`-1`.  Its image is hyperlinear because `M` is Connes embeddable, and it
is nonsofic because every homomorphism from `E` to a sofic group kills
`w`.  Hence `(NMF6)` would disprove hyperlinear implies sofic.

This endpoint is strictly smaller than Connes embeddability of the full
Clifford crossed product.  That crossed product supplies one solution by
taking `C` to be the root Majorana, but `(NMF6)` asks for only one
anticommuting orbital edge, not a Clifford family indexed by all of
`G/Gamma`.  Equivalently, after conjugating by `pi(t)^*`, it asks for a
`Gamma`-central involution whose conjugate by the strict predecessor
`t^(-1) a t` is its Clifford partner.

The norm-corona theorem proves that no operator-norm MF construction can
realize `(NMF6)`.  A successful model must be genuinely tracial and must
allow the adjoint Kazhdan projection to be infinite.  This is a smaller
direct-HS target than the complete CAR action, but it retains the same
relative-commutant obstruction.

## 9. Orthogonal/CAR formulation and its exact scope

There is a useful functorial sufficient condition for `(NMF6)`.  Let

```text
rho:G->O(H_R)
```

be an orthogonal representation and let `xi` be a unit vector such that

```text
rho(gamma)xi=xi                 (gamma in Gamma),
<rho(t)xi,rho(a t)xi>=0.                            (NMF7)
```

Let `CAR(H_R)` denote the tracial real-Clifford/CAR algebra and write
`s(eta)` for the Majorana associated with a unit vector `eta`.  The
Bogoliubov action of `G` satisfies

```text
alpha_g(s(eta))=s(rho(g)eta).
```

In the crossed product

```text
N_rho=CAR(H_R) crossed_rho G,
```

put `C=s(xi)`.  The first part of `(NMF7)` gives `C in u(Gamma)'`, while

```text
D=u_t C u_t^*=s(rho(t)xi),
u_a D u_a^*=s(rho(a t)xi).
```

Orthogonal Majoranas anticommute.  Hence the second part of `(NMF7)` gives

```text
[D,u_a D u_a^*]=-1.                                  (NMF8)
```

Consequently:

```text
if N_rho is Connes embeddable, then hyperlinear does not imply sofic.
                                                               (NMF9)
```

The quasi-regular representation on `ell2_R(G/Gamma)`, with
`xi=delta_Gamma`, satisfies `(NMF7)`: the two vectors are the distinct
cosets `t Gamma` and `a t Gamma`.  Thus the complete Clifford crossed
product is one canonical instance of `(NMF9)`.  The value of `(NMF7)` is
that it permits a different orthogonal representation with the same one-edge
geometry; it does not require a labeled Majorana for every coset.

Two elementary no-go statements calibrate the remaining search.

1. `rho` cannot be finite dimensional.  Indeed

   ```text
   Fix_Gamma(rho) <= Fix_(t Gamma t^(-1))(rho)
                   =rho(t)Fix_Gamma(rho).
   ```

   The two extreme spaces have equal finite dimension, so equality holds.
   Hence `rho(t)xi` is `Gamma`-fixed and `rho(a t)xi=rho(t)xi`, contrary
   to `(NMF7)`.

2. `rho` cannot be weakly contained in the regular representation.  On
   restriction to `Gamma`, the regular representation of `G` is a multiple
   of `lambda_Gamma`.  The nonzero invariant vector `xi` would therefore
   make the trivial representation of `Gamma` weakly contained in
   `lambda_Gamma`, forcing `Gamma` to be amenable.  This contradicts the
   Kazhdan infinite subgroup used in the Kun--Thom construction.

Thus a successful CAR model is necessarily infinite dimensional and has a
singular, non-weakly-regular `Gamma`-sector.  Standard finite-dimensional
Bogoliubov models, profinite actions, and constructions controlling only
the regular/absolutely-continuous part of an orthogonal representation do
not reach `(NMF9)`.

Nor does the current halo/graph-wreath permanence theorem bypass this
issue.  Alekseev--Bradford require a sofic action on the underlying labeled
set or graph.  For the quasi-regular model this would recover a sofic model
of `G action G/Gamma`, whereas the Kun--Thom obstruction proves that this
action is not sofic.  The crossed-product CE assertion in `(NMF9)` is the
new content, not a consequence of existing action permanence.

## 10. Historical status snapshot (2026-08-13; superseded)

The mutable implementation roster has been removed from this historical
note.  Use the sources named in the banner for the current release status.
