---
rg: 2
id: jacobson-relative-hs-rigidity-firewall-proof
kind: route
title: Separate exact Kazhdan rigidity from normalized-HS head collapse
target: jacobson-property-t-and-finite-k-do-not-exactify-the-head
requires:
  - one-balanced-actor-qutrit-bridge-is-jacobson-core
  - binary-jacobson-core-is-weakly-sofic-with-fd-head-radical
  - binary-jacobson-steinberg-cover-is-elementary
---

## 1. Property (T) is present, but only for genuine representations

The ring

```text
J=F_2<S,T | TS=1>
```

is a finitely generated unital associative ring.  Ershov's theorem on
noncommutative universal lattices says that `EL_n(R)` has Kazhdan
property `(T)` whenever `n>=3` and `R` is a finitely generated
associative ring.  It applies here and gives

```text
G=EL_28(J) has property (T).                              (JRF3)
```

Primary source:

- https://arxiv.org/abs/0809.4095

It follows formally that `(G,L)` has relative property `(T)`: an
almost-invariant vector in a genuine unitary representation of `G`
has a `G)-invariant vector, hence an `L)-invariant vector.  This
implication adds no assertion about maps of the generators which only
approximately satisfy the relators.

The established Steinberg-cover calculation supplies a fixed finite
presentation of this elementary group.  Write it as

```text
G=<Sigma | R>
```

and choose a word in `F_Sigma` representing
`w=x_13(1-ST)`.  For a tuple `U=(U_s)_(s in Sigma)` of
`d)-dimensional unitaries, set

```text
Def_R(U)=max_(r in R) ||r(U)-I||_(2,d),
||A||_(2,d)^2=Tr(A^* A)/d,
kappa_w(delta)=sup{||w(U)-I||_(2,d): Def_R(U)<=delta},   (JRF4)
```

where the supremum includes every positive dimension.

## 2. The missing modulus is exactly ultraproduct head invisibility

We prove the equivalence claimed in the status statement:

```text
kappa_w(delta)->0 as delta->0
       iff
every homomorphism G->prod_omega U(d_n) kills w,          (JRF5)
```

where the target is a metric ultraproduct for normalized HS distance.

Suppose the left side fails.  There are `epsilon>0`, dimensions
`d_m), and tuples `U^(m)` such that

```text
Def_R(U^(m))->0,
||w(U^(m))-I||_(2,d_m)>=epsilon.
```

Sending each presentation generator to the class of its coordinate
sequence defines a homomorphism into any nonprincipal metric
ultraproduct.  All relators vanish there, while the displayed lower bound
makes the image of `w` nonidentity.

Conversely, choose unitary lifts of the finitely many generator images of
a homomorphism to a metric ultraproduct.  The defects of the finitely many
relators tend to zero along the ultrafilter.  If the image of `w` is
nonidentity, its distance from the identity is bounded below on an
ultrafilter-large set.  A diagonal choice of indices gives tuples with
relator defect tending to zero and `w)-defect bounded below.  Thus the
left side of `(JRF5)` fails.

This compactness argument is important logically.  Proving the
dimension-free limit in `(JRF5)` is already proving that the marked head
lies in the normalized-HS ultraproduct radical.  It is not an auxiliary
continuity lemma which property `(T)` supplies for free.

## 3. A rank-one relator error defeats the adjoint-representation route

A common proposed use of relative property `(T)` is to put the matrix
algebra in its normalized HS Hilbert space and let a unitary act by
conjugation.  The following exact calculation blocks that passage.

For `d>=2`, let

```text
V_d=diag(-1,1,...,1).
```

Then

```text
||V_d-I||_(2,d)=2/sqrt(d)->0.                            (JRF6)
```

On the normalized HS Hilbert space, take
`X_d=sqrt(d) E_12`, so `||X_d||_(2,d)=1`.  Conjugation gives

```text
Ad(V_d)X_d=-X_d,
||(Ad(V_d)-I)X_d||_(2,d)=2.
```

Since the difference of two unitaries has operator norm at most two,

```text
||Ad(V_d)-I||_(B(HS_d))=2 for every d.                  (JRF7)
```

Thus there is no dimension-free function `eta(t)->0` which bounds the
operator norm of `Ad(V)-I` by
`eta(||V-I||_(2,d))`.

Assigning matrices to presentation generators gives a genuine
representation of the free group on `Sigma` by adjoint operators, but it
does not give a representation of `G).  To descend through the relators
one would need those adjoint relators to be small in Hilbert-space operator
norm.  Equations `(JRF6)-(JRF7)` show that normalized HS relator control
does not provide this.  Applying a Kazhdan constant at that point therefore
assumes the missing stability step.

The root-system grading and relative-root estimates in the proof of
`(JRF3)` concern almost invariant vectors for exact representations.
They do not change this norm discontinuity.

## 4. The available stability theorems use different hypotheses

The Frobenius-stability theorem of de Chiffre, Glebsky, Lubotzky and Thom
is a theorem for finitely presented 2-Kazhdan groups and the unnormalized
Frobenius norm

```text
||A||_Frob=(Tr(A^* A))^(1/2).
```

Primary source:

- https://arxiv.org/abs/1711.10238

Ershov proves property `(T)), not the required 2-Kazhdan hypothesis.
There is also a dimension-dependent change of scale

```text
||A||_Frob=sqrt(d) ||A||_(2,d).                          (JRF8)
```

A normalized-HS defect tending to zero can therefore stay bounded away
from zero, or diverge, in Frobenius norm.  The matrices in `(JRF6)`
already have Frobenius distance exactly two from the identity.  Hence that
stability theorem cannot be rescaled into `(JRF5)`.

Uniform Ulam-stability results have another mismatch.  They begin with a
map defined on every group element and a global defect such as

```text
sup_(g,h in G) ||phi(gh)-phi(g)phi(h)||.
```

A presentation microstate controls only the fixed finite relator list.
Choosing word representatives for all elements gives no uniform bound:
errors accumulate with word length and van Kampen area.  Property
`(TTT)), where available, and uniform stability for higher-rank lattices
therefore do not turn a local presentation defect into `(JRF5)).

Primary sources:

- https://arxiv.org/abs/0911.3975
- https://arxiv.org/abs/1010.0565
- https://arxiv.org/abs/2301.00476

There is a stronger negative audit in the normalized metric.  Becker and
Lubotzky prove that an infinite hyperlinear property-`(T)` group is not
HS-stable.  Fournier-Facio, Gerasimova and Spaas prove the corresponding
failure even for local HS-stability; for finitely presented groups local
HS-stability and HS-stability coincide.  Thus local exactification is not
an automatic consequence of property `(T)).  Proving it for this
particular `G` would itself be a decisive new nonhyperlinearity argument,
not an input presently supplied by the literature.

Primary sources:

- https://arxiv.org/abs/1809.00632
- https://arxiv.org/abs/2307.13155

## 5. Every finite K-head window has an exact retaining model

Let `E` be any finite subset of the finitary kernel `L` and enlarge it
to its finite `K)-orbit

```text
E^K={k e k^(-1): k in K, e in E}.
```

The subgroup `N=<E^K>` is finite because `L` is locally finite.
It is normalized by `K`.  Consequently

```text
F=<K,E>=NK                                                (JRF9)
```

is a finite subgroup of `G`.

Let `lambda_F` be the complex left regular representation of `F).
For every `h!=1` in `F`,

```text
tr_F(lambda_F(h))=0.                                    (JRF10)
```

If `E` contains the head root `w`, then `w^2=1` in characteristic
two.  Left multiplication by `w` partitions `F` into two-cycles.
Hence the `+1` and `-1` eigenspaces of `lambda_F(w)` both have
dimension `|F|/2`.  The negative spectral cut has normalized rank
exactly one half.

The restriction of `lambda_F` to `K` is a direct sum of copies of the
regular representation of `K`.  In particular an order-three qutrit
element has its three complex spectral phases with equal multiplicity, and
all fixed qutrit group-algebra marginals have their canonical traces.
Nothing is merely approximate in this model.

This does not extend `lambda_F` to a representation of the full group
`G`: the balanced actor moves between larger head windows.  That is
exactly the point.  Any proposed contradiction which uses only exact
`K)-types and finitely many relations internal to a fixed head window is
false in the model `(JRF9)`.  A load-bearing argument must authenticate a
mixed actor occurrence across those windows.

## 6. Exact finite-dimensional annihilation has no uniform rate

Every exact finite-dimensional representation of `G` kills `L`, by
the established finite-dimensional head-radical theorem.  To deduce
`(JRF5)` from this fact one would need a uniform assertion that
small-defect tuples are close enough to exact representations, or at least
that the single word `w` is close to its exact value.  The latter assertion
is precisely `kappa_w(delta)->0`; restating exact annihilation does not
prove its uniformity in the dimension.

There is also a general counterexample to any implication using property
`(T)) alone.  Thom constructed a finitely generated LEF, hence sofic and
hyperlinear, Kazhdan group which is not residually finite.  Choose a
nonidentity element in its finite residual.  Every exact
finite-dimensional unitary representation kills that element: its image is
a finitely generated linear group and is residually finite, so a surviving
image would be separated by a finite quotient.  Yet a hyperlinear
embedding retains the element in a normalized-HS ultraproduct.

Primary source:

- https://arxiv.org/abs/0810.2180

Thom's group is not finitely presented (a finitely presented LEF group is
residually finite), so it does not decide the present finitely presented
case.  It does prove sharply that Kazhdan rigidity plus exact
finite-dimensional annihilation is not the missing theorem.

Finally, simplicity of `L` says that the nontrivial `w` normally
generates `L`.  Root commutator identities propagate exact annihilation
from `w` to the other finitary roots.  They cannot propagate relator
smallness backwards to `w`: such an estimate would express a nontrivial
element of `G` as a controlled consequence of its defining relators.
The finite models in Section 5 give a concrete firewall to that reversal.

Combining Sections 1-6 proves the stated boundary.  Property `(T)),
relative property `(T)), finite-`K) exactification, root grading,
finite-dimensional annihilation and the published stability results do not
establish `(JRF5)`.  The remaining route must introduce information absent
from every finite `K)-head window, namely a quantitatively calibrated
mixed `S/T)-bearing actor occurrence.
