# Thom's group reduces to a dominant-centralizer-orbit theorem

Date: 2026-08-12

## 1. Outcome

Let `R=Z[1/p]` and let `Ktilde=K_0(R)` be the de Cornulier--Thom
four-block group.  If `Z_0~=Z` is the integral subgroup of its top-right
central root group, put

```text
K=Ktilde/Z_0.                                           (TKD1)
```

The known theorems give:

* `K` is finitely presented and Kazhdan;
* `K` is hyperlinear;
* `K` is not residually finite; and
* the soficity of `K` remains open.

The last point is stated explicitly in Alekseev--Thom,
*Centralizers of sofic approximations of Kazhdan groups*,
[arXiv:2608.05362](https://arxiv.org/abs/2608.05362), Section 6.  Their
Theorem A is conditional on an ergodic-centralizer sofic embedding; it does
not construct one from an arbitrary sofic embedding.

The explicit Prüfer center and the non-Hopfian dilation do not close that
gap.  They reduce the desired contradiction to the following statement:

```text
K sofic
  ==> there is a sofic embedding whose lifted finite centralizers
      have one orbit of asymptotic density one.         (TKD2)
```

Equation `(TKD2)` is the `K`-specific dominant-orbit form of the
Hayes--Kunnawalkam Elayavalli ergodic-centralizer conjecture.  Proving it
would prove `K` nonsofic; it is not a routine finite-level matching lemma.

## 2. The central tower and the self-quotients

In the `(1,3,3,1)` block realization, the top-right root subgroup is

```text
Z(Ktilde)={u_14(z):z in R}~=R.                         (TKD3)
```

Only the inclusion needed below is used:

```text
Z(Ktilde)/Z_0~=Z[1/p]/Z~=C_(p^infinity) <= Z(K).       (TKD4)
```

Writing equality in `(TKD4)` would require the separate fact that the
central quotient creates no additional central elements.  None of the
arguments here needs that stronger assertion.

Conjugation by

```text
D=diag(p,I_3,I_3,1)                                   (TKD5)
```

defines an automorphism `delta` of `Ktilde` with

```text
delta(Z_0)=pZ_0 properSubset Z_0.                      (TKD6)
```

It therefore induces a surjective noninjective endomorphism

```text
alpha:K->K,
ker(alpha^m)=F_m=p^(-m)Z/Z~=C_(p^m),
K/F_m~=K.                                             (TKD7)
```

This is de Cornulier's non-Hopfian mechanism; see
[arXiv:math/0502140](https://arxiv.org/abs/math/0502140).

Every homomorphism from `K` to a finite group kills the subgroup in
`(TKD4)`.  Indeed, if the target has exponent `N` and `c in C_(p^infinity)`,
choose `d` with `N d=c`; then the image of `c` is the `N`th power of the
image of `d`, hence is trivial.  This proves non-residual-finiteness but not
nonsoficity.

## 3. Finite central quotients preserve a hypothetical sofic model

Assume that `K` has a sofic embedding and fix `m`.  Standard finite-group
permutation stability allows the representatives of `F_m` to be made into
an exact action after changing `o(|X_n|)` points.  It is free on
`(1-o(1))|X_n|` points.  Representatives of each fixed finite set in `K`
may likewise be modified on whole `F_m`-orbits so that they are exactly
`F_m`-equivariant on the good part.

Quotienting the good part by the free `F_m`-action gives finite sets

```text
Y_n=X_n/F_m.                                           (TKD8)
```

The induced permutations form a sofic approximation of `K/F_m`.  If
`g notin F_m` fixes an orbit downstairs, then upstairs

```text
sigma_n(g)x=sigma_n(f)x                               (TKD9)
```

for some `f in F_m`.  The union, over the finite set `F_m`, of the points
approximately fixed by `f^(-1)g!=1` has asymptotic density zero.  Thus
separation survives.

Consequently

```text
K sofic ==> K/F_m sofic.                              (TKD10)
```

Because `K/F_m~=K`, this operation reproduces another sofic approximation
of the same group.  It creates no contradiction.

## 4. What centralizer lifting actually supplies

Alekseev--Thom Theorem 3.1 says that, after an essentially equivalent
change of a sofic model of a Kazhdan group, its ultraproduct centralizer has
the form

```text
C(pi(K))=product_U A_n,
A_n<=Sym(X_n).                                         (TKD11)
```

If one can additionally realize `F_m` exactly inside the finite groups
`A_n`, freely on the good part, then every `A_n`-orbit there has size
divisible by `p^m`:

```text
p^m divides |A_n x|.                                  (TKD12)
```

There is a minor lifting subtlety which must not be hidden.  Theorem 3.1
places the finite subgroup in the **metric ultraproduct** of the `A_n`.
Finite permutation stability produces nearby exact permutations in
`Sym(X_n)`, but does not by itself say that the corrected permutations lie
inside the prescribed subgroup `A_n`, still less inside `Z(A_n)`.
Accordingly `(TKD12)` should either be proved by an additional internal
lifting lemma or granted as the strongest favorable finite-level scenario.
The no-go below holds even under that grant.

Define

```text
eta_n=max_(x in X_n) |A_n x|/|X_n|.                   (TKD13)
```

Equation `(TKD12)` says nothing about `eta_n`: the number of `A_n`-orbits
may tend to infinity.  The calibration

```text
X_n=(Z/p^(m_n)Z) times {1,...,b_n},
m_n->infinity, b_n->infinity,                         (TKD14)
```

already has a free coherent central tower while its central orbits have
density `1/b_n->0`.

Moreover quotienting by `F_m` preserves normalized orbit proportions:

```text
(|A_nx|/p^m)/(|X_n|/p^m)=|A_nx|/|X_n|.               (TKD15)
```

Thus neither increasing `m` nor using `K/F_m~=K` improves the statistic
which ergodicity needs.

## 5. The dilation is not a centralizer transformation

The endomorphism `alpha` cannot be implemented by conjugation in any
faithful permutation-ultraproduct embedding.  If a permutation `T`
satisfied

```text
T pi(g) T^(-1)=pi(alpha(g)),                           (TKD16)
```

then for `1!=c in ker(alpha)=C_p` one would have

```text
T pi(c) T^(-1)=1,                                    (TKD17)
```

contradicting injectivity of `pi`.  The inverse dilation does not descend
to `K`, because `delta^(-1)(Z_0)=p^(-1)Z_0` is not contained in `Z_0`.
Hence the non-Hopfian map supplies neither an injective compression nor an
additional centralizer transformation.

## 6. Exact missing theorem

Alekseev--Thom Lemma 2.8 proves that ergodicity of the rigid centralizer in
`(TKD11)` forces

```text
lim_U eta_n=1.                                        (TKD18)
```

Conversely, a conull finite-level orbit makes the ultraproduct action
ergodic.  Proposition 2.9 then yields

```text
(TKD18) ==> K is LEF.                                 (TKD19)
```

Since `K` is finitely presented, LEF implies residual finiteness, contrary
to `(TKD4)`.  Therefore `(TKD2)` would prove `K` nonsofic and, using Thom's
hyperlinearity theorem
[arXiv:0810.2180](https://arxiv.org/abs/0810.2180), would disprove
`hyperlinear ==> sofic`.

What the explicit group currently gives is only divisibility `(TKD12)`,
not dominance `(TKD18)`.  The missing input must control the multiplicity
spaces `X_n/F_m`.  Equivalently, it must match the cyclic-fiber quotient
models back to the original model in a way that merges their centralizer
orbits.  Property `(T)`, finite presentation, and the centralizer-lifting
theorem do not provide that matching.

Extreme-point selection does not repair the gap.  The relevant space of
sofic representations does not have the compact convex structure needed
for a direct Krein--Milman or Zorn argument; decreasing closed faces can
have empty intersection.  Thus the implication

```text
K sofic -> extreme/ergodic-centralizer model           (TKD20)
```

is precisely the open step, not a consequence of component selection.

## 7. Research consequence

The Prüfer tower and the dilation should now be treated as a completed
negative audit:

```text
central p-power fibers
  do not control the number of multiplicity fibers.    (TKD21)
```

A renewed attack on `K` must add a genuinely new theorem about those
multiplicity spaces--for example a `K`-specific permutation-stability,
cosystolic, or recurrence theorem strong enough to prove `(TKD18)`.  Merely
repeating finite central quotienting, expander component selection, or the
non-Hopfian self-map cannot advance the argument.
