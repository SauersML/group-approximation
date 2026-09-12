# Realization across a closed compact stratum

Status: internally reviewed on 5 September 2026; no unresolved gap found.
This proves a mixed target-realization theorem using the previously
internally reviewed inputs listed below. It does not claim general
surjectivity for arbitrary mixed strata.

## 1. Statement and inputs

Let D be separable, simple, stably finite, pure, and real rank zero.
Let X be finite-dimensional compact metrizable, put B=D tensor K and
T=(D tensor Z) tensor K, and write phi for first-factor inclusion,
including its induced Cu maps. Let b in C(X,T)_+ be a contraction.

Suppose a closed subset Y of X satisfies:

1. The class [b|Y] is compact in Cu(C(Y,T)).
2. For every x outside Y, [b(x)] is soft or zero in Cu(T).

Then there is a positive a in C(X,B) with phi[a]=[b]. No extension of
the projection bundle on Y to the whole of X is assumed. The bundle
may be nontrivial, and the soft fiber classes outside Y may vary.
Zero fibers on Y are permitted.

The previously reviewed inputs are:

- Actual soft first-factor surjectivity for every separable pure
  algebra, in
  `stw99-lxxvi-soft-realification-surjectivity-audit-2026-09-05.md`.
- Actual projection-bundle first-factor isomorphism over every compact
  metric base, in
  `stw99-lxxvi-all-base-compact-k-stability-audit-2026-09-05.md`.
- Exact relative positive embedding with strict inequality away from
  the prescribed closed subset, in
  `stw99-lxxvi-rr0-cutoff-relative-selection-audit-2026-09-05.md`.
- The coefficient first-factor Cu isomorphism and the deduction that
  D tensor Z has real rank zero, as recorded in
  `stw99-lxxvi-rr0-finite-projection-patch-realization-2026-09-05.md`.
- The stable-finite compact-class support criterion, also used in
  `stw99-lxxvi-rr0-compact-summand-cancellation-2026-09-05.md`:
  a positive element with compact class has a projection support and
  a spectral gap at zero. Projection comparison with a positive
  element is implemented by an actual projection frame in its
  hereditary module.

The relative embedding theorem applies both to B and T. Its base is
finite-dimensional throughout this proof. No stable-rank-one claim
for C(X,D) or C(X,D tensor Z) is used.

## 2. The canonical soft part

Theorem A of Seth--Vilalta,
[*Continuous functions over a pure C*-algebra*](https://arxiv.org/html/2602.14809v1),
shows that C(X,D) is pure. The target is Z-stable and hence pure.

Write sigma(s)=1' s for multiplication by the soft one of Cu(Z).
For a pure Cu-semigroup, sigma(s) is soft, sigma(s)<=s, and
sigma(s)=s whenever s is soft. Moreover, this operation commutes with
Cu morphisms between pure semigroups, including evaluations and
restrictions. These facts follow from Proposition 7.3.16 and the
automatic linearity in Proposition 7.1.7 of Antoine--Perera--Thiel,
[*Tensor products and regularity properties of Cuntz semigroups*](https://arxiv.org/pdf/1410.0483).

Apply actual soft surjectivity to sigma([b]). Choose a positive
contraction c in C(X,B) such that

```text
phi[c] = sigma([b]).                                      (2.1)
```

For every x outside Y, evaluation gives

```text
[phi(c(x))] = [b(x)].                                    (2.2)
```

The classes [c(x)] are soft or zero everywhere. A nonzero soft class
in the stably finite simple coefficient cannot be compact: compactness
and softness would make its representing nonzero finite projection
properly infinite. Thus these nonzero classes are noncompact.

Notice that (2.1) alone does not realize b on Y. There it usually
produces only the soft predecessor of the projection class. The
construction below restores that compact part with its bundle data.

## 3. Extend the compact bundle to a neighborhood

Let q be the support projection of b|Y in C(Y,T). Projection-bundle
surjectivity gives a projection P_Y in C(Y,B) and a continuous partial
isometry w on Y with

```text
w*w=phi(P_Y),       ww*=q.                               (3.1)
```

Extend P_Y as a projection P on a neighborhood W of Y. This follows
by a selfadjoint Banach-valued extension and spectral cutoff on the
open set where its spectrum remains close to {0,1}. The same standard
extension is stated in Lemma 5.7 of Tikuisis,
[*The Cuntz semigroup of continuous functions into certain simple
C*-algebras*](https://arxiv.org/pdf/1007.2927).

After shrinking W, we have

```text
[phi(P(x))] <= [b(x)]              for x in W.             (3.2)
```

Here is the local verification; no semicontinuity of an arbitrary
projection-valued rank invariant is assumed. At y in Y with q(y)
nonzero, q(y)b(y)q(y) is invertible in q(y)Tq(y). For x near y the
same is true of q(y)b(x)q(y), and

```text
b(x)^(1/2) q(y) (q(y)b(x)q(y))^(-1/2)
```

is a frame from q(y) into the hereditary module of b(x). The
projection P(x) is unitarily equivalent to P(y) near y. Compose this
transport with w(y) and the displayed frame to obtain (3.2) locally.
When P(y)=0, P vanishes in a neighborhood of y, so (3.2) is automatic.
Compactness of Y gives a single neighborhood W with the assertion.

At any x in W minus Y where P(x) is nonzero, (2.2), (3.2), and the
coefficient Cu isomorphism give the strict inequality

```text
[P(x)] < [c(x)].                                         (3.3)
```

Strictness follows because the left class is compact and the right
class is soft and nonzero. This strict collar is the room used to
attach the bundle.

## 4. Actual frames on collars

If Y is empty, (2.2) holds everywhere. For every epsilon>0, the class
of (b(x)-epsilon)_+ is strictly smaller than [phi(c(x))] whenever
the cutoff is nonzero: it is way below the common noncompact fiber
class, and equality would make that class compact. Apply exact
strict relative embedding with empty boundary to obtain
[(b-epsilon)_+]<=[phi(c)]. Taking the supremum gives
[b]<=phi[c]=sigma([b])<=[b], proving realization in this case
without assuming that pointwise softness implies global softness.
If Y=X, the projection-bundle theorem proves the assertion directly.
Otherwise choose a closed neighborhood A of Y with A contained in W.
Choose nested closed neighborhoods K_n
of Y such that

```text
K_1 subset int(A),
Y subset int(K_(n+1)) subset K_(n+1) subset int(K_n),
intersection_n K_n = Y.
```

For each n choose another closed neighborhood L_n of Y with
L_n subset int(K_n), and set

```text
C_n = A minus int(L_n).
```

This is compact and disjoint from Y, and it contains A minus K_n.
By (3.3), exact strict projection-source selection supplies a
continuous v_C on C_n satisfying

```text
v_C*v_C=P|C_n,       v_C(x) in closure(c(x)B).              (4.1)
```

We next extend this frame over all of A, allowing its range to leave
Her(c) on the inner region. Choose a strictly positive contraction h
of B. The module H_h is B itself, and every projection P(x) has class
strictly below [h] when P(x) is nonzero. For example the standard
stable module contains two orthogonal copies of P(x); equality
[h]=[P(x)] would imply 2[P(x)]<=[P(x)], contrary to finiteness.

Apply the exact strict relative embedding theorem on A with source
P, constant target h, and prescribed frame (4.1) on C_n. We obtain
a continuous v_n on A such that

```text
v_n*v_n=P,
v_n|C_n=v_C,
v_n(x)v_n(x)* in Her(c(x)) whenever x in A minus K_n.      (4.2)
```

The last assertion uses the exact agreement on C_n. In particular,
the use of the large standard module is only an interior extension;
it does not assert that an arbitrary frame in c extends through Y.

## 5. Weighted positives with shrinking compact regions

Choose a continuous chi:X->[0,1] equal to one on a neighborhood of
K_1 and supported in int(A). For a compatible metric on X, set

```text
rho_n(x) = dist(x,K_n)/(1+dist(x,K_n)),
lambda_n = 1-chi+chi rho_n,       mu_n=1-lambda_n.
```

Then the zero set of lambda_n is exactly K_n, and lambda_n=1 off
the support of chi. The support of mu_n is a compact subset of
int(A).

Extend mu_n v_n v_n* by zero off A and define

```text
a_n = mu_n v_n v_n* + lambda_n c  in C(X,B)_+.             (5.1)
```

These are positive contractions. The scalar coefficients add to one,
and both positive summands before weighting are contractions. They
have the following exact properties:

```text
a_n|K_n = v_n v_n*|K_n,
[a_n(x)] = [c(x)]                  for x outside K_n.      (5.2)
```

To prove the second assertion, if mu_n(x)>0 then (4.2) puts the
projection v_n(x)v_n(x)* inside Her(c(x)), while lambda_n(x)>0.
Consequently a_n(x) and c(x) generate the same hereditary algebra.
If mu_n(x)=0, then a_n(x)=c(x). This retains the overlap as an
actual hereditary sum; no orthogonal direct-sum replacement occurs.

## 6. Three global comparisons

We repeatedly use this elementary observation. If [u]<=s and s is
noncompact, then

```text
[(u-epsilon)_+] << [u] <= s
```

implies [(u-epsilon)_+]<s whenever the cutoff is nonzero. Equality
would imply s<<s. Thus equal soft fibers become strict after taking
a positive cutoff of the source.

First, phi[a_n]<=[b] for every n. Fiberwise comparison follows from
(3.2) on K_n and (2.2), (5.2) outside K_n. On Y the support of
phi(a_n) is equivalent to q by (3.1). For 0<epsilon<1, the boundary
frame for (phi(a_n)-epsilon)_+ into H_(b|Y) is explicitly

```text
sqrt(1-epsilon) w phi(v_n|Y)*.
```

Its initial positive is (phi(a_n)|Y-epsilon)_+, and its range lies
in qT=H_(b|Y). Outside Y the target fiber is soft or zero. The
preceding observation therefore gives strict comparison for every
nonzero cutoff. Exact strict relative positive embedding, now with
coefficient T and boundary Y, proves

```text
[(phi(a_n)-epsilon)_+] <= [b].
```

Taking the supremum over cutoffs proves the first assertion.

Second, [a_n]<=[a_(n+1)] in the source. On K_(n+1) both positives are
projections equivalent to the same restriction of P. The boundary
frame for the epsilon cutoff of a_n is

```text
sqrt(1-epsilon) v_(n+1) v_n*  on K_(n+1).
```

Off K_(n+1), the target a_(n+1) has the soft or zero class [c(x)].
The source has class [P(x)] when x is in K_n, and [c(x)] otherwise.
These classes are at most [c(x)], by (3.3). Every nonzero cutoff is
strictly smaller than the target, by the same observation. Apply
exact strict relative embedding with coefficient B and closed
boundary K_(n+1), then take all cutoffs. This proves the claimed
increasing sequence. No compatibility of v_n and v_(n+1) away from
the boundary is required.

Let z=sup_n[a_n] in Cu(C(X,B)), and choose a positive contraction a
representing z. The first comparison gives

```text
phi[a] <= [b].                                          (6.1)
```

Restriction to Y preserves the increasing supremum, so
[a|Y]=[P_Y]. At every x outside Y, the point x is eventually outside
K_n. Therefore evaluations and (5.2) give

```text
[phi(a(x))]=[b(x)]          for x outside Y,
[phi(a)|Y]=[b|Y]=[q]       in Cu(C(Y,T)).                 (6.2)
```

Finally we prove [b]<=phi[a], rather than infer it merely from
fiberwise equality. Since [q]<=[phi(a)|Y], actual projection
comparison gives a continuous t on Y with t*t=q and
t in H_(phi(a)|Y). For each epsilon>0 the element

```text
t (b|Y-epsilon)_+^(1/2)
```

is an exact boundary frame for the cutoff of b into H_(phi(a)|Y).
Off Y the common fiber class in (6.2) is soft or zero, so every
nonzero cutoff of b is strictly smaller than the target class.
Exact strict relative embedding and then the supremum over cutoffs
give [b]<=phi[a]. Together with (6.1) this proves the theorem.

## 7. Scope of the advance

The result permits a compact projection bundle confined to a closed
set, attached to soft fibers on its complement. It uses increasing
source Cu classes with larger compact neighborhoods shrinking to
that set. The bundle need only extend to a neighborhood, and its
attachment to the global soft representative is made through actual
strict hereditary embeddings on closed collars.

The theorem does not cover an arbitrary target whose compact fiber
locus is nonclosed, nor a closed locus on which the restriction is
not a compact Cu class. A uniform spectral gap on Y, equivalently
compactness of the restriction here, is an actual hypothesis.
Finite-dimensionality of X enters the exact relative extension
input. No infinite-dimensional extension is asserted by an
unjustified finite-stage approximation of this stratification.

In particular the theorem advances mixed realization but does not
resolve STW LXXVI. Passing from this closed-stratum construction to
arbitrary accumulating compact strata is still necessary for full
surjectivity.
