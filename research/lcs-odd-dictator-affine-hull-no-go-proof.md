---
rg: 2
id: lcs-odd-dictator-affine-hull-no-go-proof
kind: route
title: Compute the exact scalar closure forced by perfect parity completeness
target: lcs-parity-gadgets-preserve-odd-dictator-affine-hull
requires:
  - perfect-correlated-masks-have-undamped-conditioned-spectrum
---

## 1. Scalar LCS solutions are affine

Write a sign assignment as `z_v=(-1)^{x_v}`, with
`x_v in F_2`.  A binary LCS equation

```text
product_(v in E) z_v=(-1)^b                            (ODP1)
```

is exactly the affine equation

```text
sum_(v in E) x_v=b mod 2.                               (ODP2)
```

Repeated occurrences are counted modulo two.  A finite LCS on the variables
`Q union A` therefore has scalar solution set

```text
Sol={x in F_2^{Q union A}: Lx=b}.                       (ODP3)
```

The commutation relations attached to an LCS equation impose no additional
condition on scalar signs.

Let `x^(1),...,x^(2k+1)` belong to `Sol`.  Then

```text
L(sum_i x^(i))=sum_i Lx^(i)=(2k+1)b=b mod 2.            (ODP4)
```

Returning to multiplicative notation, the coordinatewise product of any odd
number of scalar solutions is again a scalar solution.

For each `phi in S`, choose one extension
`e_phi=(d_phi,a_phi)` supplied by `(ODA1)`.  Applying `(ODP4)` to
`{e_phi:phi in beta}` proves `(ODA2)`.  Projection to the `Q`
coordinates commutes with coordinatewise products, so

```text
Aff(D) subseteq pr_Q(Sol).                              (ODP5)
```

Here the affine hull over `F_2` is precisely the set of odd products of
elements of `D`; repetitions may be cancelled.

This also proves the probabilistic version.  A perfect scalar strategy has
average loss zero.  Every individual test loss is nonnegative, so every
positive-weight equation is satisfied.  The preceding closure can then be
applied simultaneously to that finite support.  Reweighting the support
does not affect the conclusion.

## 2. The lower bound is exact

Fix `d_0 in D` in additive notation and put

```text
H=span{d+d_0:d in D}.
Aff(D)=d_0+H.                                           (ODP6)
```

Let `H^perp` be the annihilator in the dual of `F_2^Q`.  Then

```text
x in Aff(D)
iff ell(x)=ell(d_0) for every ell in H^perp.             (ODP7)
```

Choose a finite basis of `H^perp`.  Each equality in `(ODP7)` is a
parity equation on the variables in `Q`.  Their common scalar solution set
is exactly `Aff(D)`.  Thus `(ODP5)` is the strongest possible universal
conclusion: auxiliary parity variables cannot make the projected scalar
solution set smaller than the affine hull, and parity equations can attain
that hull exactly.

In particular, parity tests distinguish all nondictators while accepting
all dictators exactly if and only if the dictator set `D` is already an
affine coset.

## 3. The full folded long code has the maximal odd hull

Let `m=|S|`, let `F_S={f:S->{+1,-1}}`, and choose an arbitrary section

```text
sigma:F_S/{+1,-1}->F_S,
sigma([f]) in {f,-f}.                                   (ODP8)
```

For `phi in S`, define
`d_phi([f])=sigma([f])(phi)`.  Suppose two odd subsets
`beta,gamma subseteq S` give the same product assignment.  Their symmetric
difference `Delta=beta triangle gamma` has even cardinality, and equality
would imply

```text
product_(phi in Delta) sigma([f])(phi)=1
for every [f].                                          (ODP9)
```

Because `|Delta|` is even, replacing `sigma([f])` by either representative
`f` or `-f` does not change the product in `(ODP9)`.  If `Delta` were
nonempty, choose `f` which is `-1` at exactly one point of `Delta` and
`+1` at the other points of `Delta`.  The product would be `-1`, a
contradiction.  Hence `Delta` is empty.

All `2^{m-1}` odd subsets consequently give distinct assignments.  They
are odd products of the `m` dictators, so they lie in `Aff(D)`.  An
affine hull of `m` points has at most `2^{m-1}` elements.  Therefore

```text
Aff(D)={d_beta: beta subseteq S, |beta| odd},
|Aff(D)|=2^{m-1}.                                      (ODP10)
```

For `m=1` or `m=2`, the only odd subsets are singletons.  For `m>=3`,
a three-element subset gives a nondictator in the hull.  This proves the
sharp threshold.

Changing the section in `(ODP8)` multiplies every `d_phi` by the same
coordinate sign vector.  An odd product is multiplied by that vector once,
so the entire affine hull is merely translated.  Its size and the
dictator/nondictator obstruction are invariant.  Quotienting away more query
coordinates can only identify an odd product with an honest assignment; it
does not give a parity equation which rejects that product.

## 4. Boundary of the no-go

In the zero-noise Taller--Vidick context, the raw characters are exactly

```text
chi_beta(f)=product_(phi in beta) f(phi),               (ODP11)
```

and folding retains the odd `beta`.  The paper's Fourier expansion and
folding identities (arXiv:2507.22444v2, Definitions 2.1--2.2) are therefore
the concrete instance of `(ODP10)`.  If a mask law is perfectly complete
on `S`, every supported mask equals one on `S`; the associated parity
equations accept every `d_phi`, so `(ODP5)` recovers all undamped odd
characters without using independence or any Fourier estimate.

The theorem is deliberately local and scalar.  A nonclassical source may
have contextwise spectral atoms which do not extend to global classical
assignments.  New cross-context relations could exploit that failure of
global extendability, and genuinely non-affine predicates can have a
perfectly complete dictator test.  But neither mechanism is a
support/folding-only change to the LCS long-code cell.  The exact residual
gate is to obtain a dimension-independent quantum decoder from such
cross-context compatibility, or to groupify a non-affine perfectly complete
test without reintroducing its affine hull.
