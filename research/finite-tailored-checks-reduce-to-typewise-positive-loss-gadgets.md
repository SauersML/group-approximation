---
rg: 2
id: finite-tailored-checks-reduce-to-typewise-positive-loss-gadgets
kind: claim
title: A finite tailored check library reduces exactly to one positive-loss gadget per verifier type
distinct_from:
  tailored-gap-checks-form-common-complete-nemesis-library: that supplies the finite positive check library and its common perfect strategy; this proves that any finite partition of that library may be aggregated without losing soundness or operator-level exactness.
  transitive-controller-orbit-common-twist-preserves-zero-lcu: that cancels one common multiplicity twist after an actual transitive payload orbit has been constructed; this reduction is scalar and does not manufacture that orbit from syntactic equality of verifier types.
  exhaustive-marked-type-energy-summation: that sums estimates over orthogonal finite-group isotypic projections inside one marked packet; this sums positive verifier losses over an arbitrary partition of the finite check set and uses no isotypic decomposition.
---

**ESTABLISHED (finite verifier-type reduction).**  Let `C` be the finite
check set of `tailored-gap-checks-form-common-complete-nemesis-library`, with
positive sampling weights `beta_c` and losing projections `L_c`.  For any
finite partition

```text
C=disjointUnion_(t in T) C_t
```

put, for a tracial strategy `S`,

```text
epsilon_t(S)=sum_(c in C_t) beta_c tau_S(L_c).          (FVT1)
```

Then every CE strategy satisfies

```text
sum_t epsilon_t(S)>=1/2,
max_t epsilon_t(S)>=1/(2|T|).                          (FVT2)
```

Suppose an ordinary marked base group decodes one common CE strategy `S`,
and for every `t` there is an extension gadget `E_t`, all with one common
perfect infinite completion, such that extension of that base type through
`E_t` forces

```text
epsilon_t(S)=0.                                        (FVT3)
```

Then the `E_t` form a common-complete nemesis family: no marked canonical CE
base type extends every `E_t`.  Moreover `(FVT3)` recovers the original exact
check conditions.  Indeed every summand of `(FVT1)` is nonnegative and every
`beta_c` is positive, so `(FVT3)` gives `tau_S(L_c)=0` for every `c in C_t`.
In the faithful tracial GNS quotient, positivity of the projection `L_c`
then gives

```text
L_c=0.                                                  (FVT4)
```

Thus passing from individual checks to finitely many verifier types loses
neither the gap nor operator-level exactness.

**Exact boundary.**  This is a reduction of the **soundness quantifier**, not
a controller construction.  Merely putting two occurrences in the same
syntactic predicate/gate type does not make their payload words one
transitive controller orbit.  The factorization theorem
`transitive-controller-orbit-common-twist-preserves-zero-lcu` requires the
actual conjugacy relations `(TCO4)` among the payload controllers.  Imposing
those relations on arbitrary occurrences changes the perfect strategy;
renaming independent orbit copies avoids the new relations but evaluates the
terms on different strategies.  Therefore `(FVT1)--(FVT4)` does not solve the
typewise nontransport-holonomy readout in
`tailored-checks-to-common-marked-group-extensions`.

Proof: `finite-verifier-type-positive-loss-proof`.

DERIVATION
finite-verifier-type-positive-loss-proof
