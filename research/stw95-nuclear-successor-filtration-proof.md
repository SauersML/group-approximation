---
rg: 2
id: stw95-nuclear-successor-filtration-proof
kind: route
title: Semisplit nuclear cells tensor exactly and transfinite continuity finishes the filtration
target: stw95-nuclear-successor-filtrations-need-no-exact-factor
requires:
  - stw95-af-factor-preserves-purity
  - stw95-purity-passes-to-sequential-inductive-limits
---

We first isolate the successor-stage mechanism.  Consider a short exact
sequence

```text
0 -> I -> E --q--> Q -> 0
```

with `Q` separable and nuclear.  The Choi--Effros lifting theorem gives a
completely positive contractive map `s:Q->E` satisfying `q s=id_Q`.  Set

```text
P=id_E-s q:E->I.
```

The map `P` is completely bounded, is the identity on `I`, and has range in
`I`.  For every C*-algebra `A`, both `id_A tensor s` and
`id_A tensor P=id-(id_A tensor s)(id_A tensor q)` extend boundedly to the
minimal tensor products.  If

```text
x in ker(id_A tensor q:A tensor_min E -> A tensor_min Q),
```

then `x=(id_A tensor P)(x)`.  Since `id_A tensor P` sends the algebraic
tensor product into `A odot I`, continuity puts `x` in `A tensor_min I`.
The reverse inclusion is automatic, and `id_A tensor q` is onto.  Hence

```text
0 -> A tensor_min I -> A tensor_min E -> A tensor_min Q -> 0
```

is exact without any exactness hypothesis on `A`.

Now prove by transfinite induction that `A tensor_min J_alpha` is pure.  The
zero stage is immediate.  At a successor stage, `L_alpha` is separable
because `B` is separable, and it is nuclear by hypothesis.  Apply the
preceding semisplit argument to

```text
0 -> J_alpha -> J_(alpha+1) -> L_alpha -> 0.
```

After tensoring by `A`, its ideal is pure by induction and its quotient is
pure by hypothesis.  Extension permanence of purity therefore makes
`A tensor_min J_(alpha+1)` pure.

Let `lambda` be a limit ordinal.  If `cf(lambda)=omega`, take an increasing
cofinal sequence `alpha_1<alpha_2<...<lambda`.  Injectivity of minimal
tensoring and algebraic density give

```text
A tensor_min J_lambda
 = lim_n (A tensor_min J_(alpha_n)).
```

Every stage is pure, so
`stw95-purity-passes-to-sequential-inductive-limits` makes the limit pure.

If `cf(lambda)>omega`, separability of `J_lambda` makes the filtration
stabilize below `lambda`.  Choose a dense sequence `(x_n)` in `J_lambda`
whose every tail is dense.  Choose `alpha_n<lambda` and
`y_n in J_(alpha_n)` with `norm(x_n-y_n)<1/n`, and put

```text
beta=sup_n(alpha_n+1)<lambda.
```

Then all `y_n` lie in `J_beta`; they are dense in `J_lambda`, so
`J_lambda=J_beta`.  Purity follows from the induction hypothesis at `beta`.
These two cases exhaust limit ordinals, and the induction reaches
`J_gamma=B`.

For the AF-layered corollary, each `L_alpha` is nuclear and
`stw95-af-factor-preserves-purity` makes `A tensor_min L_alpha` pure whenever
`A` is pure.  The theorem applies.  Notice that only the individual layers,
not the extension algebra `B`, are asserted to be AF.
