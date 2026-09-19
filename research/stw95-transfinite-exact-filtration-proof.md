---
rg: 2
id: stw95-transfinite-exact-filtration-proof
kind: route
title: Use extensions at successors, sequences at countable limits, and separable stabilization at uncountable limits
target: stw95-transfinite-exact-filtration-reduction
requires:
  - stw95-purity-passes-to-sequential-inductive-limits
---

Proceed by transfinite induction on `alpha<=gamma` to prove that
`I_alpha tensor_min B` is pure.  The zero stage is immediate.

At a successor stage, exactness of `B` gives

```text
0 -> I_alpha tensor_min B
  -> I_(alpha+1) tensor_min B
  -> (I_(alpha+1)/I_alpha) tensor_min B -> 0.
```

The ideal is pure by induction and the quotient is pure by hypothesis.
Perera--Thiel--Vilalta extension permanence makes the middle algebra pure.

Let `lambda` be a limit ordinal.  If `cf(lambda)=omega`, choose an increasing
cofinal sequence `alpha_1<alpha_2<...<lambda`.  Continuity of the filtration
and injectivity of minimal tensoring identify

```text
I_lambda tensor_min B
 =lim_n (I_(alpha_n) tensor_min B).
```

Every stage is pure by induction, so
`stw95-purity-passes-to-sequential-inductive-limits` makes the limit pure.

If `cf(lambda)>omega`, separability makes the filtration stabilize before
`lambda`.  Indeed, choose a dense sequence `(x_n)` in `I_lambda` whose every
tail is dense (repeat the terms of any dense sequence diagonally).  By
continuity, for each `n` choose `alpha_n<lambda` and `y_n in I_(alpha_n)`
with `norm(x_n-y_n)<1/n`.  Put

```text
beta=sup_n(alpha_n+1).
```

Uncountable cofinality gives `beta<lambda`.  Every `y_n` belongs to `I_beta`,
so density and closedness give `I_lambda subseteq I_beta`; the reverse
inclusion is automatic.  Hence `I_lambda=I_beta`, and purity follows from
the induction hypothesis at `beta`.  (A limit ordinal has infinite
cofinality, so these two cases exhaust all limit stages.)  The induction
reaches `I_gamma tensor_min B=A tensor_min B`.

For the final assertion, first fix a simple successor quotient `P` of `A`
and apply the theorem to the filtration of `B`, tensoring by exact `P`.
The hypothesis makes all successor products pure, hence
`P tensor_min B` is pure.  Apply the theorem again to the filtration of
`A`, now tensoring by exact `B`.  Its successor products are precisely the
pure algebras just obtained.
