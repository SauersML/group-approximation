---
rg: 2
id: glue-lemma-escape-clause-voids-the-conclusion
kind: claim
title: An additive dictator perturbation triggers the escape clause while preserving the hypotheses, so the clause must be deleted
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
---

**ESTABLISHED.**  The affine orientation-glue statement was handed over in
the form

> ... there is `Q` with `|Q| <= L` and
> `Pr_{b in B}[C_b intersect Q != empty] >= gamma`, **unless `f` already has
> a large ambient low-degree influence.**

The clause is not a harmless hedge.  It can be switched on by an additive
perturbation that changes nothing about the difficulty.

**The perturbation.**  Let `f` satisfy the hypotheses with heaviness
`delta`, and pick `z in Omega` with `hat{T_rho f}(z) = 0`.  Set

```text
f' = ( X_z + f ) / 2,      g' = T_rho f' = ( rho X_z + g ) / 2.
```

Then

* `f'` maps into `[-1,1]`, so it satisfies the hypotheses' range condition;
* `Inf^{<=d}_z(g') = rho^2/4`, so `f'` **does** have a large ambient
  low-degree influence and the escape clause fires;
* `g'|_{D_b} = ( rho * Y_{[z]_b} + g|_{D_b} ) / 2`, and the extra term lives
  on the single quotient coordinate `[z]_b`.  So for every `b` with
  `z notin C_b`,

```text
Inf^{<=d}_{C_b}( g'|_{D_b} ) = (1/4) * Inf^{<=d}_{C_b}( g|_{D_b} ) >= delta/4,
```

  i.e. the same cosets `C_b` are heavy for `f'`, at heaviness `delta/4`.

So `f'` satisfies the hypotheses with `delta/4`, has exactly the same heavy
cosets as `f` outside the at most two directions with `z in C_b`, and the
statement **asserts nothing whatever about it**.  Meanwhile a decoder
taking the escape branch is handed `Q = {z}`, which hits only the cosets
containing `z` -- a `O(1/N)` fraction when the centres `q_b` are spread.

**Consequence.**  In a soundness analysis `f` is an adversarial strategy,
so the adversary buys the escape clause for the price of one coordinate.
The clause has to be **deleted**: the statement the decoder needs is the
plain one, with `Q` an arbitrary set of size at most `L`.  The influential
coordinates then reappear where they belong, as one admissible choice of
`Q`, which is exactly how `glue-lemma-holds-for-quadratic-functions`
produces them at ambient degree two.

This is a correction to the target statement, not an obstruction to it.
`affine-orientation-glue-lemma` has been edited to the escape-clause-free
form, which is strictly stronger and is the form the region now attacks.

The proof is `glue-lemma-escape-clause-void-proof`.
