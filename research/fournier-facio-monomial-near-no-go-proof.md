---
rg: 2
id: fournier-facio-monomial-near-no-go-proof
kind: route
title: Forget the phases and obtain a forbidden essentially free near action
target: fournier-facio-monomial-near-witness-impossible
requires:
  - fournier-facio-group-is-nonsofic
---

Write a monomial actor as

```text
pi(g) delta_x = lambda_g(x) delta_(alpha_g x),
```

where `alpha_g` is a permutation of `X` and `|lambda_g(x)|=1`.  Invariance of
the charged diagonal state under `Ad(pi(g))` says exactly that the probability
charge is invariant under `alpha_g`.

For a fixed multiplication row, two monomial unit vectors supported at
different basis points have distance `sqrt(2)`.  Therefore the
charge-almost-everywhere estimate

```text
||pi(gh)delta_x-pi(g)pi(h)delta_x|| < 1
```

forces

```text
alpha_(gh)(x)=alpha_g(alpha_h(x))
```

on a conull set.  Hence the permutations form a measure-preserving near
action in the Elek--Szabo sense.

Likewise

```text
|<delta_x,pi(g)delta_x>|
```

is `1` when `alpha_g(x)=x` and `0` otherwise.  Essential freeness of `pi`
therefore makes this near action essentially free.  The established
Elek--Szabo implication (formalized in the repository as
`isSofic_of_admitsEssentiallyFreeNearAction`) would make `G` sofic,
contradicting `fournier-facio-group-is-nonsofic`.

