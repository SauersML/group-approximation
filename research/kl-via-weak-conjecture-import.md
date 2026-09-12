---
rg: 2
id: kl-via-weak-conjecture-import
kind: route
title: Import a claimed proof of the weak conjecture and transfer it to coefficient injectivity
target: kervaire-laudenbach-nonsingular-conjecture
requires: []
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

The weak Kervaire conjecture — the free product of a nontrivial group with
`Z` does not have weight one — has a claimed proof in the literature
(Kawauchi, arXiv:2303.13728).  Klyachko's equivalence turns weak
nontriviality into coefficient injectivity, so importing the claimed theorem
would establish the target and close this whole region at a stroke.

Dead twice over.

1. `weak-kervaire-transfers-only-at-unimodular-degree`: the weak conjecture
   has content only at `m = ±1` — the other degrees are automatic from the
   exponent-sum quotients — and the equivalence is with **unimodular**
   coefficient injectivity.  The target is quantified over every `m != 0`, so
   even a correct weak proof leaves `|m| > 1` untouched.
2. `kawauchi-weak-kervaire-rests-on-unresolved-inputs`: the claimed proof's
   own supporting manuscript states its dependence on the smooth unknotting
   and smooth 4D Poincaré conjectures, so importing it would replace one open
   problem with several stronger claimed resolutions rather than closing
   anything.

**What survives the demolition.**  A future *unimodular* route: should the
weak conjecture be settled by independently closed means, it would establish
the `m = ±1` case of the target, which is the case the literature regards as
hard.  That would be worth a node of its own; it would not be this one, and
it would still leave `|m| > 1` to prove.
