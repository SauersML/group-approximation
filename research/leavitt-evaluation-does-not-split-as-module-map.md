---
rg: 2
id: leavitt-evaluation-does-not-split-as-module-map
kind: claim
title: The Leavitt evaluation does not split as a module map and the Leavitt algebra is not projective over the group algebra
invalidates: [leavitt-direct-finiteness-failure-from-module-splitting]
distinct_from:
  leavitt-evaluation-splits-as-module-map: that open claim asks for a left `A`-linear section of the same evaluation; this one is its negation, established from primality of the group algebra, and it is why that node should be read as refuted rather than unattempted.
  augmentation-blocks-unital-leavitt-family: that no-go forbids a *ring* section, by an augmentation count that never sees the module structure; this forbids the strictly weaker *module* section, and it needs a global argument because no local count can see it.
  leavitt-unit-group-algebra-is-prime: that is the structural input, a property of `F_2[R^x]` alone; this is the consequence for one specific map out of it, and it is what removes a route.
  leavitt-group-algebra-not-stably-finite: that is the open matrix-level finiteness failure this lane is aimed at; this is an established module-theoretic no-go about the evaluation map, and it makes that target harder to reach rather than closer.
  left-invertible-lift-of-s0-in-leavitt-group-algebra: that asks for one element `a` over `s_0` with a left inverse, and survives; this forbids the structural machine that would have manufactured such an element wholesale, and says nothing about any particular candidate.
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
---

Let `pi : S = F_2[G] ->> R = L_(F_2)(1,2)` be the evaluation, `G = R^x`,
`K = ker(pi)`.  Then

1. there is no left `S`-linear `sigma : R -> S` with `pi . sigma = id_R`;
2. `R` is **not projective** as a left `S`-module, and not a direct summand of
   any finite free left `S`-module;
3. `K` is not a direct summand of `S` as a left `S`-module.

## The proof in four lines, and where the weight sits

Suppose `sigma` exists and put `p = sigma(1_R)`.  Left `S`-linearity for the
module structure `s . r = pi(s) r` gives `sigma(pi(s)) = s p` for every `s`,
so `pi(p) = 1_R` (hence `p != 0`), `p^2 = sigma(pi(p)) = p`, and

    k p = sigma(pi(k)) = 0     for every  k in K.

`K` is two-sided, so `K S = K` and therefore `K (S p S) = K p S = 0`.  Both
`K` and `S p S` are nonzero two-sided ideals — `K != 0` by
`leavitt-evaluation-kernel-hits-augmentation-one`, and `S p S != 0` because
`p != 0`.  A prime ring admits no such pair.  (2) follows because `R` is
cyclic over `S` and a surjection onto a projective module splits; (3) is (1)
restated.

All the weight is on primality, and hence on
`leavitt-unit-group-algebra-is-prime`.  Nothing local obstructs the splitting:
the idempotent `p` it would produce has `pi(p) = 1_R`, `eps(p) = 0`, and makes
`Sp` a unital ring with identity `p` mapped isomorphically onto `R` by `pi` —
every one of which is consistent with the rest of this graph.  That is why the
route stayed open as long as it did.

## What dies with it

The route `leavitt-direct-finiteness-failure-from-module-splitting`, which was
one of the four sufficient conditions aimed at
`leavitt-unit-group-algebra-not-directly-finite`.  The route's own reasoning
is not at fault — extending `r |-> r s_0` and `r |-> r t_0` across a
complement really would produce `ba = 1 != ab` — it is the complement that
does not exist.

The dynamical reading in `leavitt-evaluation-splits-as-module-map` goes with
it: there is no equivariant linear complement to the annihilator subshift
inside the full shift, which is the concrete form of what
`subshift-self-embedding-carries-no-surjunctivity-content` says abstractly.

## What survives untouched

`binary-leavitt-family-lifts-into-unit-corner` and
`leavitt-corner-one-sided-lift-exists` are unaffected: they ask for elements
of a corner, not for a complement, and no argument here reaches them.
`left-invertible-lift-of-s0-in-leavitt-group-algebra` also survives — this
claim kills the *structural* manufacture of that element, not the element.
