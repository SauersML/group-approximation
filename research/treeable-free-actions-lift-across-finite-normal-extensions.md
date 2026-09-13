---
rg: 2
id: treeable-free-actions-lift-across-finite-normal-extensions
kind: claim
title: A free p.m.p. action with treeable orbit relation lifts across every finite normal extension of the acting group
distinct_from:
  bernoulli-lifts-across-finite-kernels-force-virtual-splitting: that forbids lifting Bernoulli shifts over w-rigid quotients unless the extension virtually splits; this shows lifting is automatic, with no splitting at all, as soon as the orbit relation is treeable.
  weakly-bernoulli-liftable-actions-force-virtual-splitting: that is the open approximate rigidity question over w-rigid quotients; this is the flexible side, which answers the positive polarity whenever a treeable free action is weakly contained in Bernoulli shifts.
---

**ESTABLISHED (unreviewed)** by [[treeable-free-actions-lift-across-finite-normal-extensions-proof]].

Let `1 -> N -> W -π-> Q -> 1` be an extension of countable groups with `N` finite, central or not. Let
`Q ↷ (Y, μ)` be a free p.m.p. action whose orbit equivalence relation `R_Y` is treeable. Then `Y` lifts:
there is a free p.m.p. action `W ↷ (X, ν)` and a `π`-equivariant factor map `X -> Y` whose fibres are single
free `N`-orbits. One can take `X = Y × N` with `ν = μ × (uniform)`.

**Lifting criterion (proved in the route, used everywhere below).** A free p.m.p. `Q`-action `Y` lifts exactly
when the tautological cocycle `Q × Y -> Q` lifts to `W`: there is a Borel `φ : Q × Y -> W` with
`π(φ(q, y)) = q` and `φ(q_1 q_2, y) = φ(q_1, q_2 y) φ(q_2, y)` almost everywhere. Given `φ`, the lift is
`w·(y, n) = (π(w)y, w n φ(π(w), y)^-1)`. For central `N` this says the class of the extension dies in the
measured groupoid cohomology `H^2(Q ⋉ Y; N)`.

**Consequences.**
- **Extensions inherit liftability.** If `Z -> Y` is a factor map of free `Q`-actions and `Y` lifts through `φ`,
  then `Z` lifts through `φ(q, p(z))`. So every free action with a treeable free factor lifts.
- **Positive polarity from treeability.** If some free `Q`-action with treeable orbit relation is weakly
  contained in the Bernoulli shift `[0,1]^Q`, then `Q` carries a liftable action weakly equivalent to Bernoulli
  (the reverse containment is `abert-weiss-free-actions-weakly-contain-bernoulli`), for every finite extension
  of `Q` at once. When `[0,1]^Q` is itself treeable, the Bernoulli shift lifts exactly.
- **Non-treeability from rigidity.** Combined with `bernoulli-lifts-across-finite-kernels-force-virtual-splitting`:
  if `Q` is w-rigid and has a finite extension that does not virtually split, no Bernoulli shift of `Q` has
  treeable orbit relation. For `Sp_4(Z)` and Deligne's triple cover this recovers, by a cohomological route, a
  known kind of non-treeability for Kazhdan groups.
- **Where the obstruction lives.** Any obstruction to lifting, exact or approximate, is invisible on treeable
  pieces. Over an amalgam `A *_C B` of groups all of whose free actions are treeable, lifts exist on
  `A ⋉ Y` and `B ⋉ Y`, and the obstruction is the failure to match them on `C ⋉ Y`.

**Model test.**
- Hypothesis side: `Q = Z` acting by an irrational rotation, with `W = Z × C_2`, satisfies everything, and
  the conclusion is trivial there. Deligne's `E_3 -> Sp_4(Z)` with its Bernoulli shift fails the treeability
  hypothesis, by the rigidity consequence above. So the hypothesis is not vacuous and not automatic.
- Conclusion side: the theorem produces no splitting of the extension over any subgroup. That is consistent,
  because the lift twists the fibre coordinate by a point-dependent `φ`.
