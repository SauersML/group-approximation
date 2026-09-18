---
rg: 2
id: black-box-repetition-needs-sqrt-scale-soundness-gap
kind: claim
title: Any repetition amplifier certified by a universal soundness bound needs soundness deficit gamma >= c sqrt(eta/eps') -- the odd cycle kills sub-sqrt deficits
distinct_from:
  raz-odd-cycle-repetition-lower-bound: that is Raz's theorem about one game; this is the class kill it induces on amplification arguments for UGC from near-1 gaps.
  sqrt-scale-unique-games-hardness-is-equivalent-to-ugc: that proves the sqrt scale suffices; this proves the sqrt scale, and the ratio C ~ eps'^-1/2, are necessary for every black-box repetition argument.
  unique-games-hard-at-completeness-one-half: that is a gap at completeness 1/2; this concerns gaps with both values near 1.
---

**ESTABLISHED (class kill).**

**The class.** A *universal repetition bound* is a function
`F : (0,1] x N -> [0,1]` such that `val(G) <= 1 - gamma` implies
`val(G^(x n)) <= F(gamma, n)` for every bipartite unique game `G`. A *black-box
repetition amplifier* from `Gap-UG_k[1-eta, 1-gamma]` to
`Gap-UG_(k^n)[1-eps', delta']` uses three steps:

* the map `G -> G^(x n)`;
* completeness certified by product strategies, `(1-eta)^n >= 1 - eps'`;
* soundness certified by a universal bound, `F(gamma, n) <= delta'`.

Every Rao-type and Dinur--Steurer-type argument, and Step 1 of
`ugc-sqrt-scale-equivalence-proof`, is of this form.

**Statement.** Let `B` be the constant of `raz-odd-cycle-repetition-lower-bound`.

1. Every universal bound satisfies `F(gamma, n) >= 1 - 4 B gamma sqrt(n)`
   whenever `0 < gamma <= 1/8`.
2. If a black-box amplifier exists with `eps' <= 1/2` and `delta' < 1`, then

   ```text
   gamma  >=  min( 1/8 ,  (1 - delta') sqrt(eta) / (4 B sqrt(2 eps')) ).
   ```

**Invariant and death step.** The invariant is the sqrt-scale deficit ratio
`gamma/sqrt(eta)`. Every member of the class dies at the soundness
certification step:

* **Sub-sqrt deficits die.** A family of gaps with `gamma = o(sqrt(eta))`
  cannot be amplified to any fixed `(eps', delta')`. This includes
  linear-deficit hardness `gamma = L eta` for fixed `L` as `eta -> 0`, and
  every `1 - eta` versus `1 - O(eta)` hardness, such as noise tests whose
  rejection probability is linear in the noise.
* **The ratio must grow.** At the sqrt scale the ratio must satisfy
  `C >= (1 - delta')/(4 B sqrt(2 eps'))`. This matches the sufficient
  `C = sqrt(32 ln(1/delta')/eps')` of the equivalence, up to
  `sqrt(log(1/delta'))`.

**Survivors.** Any of the following escapes the kill:

* amplifiers whose soundness analysis uses the structure of the hard instances,
  for example expansion of the constraint graph, rather than a universal
  bound;
* amplifiers whose completeness exceeds the product-strategy bound;
* non-repetition amplifiers such as graph powering with alphabet reduction.

DERIVATION black-box-repetition-sqrt-scale-proof
