---
rg: 2
id: injective-ca-random-order-transport-is-dominated
kind: claim
title: The random-order decoder transport into one output site of an injective automaton is at most that site's entropy
distinct_from:
  injective-ca-images-have-full-single-site-entropy: that is the site-entropy bound itself; this is an information inequality among transport terms, equivalent to it through the transport identity, which splits log |A| into |N| averaged conditional mutual informations.
  every-injective-ca-has-uniform-single-site-output-law: that asks for a uniform site law with the output alphabet equal to the input alphabet; this is the domination form of the entropy bound for any output alphabet.
artifacts:
  - research/artifacts/random-order-decoder-transport-2026-09-12.md
---
**OPEN.** For every group `G`, finite alphabets `A`, `B`, injective automaton `kappa : A^G -> B^G` with left-inverse
memory `N` containing `e`, `y = kappa(x)` with `x` uniform, and i.i.d. order labels `U`:

    sum_(n in N) I( x(n^-1) ; y(e) | y(n^-1 N ∩ past(e)), U ) <= H(y(e)) .

By `injective-ca-random-order-transport-identity` the left side equals `log |A|`, so this is equivalent to
`injective-ca-images-have-full-single-site-entropy`, hence to the goal (two routes, intended cycle). It is a normal
form. It is kept because it isolates the conditionings as the whole difficulty and calibrates correctly.

## Attempts
- **Unconditioned case.** With no conditioning, domination is superadditivity of mutual information over the
  independent inputs `x(n^-1)`, and holds. The difficulty is carried entirely by the other decoder outputs of each
  input site that lie in the random past of `e` (artifact 3.1).
- **Pointwise in the order: false.** A bijective automaton on Z with `N = {0, 1}` gives output-side sum `3` bits
  against `H(y(0)) = 2` for one order realization (artifact 3.2). Any proof must average over the invariant random
  order.
- **Tree calibration.** On `Aut(T, xi)` domination holds, but the transport identity fails with ratio `2`, the
  modular function (artifact 2.1). So a strict automaton off groups is paid for by imbalance, not by violating
  domination. Neither the tree nor inertness kills this form.
- **Amenable decoder memory.** Holds when `Gamma = <N>` is amenable. That includes two-point decoder memory.
  - For `B = A`: `amenable-decoder-memory-forces-surjectivity` gives bijectivity, hence a uniform site law.
  - For `B != A`: that theorem does not apply. Count inside `Gamma` instead: `|F| log |A| <= |FN| H(y(e))`, then take
    right Folner sets of `Gamma` (w4-vf-positive-b, artifact 3.3).
- **First open case.** Three-point decoder memory with a nonamenable decoder group,
  `three-point-decoder-memory-injective-ca-are-surjective`. Domination there is a finite inequality among ten
  variables. Relations of `<N>` enter through site coincidences, and relations of the host through the encoder windows
  (corrected; artifact 3.3). No proof or counterexample is known, including the free decoder group.
- **Discarded on the way** (artifact Section 4): exactness transfer (left equivariance, no right Folner sets),
  free subrelations with the f-invariant (not generating, and a conjugacy invariant), symbol symmetrization
  (orbits break uniformity).
- **Per-term bounds reproduce subadditivity** (`transport-identity-gives-reciprocal-memory-entropy-bound`). Bounding
  each term by `H(y(e))` gives `H(y(e)) >= (log |A|)/|N|`. That is the elementary bound
  `log |A| <= H(y|_N) <= |N| H(y(e))`, so the identity adds nothing at that level. Domination is the constant-`1` case.
  The sharper per-term bound gives `sum_n H(y(e) | Z_n, U) >= log |A|`, which is not domination. A proof must use the
  conditionings jointly. (Corrected at the second landing: the first entry claimed the per-term bound is attained and
  that domination needs realizability beyond Shannon inequalities; attainment holds only for one order realization, and
  the impossibility was never shown.)
