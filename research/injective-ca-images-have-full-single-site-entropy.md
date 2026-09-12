---
rg: 2
id: injective-ca-images-have-full-single-site-entropy
kind: claim
title: The single-site output law of an injective automaton from A^G into any full shift has entropy at least log |A|
distinct_from:
  every-injective-ca-has-uniform-single-site-output-law: that concerns endomorphisms of one full shift; this lets the output alphabet differ from the input alphabet and asks only for the entropy bound.
  bernoulli-rokhlin-entropy-maximal-for-every-group: that bounds every measurable generating partition of a Bernoulli shift; this bounds only the finite-radius generators given by injective automata, so it is weaker.
artifacts:
  - research/artifacts/finitary-generation-single-site-criterion-2026-09-12.md
---

**OPEN.** For every group `G`, finite alphabets `A` and `B`, and injective automaton `kappa: A^G -> B^G`,
the law of `kappa(x)(e)` under the uniform product measure on `A^G` has entropy at least `log |A|`.

This is the finite-radius generation invariant, and it sits between the two landmark statements:
- `full-site-entropy-from-bernoulli-rokhlin-maximality`: maximal Bernoulli Rokhlin entropy implies it;
- `uniform-site-law-from-full-site-entropy`: with `B = A` it gives uniform site laws, hence the goal
  through `gottschalk-via-uniform-single-site-output-law`.

## Attempts

- **Escapes the partition-bounded obstruction, but not the goal.** The infimum of site entropy over
  injective automata is at least the Rokhlin entropy, and it depends on the topological coding. So
  `rokhlin-entropy-is-the-largest-partition-bounded-invariant` does not apply to it. Its lower bound still
  implies the goal, so it is at least as hard.
- **Counting stops.** With decoder memory `E`, counting gives only `H >= log |A| sup_F |F|/|F E|`, which
  is below `log |A|` on nonamenable groups. On simple Kazhdan hosts a proof needs input other than
  counting.
- **Known cases.** Amenable groups (Følner counting) and sofic groups (sofic entropy bounds every
  generating partition) satisfy it.
