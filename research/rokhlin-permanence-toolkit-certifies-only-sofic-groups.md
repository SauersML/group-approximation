---
rg: 2
id: rokhlin-permanence-toolkit-certifies-only-sofic-groups
kind: claim
title: Started from sofic groups, the landed Rokhlin-maximality permanence operations produce only sofic groups
distinct_from:
  fg-simple-subgroups-of-local-embedding-free-closure-are-sofic: that concerns the surjunctivity permanence closure without local embeddings and its finitely generated simple subgroups; this concerns the Rokhlin-maximality operations, local embeddings included, and identifies the whole closure with the sofic class.
  sofic-permanence-closure-omits-simple-fa-nonsofic-groups: that excludes one finitely presented simple nonsofic FA group from a closure under arbitrary extensions; this shows the closure under the landed Rokhlin operations is the sofic class itself.
  weakly-bernoulli-liftable-finite-extensions-are-sofic: that is the soficity transfer for one operation, finite ascent through a weakly Bernoulli lift; this assembles it with the other five operations into a closure theorem.
artifacts:
  - research/artifacts/gk3-rokhlin-tester-2026-09-14.md
  - research/artifacts/gk3-rokhlin-tester-2026-09-14-part2.md
---

**ESTABLISHED (unreviewed)** by `rokhlin-permanence-toolkit-sofic-closure-proof`.

Let `R` be the smallest class of countable groups that contains every sofic group and is closed under the six
operations for which main proves that Rokhlin maximality of uniform Bernoulli shifts transfers:
1. subgroups (`bernoulli-rokhlin-maximality-passes-to-subgroups`);
2. finite-index overgroups (same node);
3. local embeddings, hence directed colimits with arbitrary structure maps
   (`rokhlin-maximality-closed-under-local-embeddings`);
4. overgroups of an infinite co-amenable subgroup (`rokhlin-maximality-ascends-co-amenable-subgroups`);
5. quotients by finite normal subgroups (`rokhlin-maximality-descends-along-finite-normal-quotients`);
6. extensions `W` of a finitely generated member `Q = W/N` by a finite normal subgroup `N`, in cases (i) and (ii) of
   `finite-kernel-rokhlin-ascent-from-weakly-minimal-lift`:
   - (i) some finite-entropy free ergodic `Q`-action lifting to a free `W`-action is weakly contained in all free
     `Q`-actions;
   - (ii) some finite-entropy Bernoulli shift of `Q` lifts.

Case (iii) of that node is `seward-direct-product-relative-rokhlin-entropy-conjecture`. It is open and is not an
operation here.

Then `R` is exactly the class of sofic groups.

**Consequences.**
- **Tester host.** The host `U` of `gottschalk-surjunctivity-fixed-two-generator-tester` contains the finitely presented
  nonsofic group of `fp-surjunctive-nonsofic-group-exists`, so `U ∉ R`.
  - No iteration of the landed permanence theorems proves `bernoulli-rokhlin-entropy-maximal-on-fixed-tester`.
  - The Rokhlin route to Gottschalk's conjecture needs a lower-bound mechanism that is not a permanence theorem.
- **Candidates.** The known candidates are open:
  - `seward-direct-product-relative-rokhlin-entropy-conjecture`;
  - `rokhlin-window-transport-is-dominated`, on a nonsofic canonical host;
  - `rokhlin-maximality-ascends-amenable-normal-extensions`.
- **Deligne's triple cover.** `E_3 ∈ R` iff `deligne-triple-cover-is-sofic`.

**Scope.** This is a barrier about the toolkit. It does not say that any nonsofic group fails maximality. It sharpens
the scope remark on `rokhlin-maximality-ascends-co-amenable-subgroups`, that every group known to be maximal is sofic,
into a closure statement that holds under any order of the six operations.

**Model test.**
- **Hypothesis side.** Weak containment in operation 6 is consumed by the soficity transfer. Case (iii), which drops
  it, is not covered.
- **Conclusion side.** The Kun–Thom wreath and nonsofic Gohla–Thom extensions lie outside `R`. This is consistent with
  `kun-thom-wreath-bernoulli-rokhlin-maximal` being open, and with `gohla-thom-lattices-no-weakly-bernoulli-liftable-action`
  excluding operation 6 there.
