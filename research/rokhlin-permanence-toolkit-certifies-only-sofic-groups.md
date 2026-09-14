---
rg: 2
id: rokhlin-permanence-toolkit-certifies-only-sofic-groups
kind: claim
title: Started from sofic groups, the landed Rokhlin-maximality permanence operations produce only sofic groups
distinct_from:
  fg-simple-subgroups-of-local-embedding-free-closure-are-sofic: that concerns the surjunctivity permanence closure without local embeddings and its finitely generated simple subgroups; this concerns the Rokhlin-maximality operations, local embeddings included, and identifies the whole closure with the sofic class.
  sofic-permanence-closure-omits-simple-fa-nonsofic-groups: that excludes one finitely presented simple nonsofic FA group from a closure under arbitrary extensions; this shows the closure under the landed Rokhlin operations is the sofic class itself.
  weakly-bernoulli-liftable-action-makes-extension-sofic: that is the soficity transfer for one operation, finite central ascent through a weakly Bernoulli lift; this assembles it with the other five operations into a closure theorem.
artifacts:
  - research/artifacts/gk3-rokhlin-tester-2026-09-14.md
---

**ESTABLISHED (unreviewed)** by `rokhlin-permanence-toolkit-sofic-closure-proof`.

Let `R` be the smallest class of countable groups containing every sofic group and closed under the six operations
for which main proves that Rokhlin maximality of uniform Bernoulli shifts transfers:
1. subgroups (`bernoulli-rokhlin-maximality-passes-to-subgroups`);
2. finite-index overgroups (same node);
3. local embeddings, hence directed colimits with arbitrary structure maps
   (`rokhlin-maximality-closed-under-local-embeddings`);
4. overgroups of an infinite co-amenable subgroup (`rokhlin-maximality-ascends-co-amenable-subgroups`);
5. quotients by finite normal subgroups (`rokhlin-maximality-descends-along-finite-normal-quotients`);
6. finite central extensions of a finitely presented member admitting a liftable free action weakly contained in the
   Bernoulli shift of the base (`finite-kernel-rokhlin-ascent-from-weakly-minimal-lift`, cases (i) and (ii)).

Then `R` is exactly the class of sofic groups.

**Consequences.**
- **Tester host.** The host `U` of `gottschalk-surjunctivity-fixed-two-generator-tester` contains the finitely presented
  nonsofic group of `fp-surjunctive-nonsofic-group-exists`, so `U ∉ R`. No iteration of the landed permanence theorems
  proves `bernoulli-rokhlin-entropy-maximal-on-fixed-tester`. The Rokhlin route to Gottschalk's conjecture needs a
  lower-bound mechanism that is not a permanence theorem.
- **Candidates.** The known candidates are open:
  - `seward-direct-product-relative-rokhlin-entropy-conjecture`, in case (iii) of the finite-kernel ascent;
  - `rokhlin-window-transport-is-dominated`, on a nonsofic canonical host;
  - `rokhlin-maximality-ascends-amenable-normal-extensions`.
- **Deligne's triple cover.** `E_3 ∈ R` iff `deligne-triple-cover-is-sofic`.

**Scope.** This is a barrier about the toolkit. It does not say that any nonsofic group fails maximality. It sharpens
the scope remark on `rokhlin-maximality-ascends-co-amenable-subgroups`, that every group known to be maximal is sofic,
into a closure statement that holds under any order of the six operations.

**Model test.**
- **Hypothesis side.** Finite presentation in operation 6 is consumed by the soficity transfer, which uses a
  presentation of the base.
- **Conclusion side.** The Kun–Thom wreath and nonsofic Gohla–Thom extensions lie outside `R`. This is consistent with
  `kun-thom-wreath-bernoulli-rokhlin-maximal` being open and with `gohla-thom-lattices-no-weakly-bernoulli-liftable-action`
  excluding operation 6 there.
