---
rg: 2
id: gottschalk-via-proper-domain-duality
kind: route
title: Restrict any decoder to the bounded-defect SFT and forbid dual failures on proper strongly irreducible domains
target: gottschalk-surjunctivity-conjecture
requires:
  - strict-pairs-give-dual-failures-on-bounded-defect-domains
  - proper-sft-domains-admit-no-dual-failures
artifacts:
  - research/artifacts/bounded-defect-domain-duality-2026-09-17.md
---

Let `G` be a group that is not surjunctive.
1. `G` carries a strict pair `(τ, σ)`. An injective, non-surjective automaton has a decoder; see the assembly
   step of `bounded-defect-domain-dual-failure-proof`.
2. By `strict-pairs-give-dual-failures-on-bounded-defect-domains`, some bounded-defect domain `X_R` is a proper
   strongly irreducible SFT, and `σ|_{X_R} : X_R → A^G` is strongly post-surjective and not pre-injective.
3. That contradicts `proper-sft-domains-admit-no-dual-failures` for `G`.

**Comparison with `gottschalk-via-dual-surjunctivity-and-decoder-transfer`.** That route needs two open steps:
- the full-shift dual statement;
- the existence of a full-shift post-surjective decoder (`strict-pairs-admit-post-surjective-decoders`).

This route needs one open step. The decoder step is gone, because every decoder already works on `X_R`. The
cost is that the dual statement must cover proper strongly irreducible SFT domains.
- For amenable groups the remaining step holds (sketch in the claim).
- For sofic groups it is open, and a sketch through sofic entropy is recorded in the claim's Attempts.
- The two steps can fail independently. The established step holds for every group, and the open step is a
  statement about all SFT domains, not only those that come from strict pairs.
