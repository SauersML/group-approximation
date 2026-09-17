---
rg: 2
id: fpbs-q-normal-chain-fixed-price-consequence-scope
kind: claim
title: The fixed-price-one consequence of the q-normalizer chain lemma is supported by a Bernoulli maximal-cost import matching its group hypotheses
distinct_from:
  fpbs-bernoulli-maximal-cost: that records maximal cost of the Bernoulli action for infinite finitely generated groups; this is the scope gap asking that the chain lemma's fixed-price consequence be restricted to that class or backed by an import for all countably infinite groups.
  fpbs-q-normal-hyperfinite-chain-forces-cost-one: that is the per-action chain lemma C(R)=1 with its consequences; this is the import-scope gap a referee found in the consequences of its proof route.
---

**OPEN.** This is the scope gap found by referee lens 2 (2026-09-17) in the
route `fpbs-q-normal-hyperfinite-chain-forces-cost-one-proof`. The lens found
the main lemma `C(R)=1` sound. What is missing is support for one consequence.

**Claim.** One of the following holds, and the claim and route
`fpbs-q-normal-hyperfinite-chain-forces-cost-one(-proof)` are edited to match.

1. **Restriction.** The consequence "a chain for the Bernoulli action gives
   `Gamma` fixed price one" is stated only for infinite finitely generated
   `Gamma`, which is the hypothesis of `fpbs-bernoulli-maximal-cost`.
2. **Stronger import.** A verbatim source shows that the Bernoulli action has
   maximal cost among free p.m.p. actions of every countably infinite group,
   and it is recorded as an ESTABLISHED claim that the route imports. Likely
   reference, not verified: Abert--Weiss, *Bernoulli actions are weakly
   contained in any free action* (2013), together with Kechris's
   weak-containment monotonicity of cost.

Once either option is recorded, this claim can be closed and the chain lemma's
route refereed again. The `beta_1^(2)=0` consequence, via
`fpbs-amen2-betti-cost-input`, is not affected.
