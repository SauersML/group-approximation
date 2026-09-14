---
rg: 2
id: fournier-facio-compression-subgroup-not-hyperlinear
kind: claim
title: The Kazhdan compression subgroup of the Fournier--Facio group is not hyperlinear
distinct_from:
  fournier-facio-simple-factor-not-hyperlinear: That is the strictly stronger assertion about the simple factor S <= Gamma; this concerns Gamma, the target of every one-compressor argument.
  fournier-facio-has-no-purely-singular-free-near-representation: That is the negative branch for the whole group G; this is the strictly stronger assertion about its Kazhdan subgroup Gamma, and it does not need property (T) of G.
---

Let `Gamma = pi(P) <= G` be the property-(T) compression subgroup of
`fournier-facio-torsion-free-skeleton`.  Then `Gamma` is not hyperlinear.

By `fournier-facio-one-compressor-subgroup-reduces-to-gamma` this is
equivalent to nonhyperlinearity of `<Gamma, t_1>`, or of `<Gamma, t_2>`.  It
is the exact landing point of every obstruction that uses one compressor and
not property (T) of `G`.  It implies the negative branch for `G` by subgroup
permanence, and it is implied by `fournier-facio-simple-factor-not-hyperlinear`.

## Attempts

* **Obstruct the commutant shift.**  Every relation behind
  `fournier-facio-regular-models-carry-commutant-shift` holds in
  `<Gamma, t_1>`, so an argument forbidding that shift in matricial models is
  an argument for this claim.  It dies as stated: the shift is realized in the
  finite von Neumann algebra `L(<Gamma,t_1>)`, so a proof must use matricial
  microstates, and no normalized-HS counting device for proper endomorphisms
  of a commutant is known.
* **Internal compression.**  `Gamma >= pi(P_1) x pi(P_2) x pi(S)` with
  `pi(P_i) = t_i Gamma t_i^-1 ~= Gamma`, a binary self-similar tail.  No
  compressor lies inside `Gamma`, so the OpenAI/Kun--Thom mechanism has no
  internal instance, and property (T) of `Gamma` alone gives no ambient
  expansion.  Dies at the median size-matching step (artifact Section 3(c)).
* **Through the simple factor.**  Route
  `fournier-facio-gamma-not-hyperlinear-via-simple-factor`; its prerequisite is
  deferred in its own node.

Artifact: `research/artifacts/fournier-facio-one-compressor-reduction-2026-09-11.md`.
