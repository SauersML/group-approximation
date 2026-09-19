---
rg: 2
id: finite-monoid-table-embeddings-forbid-bernoulli-deficit
kind: claim
title: A Bernoulli witness pattern whose product table embeds in a finite monoid has full value, and exact finite models reach exactly these patterns
distinct_from:
  finite-core-height-potential-forbids-bernoulli-deficit: that needs a height potential with finite zero-height core and builds padded germ models; this needs only an injective partial homomorphism of the Q-table into some finite monoid, contains that theorem as the special case of a sink transformation monoid, and characterizes exact finite models.
  rokhlin-maximality-closed-under-local-embeddings: that transports configurations along injective partial multiplication tables into groups; this allows a finite monoid target in which non-read letters are non-invertible, and needs no maximality of the target.
  reading-model-entropy-certificates-are-soficity: that shows double-count certificates on ball configurations are equivalent to soficity; this shows exact finite certificates of all configurations are equivalent to LEF, while exact certificates of single patterns reach beyond LEF groups.
  sofic-radical-localizes-bernoulli-deficit-witnesses: that uses approximate permutation models of a sofic subgroup; this uses exact non-injective models of one finite table and assumes nothing about any subgroup.
artifacts:
  - research/artifacts/finite-monoid-certificates-2026-09-17.md
  - experiments/finite-monoid-certificates-2026-09-17/check_monoid_model.py
---

Let `G` be a countable group, `|A| = q >= 2`, and `(k, E, F, psi)` a configuration as in
`bernoulli-rokhlin-deficit-has-a-finitary-witness`, with value `Phi`. Put `Q = {1} ∪ E ∪ FE`.

A *Q-table embedding* into a finite monoid `M` is a map `lambda : E ⊔ F -> M` such that the rule
`[1] = 1_M`, `[e] = lambda(e)`, `[fe] = lambda(f) lambda(e)` is a well-defined injective function
`Q -> M`. So equal elements of `G` get equal values, and distinct ones get distinct values.

**Theorem M.** If the pattern has a Q-table embedding into a finite monoid, then `Phi >= log q`.

**Theorem M' (converse).** A finite functional model (`T_f`, `S_e` on a finite set, as in Lemma 1 of
`research/artifacts/height-graded-germ-models-2026-09-17.md`) whose coincidences hold at every point
and which has one good point gives a Q-table embedding into the opposite of its transformation
monoid.

**Corollaries.**
- *Corollary A.* A height potential with finite core gives a Q-table embedding into a transformation
  monoid with a sink. So `finite-core-height-potential-forbids-bernoulli-deficit` follows.
- *Proposition R.* Letters in read pairs map to units. If every letter is read, then `[Q]` lies in the
  finite group `U(M)`.
- *Corollary R.* Every configuration over `G` is finite-monoid embeddable if and only if `G` is LEF.

**Consequence (filter and kill).**
- Every deficit witness over any group has a Q-table with no injective partial homomorphism into any
  finite monoid.
- Every exact finite model of such a pattern has no good point. Any finite-model certificate for it
  must be approximate: its coincidences fail on every invariant set containing a good point.
- At group level, exact finite models certify every configuration over `G` only when `G` is LEF.

Full proofs are in Sections 1 to 5 of the artifact. Section 6 records the open prerequisites (D1)-(D3) and
the two questions left open.

**ESTABLISHED 2026-09-17** by [[finite-monoid-table-embeddings-proof]].
