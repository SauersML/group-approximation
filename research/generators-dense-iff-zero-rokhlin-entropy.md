---
rg: 2
id: generators-dense-iff-zero-rokhlin-entropy
kind: claim
title: Generating partitions of an ergodic action are dense in the Rokhlin metric exactly when its Rokhlin entropy is zero, so a group has dense generators in its free actions exactly when its Rokhlin supremum is zero
distinct_from:
  iid-generators-dense-at-zero-rokhlin-supremum: that asks for density among the partitions with independent translates and a fixed distribution; this proves density among all finite-entropy partitions, which is the non-exact half of that claim.
  iid-generators-not-dense-at-positive-rokhlin-supremum: that shows non-density among i.i.d. partitions of prescribed distribution when the supremum is positive; this is the characterization among all partitions.
---

**ESTABLISHED (unreviewed)** by [[generators-dense-iff-zero-rokhlin-entropy-proof]].

Let `G` be countably infinite and `G ↷ (X, µ)` an ergodic p.m.p. action on a non-atomic standard probability
space. Let `P_H(X)` be the set of countable Borel partitions with finite Shannon entropy, with the Rokhlin
metric `d^Rok(α, β) = H(α | β) + H(β | α)`.

1. The generating partitions are dense in `(P_H(X), d^Rok)` if and only if `h^Rok_G(X, µ) = 0`.
2. The following are equivalent:
   - `h^Rok_sup(G) = 0`;
   - in every free ergodic p.m.p. action of `G`, generating partitions are `d^Rok`-dense;
   - in some Bernoulli shift over `G` with finite nontrivial base, generating partitions are `d^Rok`-dense.
3. **Same window statistics.** When `h^Rok_G(X) = 0`, every partition `β` has, for each `ε > 0`, a generating
   partition that coincides with `β` off a set of measure at most `ε`. It uses two new labels on that set. In
   particular, near every i.i.d. partition of a Bernoulli shift there are generating partitions whose
   finite-window statistics differ from it by at most `|W|·ε` in total variation.

**Reading.**
- For `iid-generators-dense-at-zero-rokhlin-supremum`, the non-exact half holds at zero supremum. What remains
  is exactification: make an approximately i.i.d. generating partition exactly i.i.d. while keeping what it
  captures.
- At positive supremum even the non-exact half fails, trivially: the trivial partition `{X}` has no generator
  within `d^Rok`-distance `h^Rok_G(X)`.
- Model test. An irrational rotation, as a `Z`-action, has entropy `0`, and item 1 makes its generating
  partitions dense. A Bernoulli shift over `Z` has positive entropy, and item 1 says its generators are not
  dense near `{X}`.

**Credit.** Item 1 `⇐` is a direct consequence of Seward's small-support generators
(`seward-small-support-relative-generators`, Part I, Theorem 2.3). The density formulation was not found in
Sections 1 and 2 of arXiv:1405.3604; the check was bounded to those sections.
