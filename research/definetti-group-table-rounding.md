---
rg: 2
id: definetti-group-table-rounding
kind: claim
title: Dimension-free symmetric-extension rounding of a finite multiplication table
distinct_from:
  hyperlinear-implies-sofic: that is the group statement, quantified over all groups and all windows at once; this is a single quantitative theorem about one finite table, with its own parameters (extension level, defect threshold) chosen in a fixed order, and it is strictly stronger — it supplies an explicit rounding map, not only the existence of some sofic approximation.
  group-table-cpsd-cp-face-collapse: that asks whether two convex cones have the same closure on the group-table face — a statement about exact optima with no rate; this asks for a quantitative rounding at a finite extension level, and would give the collapse a constructive proof rather than the other way round.
  geometric-schreier-design: that rounds positions on a sphere into a labelled Schreier graph and its enemy is the discrete/continuous index gap; this rounds a symmetric-extension moment object and its enemy is product-state integrality. Neither statement mentions the other's object.
artifacts:
  - research/artifacts/hyperlinear-divergent-strategies-2026-08-18.md
---

**Target (Target A of the source dossier).**  For every finite partial
multiplication table `T` and every `eps > 0` there exist an extension level
`m = m(T,eps)` and a threshold `eta = eta(T,eps,m) > 0` such that: every
balanced, regular-trace, `m`-symmetric-extendible unitary solution of `T` with
multiplicative defect `< eta` rounds to a permutation solution of `T` with
Hamming defect `< eps` — **with no dependence on the matrix dimension**.

The order of quantifiers is the whole point: fix the table, fix `eps`, then
choose `m`, and only afterwards ask hyperlinearity for a microstate accurate
enough.  Nothing has to be uniform over tables, and nothing may depend on `d`.

**The four properties an encoding must have.**  Build a convex relaxation
`Q_m(T)` whose variables are moments of the microstate, with

- **(DF1) unitary lift** — a microstate of HS defect `delta` gives a feasible
  `m`-symmetric point with constraint violation `O(sqrt(m)·delta)`;
- **(DF2) dimension-free local norm** — every table constraint is controlled
  in normalized HS norm with absolute constants;
- **(DF3) de Finetti collapse** — every feasible `m`-symmetric point is
  `O(m^{-1/2})`-close, in that norm, to a mixture of product assignment
  states;
- **(DF4) product-state integrality** — product assignment states satisfying
  the table constraints round, with dimension-free loss, to partial
  bijections, repaired to permutations by a Hall-type argument.

Then `m → ∞` with `delta → 0` and `m·delta^2 → 0` sends both errors to zero.

**Why the parameter arithmetic now works.**  (DF1) is supplied by
`balanced-replica-hs-amplification`: balanced replication costs a factor
`sqrt(2m)` in defect and nothing in dimension, so `m` may be chosen after the
table.  (DF3) is the shape of the 2026 dimension-free bosonic de Finetti
theorem in Hilbert–Schmidt distance — Jeronimo–Wu–Xu, arXiv:2608.02590
(2026-08-03), optimal rate `Θ(N^{-1/2})`, error independent of the local
Hilbert-space dimension, proved by argmax/SOS rounding of a
symmetric-extension SDP; Miyamoto arXiv:2608.07986 (2026-08-08) has a
dimension-independent HS version tolerating logarithmically many observed
registers, which is what a table needing more than two local marginals would
want.  **Neither theorem is imported as a premise here**: they are stated for
bosonic/exchangeable quantum states, not for a group-table relaxation, and the
work of this claim is to build a relaxation to which an argument of that kind
applies.

**Where the difficulty is concentrated: (DF4).**  Two encodings are known to
fail.  A Choi-state encoding puts the de Finetti split between copies, which
says nothing about classicality *inside* the input–output pair.  A dephasing
encoding is refuted outright (`dephasing-destroys-multiplicativity`).  So the
object must keep path coherence until the multiplication constraints are
imposed and only then let symmetry destroy the phase.  The dossier's candidate
is the path-amplitude tensor for a relation `gh = k`,

```text
T^{g,h,k}_{i,j,l} = (U_g)_{l,j} · (U_h)_{j,i} · conj((U_k)_{l,i}),
```

whose permutation solutions are exactly the one-hot ones; the proposal is to
build a positive doubled moment object from `T`, take balanced replicas,
symmetrize, and ask whether an argmax principle concentrates the mass on a
bounded number of path choices.  That is a proposal, not a lemma.

## Attempts

- **Import the de Finetti theorem directly on the Choi states of the
  microstate.**  Dies immediately: the tensor split is wrong.  Symmetry across
  replicas gives a mixture of product states across *copies*, whereas the
  needed classicality is between the input and output index of a single copy,
  where the Choi vector of a unitary is maximally entangled — and so is that
  of a permutation, so the quantity does not even discriminate.
- **Classicalize first, then impose the relations** (dephasing to
  unistochastic matrices, Birkhoff, sample).  Refuted:
  `dephasing-destroys-multiplicativity`; recorded as the dead route
  `sofic-model-via-unistochastic-dephasing`.
- **Replicate the channels and use asymptotic quantum Birkhoff.**  Refuted:
  `asymptotic-quantum-birkhoff-false`; recorded as the dead route
  `sofic-model-via-quantum-birkhoff-channel-rounding`.  This is the sharpest
  warning available — any proof of the present claim must use the group table
  and the regular trace, since the same statement for arbitrary bistochastic
  channels is false.
- **Entrywise tropicalization** (take `|·|^m` and let `m → ∞` to select a
  path).  Dies on Fourier/Haar-like blocks, where many entries share the same
  modulus and the limit preserves a large tie instead of selecting; breaking
  ties by a generic perturbation destroys the multiplicative coherence that
  was the reason to be there.
- **Deferred, and the recommended next step:** the associativity square
  `gh = k`, `hr = s`, `gs = t`, `kr = t` is the smallest instance with genuine
  interaction between relations, where independently-rounded pairs can be
  globally inconsistent.  A low-level noncommutative moment relaxation with
  symmetric extensions can be optimized numerically against a collision
  functional; if the optimum fails to decay like `m^{-1/2}` uniformly in the
  matrix dimension, this claim is dead and the counterexample is a candidate
  finite gap for `finite-table-quantum-classical-hamming-gap`.
