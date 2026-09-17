---
rg: 2
id: fpbs-commensurated-subgroup-sparse-spines
kind: claim
title: An infinite commensurated subgroup of infinite index with summable sheet trees gives invariant sparse spines, so BS(m,n) and finite-lamp wreath products carry soft collapse families
distinct_from:
  fpbs-soft-collapse-on-fg-normal-and-kazhdan-groups: that builds spines over a finitely generated normal subgroup, where the projected walk is a Markov chain on the quotient group; here the subgroup is only commensurated (no quotient group, no Markov projection) or infinitely generated, and the connector step is replaced by trajectory stabilizers of finite index and the sheets by hierarchical trees with summable length cost
  fpbs-soft-collapse-iff-invariant-sparse-spines: that proves the equivalence between spines and soft collapse families and builds spines over a surjection onto Z with finitely generated kernel; this supplies spines on new classes and uses Theorem A only for the corollary
  fpbs-kazhdan-sparse-spines: that asks for factor-of-iid spines, which would give fixed price one; the spines here are invariant but not factors of iid
---

**ESTABLISHED (class-killing obstruction, extension to new classes).** Proof in
`fpbs-commensurated-subgroup-sparse-spines-proof`. Terminology (invariant
sparse spines; soft collapse family (S1)--(S4)) is that of
`fpbs-soft-collapse-iff-invariant-sparse-spines`.

Let `Gamma` be finitely generated, `S` a finite symmetric generating set,
`|.|_S` the word length, and `H <= Gamma` a subgroup that is

* infinite, of infinite index, and
* **commensurated**: `H ∩ gHg^{-1}` has finite index in `H` for every `g`.

Say `H` has a **summable sheet tree** if either

* (T1) `H` is finitely generated, or
* (T2) `H = union_k H_k` for finite subgroups `{e} = H_0 < H_1 < ...`, and
  there are finite sets `T_k subset H_k` with `H_k = <H_{k-1}, T_k>` and
  `sum_k (1 + max_{t in T_k} |t|_S) / |H_{k-1}| < infinity`.

**Theorem.** If `H` is infinite, of infinite index, commensurated and has a
summable sheet tree, then `Cay(Gamma,S)` has invariant sparse spines. For
every `eps, eta in (0,1]` the constructed spine has density at most
`(1 + K + eta) eps`, where `K = sum_j (|v_j| + 1)` over fixed words `v_j`
for a finite generating set of `H` in case (T1), and `K = sum_k (1 + max_{T_k} |t|_S)/|H_{k-1}|` in case (T2).

**Corollary (obstruction).** If moreover `Gamma` is nonamenable, every Cayley
graph of `Gamma` carries a soft collapse family (Theorem A of
`fpbs-soft-collapse-iff-invariant-sparse-spines`). No argument whose only
inputs are Bernoulli facts at `p <= p_c` plus invariance, ergodicity,
insertion tolerance, monotonicity, uniqueness above `p_c` and continuity of
`theta` can prove `p_c < p_u` on these graphs. Members:

* `BS(m,n) = <a,t | t a^m t^{-1} = a^n>` with `|m|,|n| >= 2`: `H = <a>` is
  commensurated, since `t<a^m>t^{-1} = <a^n>`. This settles the named test case
  `BS(2,3)` of `fpbs-soft-collapse-on-fg-normal-and-kazhdan-groups`, whose
  infinite normal subgroups are all infinitely generated.
* every lamplighter `A wr Q = (⊕_Q A) ⋊ Q` with `A` finite nontrivial and `Q`
  finitely generated nonamenable, through (T2) with `H_k = ⊕_{B_Q(k-1)} A`. This
  settles the named test case `Z/2 wr F_2`.
* every fundamental group of a finite graph of finitely generated groups whose
  edge groups have finite index in the adjacent vertex groups, with infinite
  vertex groups, infinite index and nonamenable (for example
  `F_2 *_C F_2` with `C` of finite index in both factors): a vertex group is
  commensurated.
* every group of `fpbs-soft-collapse-on-fg-normal-and-kazhdan-groups`
  Theorem 1 (normal subgroups are commensurated), with a shorter connector
  argument.

**What remains for soft arguments.** Of the four named test cases, only the
single torsion Tarski monster and `B(m,n)` survive, together with groups
without an infinite commensurated subgroup of infinite index that has a
summable sheet tree and without (T).

**Calibration.**

* `F_2`: invariant sparse spines of density `eps` give a free p.m.p. action
  (spine times Bernoulli) of cost at most `1 + eps |S|/2` (proof, Section 5).
  So `F_2`, of cost `2`, has no such `H`, as must hold: its infinite
  commensurated subgroups have finite index.
* Consequence to cross-check against the literature: every group with such
  an `H` has cost one, hence `beta_1^{(2)}(Gamma) = 0`, consistent with
  Gaboriau for `BS(m,n)` and for groups with an infinite amenable normal
  subgroup.

Paradigm answers (inverter lane of `fpbs-benjamini-schramm-counterexample-exists`):

* **Why this works where the normal-subgroup construction stops.** For a
  commensurated `H` the right random walk has no Markov projection to
  `Gamma/H`, but the trajectory `x w_i H` of a fixed word from `x in x_0 H` is
  constant on the finite-index subgroup `x_0 (H ∩ ∩_i w_i H w_i^{-1})`, which
  is all Borel--Cantelli needs. For infinitely generated `H` the sheet cannot
  be joined by bounded words; a hierarchical spanning tree of finite subgroups
  with summable length cost replaces them.
* **First falsifiable step.** The trajectory identity `x_0 h w_i H = x_0 w_i H`
  for `h` in the intersection, checked by hand on `BS(2,3)`.
