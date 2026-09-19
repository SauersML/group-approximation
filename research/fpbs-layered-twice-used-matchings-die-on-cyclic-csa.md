---
rg: 2
id: fpbs-layered-twice-used-matchings-die-on-cyclic-csa
kind: claim
title: Layered twice-used-letter Morse matchings have mass at most |S| - 2 on every non-cyclic torsion-free group with cyclic malnormal maximal abelian subgroups, so on hyperbolic groups with vanishing first l2 Betti number they stay a full unit short at every generating set and word list
artifacts:
  - research/artifacts/fpbs-layered-twice-used-letter-towers-2026-09-18.md
distinct_from:
  fpbs-one-relator-twice-used-letter-fixed-price: that constructs a one-layer twice-used-letter matching reaching the ceiling for one-relator groups; this bounds every layered iteration of that construction over any generating set and list, and shows it can never reach z when beta_1 = 0 on cyclic-CSA groups
  fpbs-single-letter-morse-matchings-die-on-bernoulli: that kills letters used k >= 3 times via a Kesten gap on Bernoulli; this kills letters used exactly twice (where Lambda_s is cyclic and the gap argument is silent) by a group-theoretic tower count valid on every free p.m.p. action
  fpbs-letter-saturated-morse-matchings-die-on-bernoulli: that caps per-(type, letter) shares from a spectral gap; this is a global mass bound for the acyclic twice-used class, with no spectral input
  fpbs-amenable-edge-towers-reach-only-class-t: that bounds what amenable-edge graph-of-groups towers reach; this bounds Cayley cell matchings whose letter layers form root-commensuration towers over a cyclic group
  fpbs-morse-deficit-vanishes-for-full-presentations: that is the open vanishing claim over all matchings; this is a lower bound on one class of matchings, uniform over all word lists P_L
---

**ESTABLISHED (written deduction).** Proof in `fpbs-layered-twice-used-matchings-die-on-cyclic-csa-proof`.

**Class (LTU).** A Morse matching `M` (conditions M1–M2 of `fpbs-bernoulli-morse-collapse-criterion`; M3 is not
needed) is *layered twice-used* if:
- the active letters (those matched on positive measure) carry a total order;
- every matched cell whose matched edge has letter `s` contains `s` exactly twice;
- every other letter of that cell is an unmatched letter or an active letter later than `s`.

The class contains:
- the dual-forest matching of `fpbs-one-relator-twice-used-letter-fixed-price`;
- the commuting-direction chains;
- all Magnus/Tietze iterations of these, over any generating set `S` and any list, including `P_L`.

**Theorem.** Let `Gamma` be *cyclic-CSA* (torsion-free, with every maximal abelian subgroup cyclic and malnormal)
and not cyclic. Then every LTU matching on every free p.m.p. action, for every finite `S` and every list `R`, has
`mu(M) <= |S| - 2`.

On Bernoulli:
- the LTU deficit is `>= 1 - beta_1^(2)(Gamma)`;
- the Theorem A certificate is `C <= |S| - mu(M)`, which is always `>= 2`.

**General tower lemma (any group).** Suppose an LTU matching has more than `|S| - 2` mass. Then at most one letter
`t` is unmatched, and `Gamma` is built from `<t>` by adjoining the active letters one at a time. Each step is either
- a nontrivial commensuration: `s u s^{-1} ∈ H` for some `u ∈ H \ {1}`; or
- a nontrivial root: some `g ∈ sH \ {1}` has `g^2 ∈ H`.

**Class killed.** Twice-used-letter matchings whose letter dependency is acyclic.
- *Invariant:* the maximal cyclic subgroup `C(t)`. It is closed under nontrivial commensuration (malnormality) and
  under square roots (uniqueness of the maximal abelian subgroup).
- *Step where it dies:* the bottom layer. The last active letter must root-commensurate `<U>`, and each higher
  layer is then forced into `C(t)`.

**Changes belief.** This covers every torsion-free hyperbolic group with `beta_1^(2) = 0`, for example:
- closed hyperbolic 3-manifold groups, which have fixed price `1` by Agol and Gaboriau;
- torsion-free lattices in `Sp(n,1)`.

For these groups the only positive mechanism the node has, the twice-used dual forest together with its layered and
Tietze iterations, stays a full unit of mass short. This holds at every generating set and every `L`.

Any proof of the node on these groups must therefore use, on positive measure, either
- a matched letter used `>= 3` times in its cell, which is spectrally capped by the w8/w9 theorems; or
- a cyclic letter dependency, the balanced multi-letter regime.

**Calibration.**
- Two-generator one-relator groups with a twice-used letter are Baumslag–Solitar groups or have nontrivial centre,
  so they are never non-cyclic cyclic-CSA. This is consistent with the positive theorem there.
- For `beta_1 >= 1` (surfaces, one-relator groups on at least 3 generators) the bound is vacuous, as it must be.
