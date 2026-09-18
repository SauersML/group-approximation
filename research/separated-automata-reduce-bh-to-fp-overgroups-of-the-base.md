---
rg: 2
id: separated-automata-reduce-bh-to-fp-overgroups-of-the-base
kind: claim
title: A separated automaton group, with loops on private letters over a base acting on the other letters, is Boone–Higman as soon as its base embeds in a finitely presented automaton group, because its isomorphism type sees the base only abstractly and its cycle germs can be saturated to (base wr finite) x finite
distinct_from:
  spine-mover-automata-over-fp-bases-are-lift-presented: that is one separated automaton (spine plus odometer mover) over a finitely presented base acting on the same tree; this covers every separated automaton, and needs only an abstract embedding of the base into some finitely presented automaton group.
  nekrashevych-fp-iff-cycle-germ-groups-fp: that is the germ criterion under (P1); here the base may have any activity, and the germ groups are made finitely presented by saturation instead of assumed.
  decidable-fg-self-similar-groups-embed-in-fp-self-similar: that asks for finitely presented self-similar overgroups of all decidable self-similar groups; this needs them only for the bases of separated automata, which are simpler than the automaton groups built on them.
---

**ESTABLISHED** by `separated-automata-reduce-bh-to-fp-overgroups-of-the-base-proof` (lane proof, elementary; no
priority claimed; not yet refereed).

## Separated automata

`X = Y ⊔ Z` and `S = S_B ⊔ L`, both finite and closed under inverses, such that:
- **Base.** `S_B` is closed under sections. Each `b in S_B` preserves `Y` and fixes every `z in Z` with trivial
  section, so `B = ⟨S_B⟩` acts only on maximal `Y`-blocks.
- **Loops.** Each `t in L` preserves `Y` and `Z` and has a loop letter `ℓ(t) in Z` with `t|_{ℓ(t)} = t`. Its
  other sections are `t|_z = 1` for `z in Z ∖ {ℓ(t)}` and `t|_y in S_B ∪ {1}` for `y in Y`.

`G = ⟨S⟩`. The germ-data group is `B̂ = ⟨B, q_t : t in L⟩ <= Aut(Y^*)`, where `q_t(y v) = t(y) · t|_y(v)`.
Examples:
- spine-Grigorchuk (`Y = {0,1}`, `Z = {2}`);
- every `M(P)` of `spine-mover-automata-over-fp-bases-are-lift-presented` (`Z = {2,3}`).

## Statement

1. **Separated criterion.** If `B`'s action on `Y^*` is lift-presented and the germ groups `G_(z^ω)`, `z in Z`, are
   finitely presented, then `G`'s action is lift-presented. Conversely, a lift-presented `G` has fp germ
   groups at every `z^ω` (`nekrashevych-fp-iff-cycle-germ-groups-fp`, necessity).
2. **Germ saturation.** Each `G_(z^ω)` embeds in `Q_z = (B ≀ Sym(Y)) × Sym(Z ∖ {z})`. If `B` is finitely presented,
   adding finitely many spinal loop states at each `z` gives a separated automaton group `G^+ ⊇ G` with
   `G^+_(z^ω) = Q_z`, finitely presented, so `G^+` is lift-presented.
3. **Germ transplant.** `G` embeds in the unrestricted permutational wreath product `B̂^{Z^*} ⋊ H`, where `H` is
   the Z-part of the loops, by elements defined from `B̂` as an abstract group. So if `φ: B̂ ↪ P` for a finitely
   presented automaton group `P`, then `G` is isomorphic to a subgroup of a separated automaton group over `P`.
4. **Reduction.** `B̂ ↪ B ≀ Sym(Y)`, and `P ≀ Sym(Y)` is a finitely presented automaton group whenever `P` is
   (`lift-presentable-groups-closed-under-products-and-wreaths`, proof of 1). Hence:

> **If the base `B` embeds in a finitely presented automaton group, then `G` is LP-embeddable, so `V`-type
> finitely presented simple hosts contain it and `G` satisfies Boone–Higman.**

## Consequences

- **All test cases hinge on one statement.** The spine-Grigorchuk group, the spine-mover group `M(Γ)`, and every
  separated automaton over the Grigorchuk base are Boone–Higman if **the Grigorchuk group embeds in a finitely
  presented automaton group**. Their own actions have non-fp Nekrashevych groups
  (`nekrashevych-fp-iff-cycle-germ-groups-fp`).
- The known fp overgroup of `Γ` does not help. Grigorchuk's ascending HNN extension is finitely presented but not
  residually finite (Sapir–Wise, J. Pure Appl. Algebra 166 (2002); Grigorchuk), so it is in no self-similar group.
- **Degree drops.** For a separated automaton of activity degree `m` the base has degree `<= m - 1`. For linear
  separated automata the base is bounded, so the needed input is
  `bounded-automaton-groups-embed-in-fp-automaton-groups`.

## Lesson for general BH

For separated automata the base is invisible except as an abstract group: germ transplant lets any faithful
action of it replace the given one. Germ saturation then makes every cycle germ group `(base ≀ finite) × finite`.
So the only obstruction to a self-similar Boone–Higman host is a finitely presented automaton overgroup of the
base, which sits one activity degree lower. BH through self-similar hosts is thereby pushed down to bounded
(contracting) automaton groups, where it is a single question about the self-similar Higman embedding.
