---
rg: 2
id: spine-hosts-reduce-to-fp-rf-overgroups-of-the-lamp
kind: claim
title: Germ groups at stable rays are the loop subgroups, so every lift-presented automaton group has finitely presented loop subgroups; a separated automaton group is LP-embeddable once its base lies in a finitely presented subgroup of a lift-presented automaton group, and for spine groups every same-tree lift-presented overgroup forces this
distinct_from:
  separated-automata-reduce-bh-to-fp-overgroups-of-the-base: that needs the base inside a finitely presented automaton group; this needs only a finitely presented subgroup of an automaton group whose action is lift-presented (which need not be finitely presented), and shows that condition is forced for spine groups.
  nekrashevych-fp-iff-cycle-germ-groups-fp: that computes germ groups as a groupoid quotient; this identifies them with subgroups of the automaton group itself.
---

**ESTABLISHED** (lane proof below, elementary; no priority claimed; not yet refereed).

## Statement

1. **Loop subgroups are germ groups.** Let `G = ⟨S⟩` be an automaton group and `y` a letter of a closed family of
   stable letters. Then the germ map is an isomorphism
   `L_y = {g in G : g(y) = y, g|_y = g} -> G_(y^ω)`.
   So if `G`'s action is lift-presented, every such `L_y` is finitely presented
   (`nekrashevych-fp-iff-cycle-germ-groups-fp`, necessity). In particular this holds for every finitely presented
   automaton group, and `L_y` is residually finite.
2. **Weaker sufficient condition.** Let `G` be separated over a base `B`
   (`separated-automata-reduce-bh-to-fp-overgroups-of-the-base`). Suppose `B <= K <= P`, where `K` is finitely
   presented and `P` is an automaton group whose action is lift-presented. `P` need not be finitely presented;
   for example `P` could be contracting. Then `G` is LP-embeddable, hence Boone–Higman.
3. **Necessity for spine groups.** Suppose `G <= G^+`, where `G^+` is an automaton group acting on the same tree
   and extending `G`'s action. Suppose also that a spine letter `z` is stable for `G^+` in a closed family, and
   that `G^+`'s action is lift-presented. Then `L_z(G) <= L_z(G^+)`, which is finitely presented. For the
   spine-Grigorchuk group, `L_2(G) = ⟨ŝ_γ⟩ ≅ Γ`. So such an overgroup exists only if `Γ` lies in a finitely
   presented subgroup of a lift-presented automaton group, and by 2 that condition then makes `G` LP-embeddable.

## Consequence: the real barrier

By 3, every self-similar route of this kind needs `Γ` inside a **finitely presented residually finite group**. No
such group is recorded on main, and none is known to this lane. Neither a finitely presented residually finite
group with an infinite finitely generated torsion subgroup, nor one containing the Grigorchuk group, is known
here. `rf-hosts-cannot-realize-branch-substitutions` shows the known finite presentation mechanism cannot be used.
The open input is sharpened to `grigorchuk-group-embeds-in-fp-residually-finite-group`, together with its
automaton-embedded form in 2.

## Proof

**1.** By (Φ5) of `nekrashevych-fp-iff-cycle-germ-groups-fp-proof`, every germ at `y^ω` is the germ of some
`ŵ(p) in L_y`. Now let `g in L_y` have trivial germ. Then `g` is trivial on some `y^k X^*`, and `g|_{y^k} = g`,
so `g = 1`. Hence the germ map is injective on `L_y`. Since `L_y` is a group, the image is all of `G_(y^ω)`.

**2.**
- **Enlarged base.** `B̂ ↪ B ≀ Sym(Y) ↪ K ≀ Sym(Y) ≤ P' := P ≀ Sym(Y)`. `P'` is the automaton group of
  `lift-presentable-groups-closed-under-products-and-wreaths` (proof of 1, with `Δ = ∏ ι_j`), and its action is
  lift-presented by item 1 there.
- **Adding states keeps lift-presentation.** Suppose `S ⊆ S''` are finite, section-closed and generate the same
  group, and put `M = ⟨⟨R ∪ {s''^{-1} u_{s''}}⟩⟩_lift` in `F(S'')`, where `u_{s''}` is a word in `S` for `s''`.
  - The retraction `s'' ↦ u_{s''}` sends every relator to a relator in `F(S)`.
  - `M ∩ F(S)` is a lift ideal of `F(S)` containing `R`.
  - Hence `N_{S''} = M`, and adding finitely many states of `P'` keeps its action lift-presented.
- **Germ transplant.** The transplant of `separated-automata-reduce-bh-to-fp-overgroups-of-the-base-proof` §3 puts
  `G` in a separated automaton group over `P'`. Every closed-path element acts on `Y'`-blocks by an element of
  `φ(B̂) ⊆ K' := K ≀ Sym(Y)`. So each germ group embeds in `Sym(Z∖z) × K'`.
- **Saturation.** Add spinal loops at each `z`, with germ data the generators of `Sym(Z∖z) × K'`. Their sections
  lie in `P'`; add these as states. Then every germ group equals `Sym(Z∖z) × K'`, which is finitely presented.
- **Conclusion.** The separated criterion (§1 there) needs only a lift-presented base and finitely presented germ
  groups. So the enlarged group is lift-presented.

**3.** Elements of `L_z(G)` fix `z` and equal their section at `z` in the common action, so they lie in `L_z(G^+)`.
That group is finitely presented by 1. For the spine group, `L_2(G) ⊇ ⟨ŝ_γ⟩ ≅ Γ`. It is all of it by the germ
computation in `nekrashevych-fp-iff-cycle-germ-groups-fp`, consequence 2. ∎

## Lesson for general BH

For automaton groups with a spine, self-similar Boone–Higman hosts exist in the lift-presented sense exactly when
the lamp group sits in a finitely presented subgroup of some lift-presented automaton group. This is up to the
same-tree caveat in 3. So the self-similar programme for subexponential automata meets a classical problem: can
a finitely presented residually finite group contain a given infinite finitely generated torsion (branch) group?
