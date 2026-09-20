---
rg: 2
id: lebesgue-preserving-subgroup-of-2v-is-the-turing-machine-group
kind: claim
title: "The Lebesgue-preserving subgroup M_2 of 2V is, under the baker's-map coding, exactly the moving-tape group RTM_fix(2,1) of reversible binary Turing machines; so the Callard--Salo distortion element lies in the Jacobian kernel, M_n admits no proper commensurating action, and the cubical kill switches on strictly between the full-shift group [[X]] (no distortion) and M_2"
distinct_from:
  nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal: that describes Φ M_2 Φ^{-1} as the full group of the homoclinic-plus-shift groupoid and leaves open whether the Callard--Salo element can be put into M_2; this identifies the same group with the Turing-machine group RTM(2,1), which puts a polylog-distorted element in M_2 and settles that question
  brin-thompson-mv-contains-a-distortion-element: that places a distortion element somewhere in mV; this places one in the measure-preserving subgroup M_2 (Jacobian kernel), which the mV statement does not locate
  cubical-coset-proper-actions-capture-distorted-elements: that is the abstract bounded-or-linear and capture lemma; this applies it to M_n and to the M_n half of the Jacobian split, where no distortion element was known
  heisenberg-not-in-wobbling-groups-of-quadratic-growth-graphs: that excludes sublinearly distorted elements from wobbling groups of linear growth; this uses it to show the new kill does not descend from M_2 to [[X]]
  full-shift-full-group-kazhdan-subgroups-are-finite: that is a (T)-type restriction on [[X]]; this is a cubical-type restriction on the overgroup M_2 and a proof that it does not reach [[X]]
---

**ESTABLISHED** by `lebesgue-preserving-2v-turing-machine-proof`.

## Setting

As in `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`:
- `C = {0,1}^ω`; `nV` acts on `C^n` by prefix replacements on finite brick partitions;
  `c : nV → C(C^n, Z^n)` is the exponent cocycle, `J = c_1 + … + c_n` the log-Jacobian;
- `M_n = {g : J(g) ≡ 0}`, which is the subgroup preserving the Lebesgue (Haar) measure `λ`
  (item 3(a) there);
- `X = {0,1}^Z` with shift `σ`, `[[X]]` its topological full group, and
  `Φ : C^2 → X`, `Φ(a, b) = … b_1 b_0 . a_0 a_1 …`.

`RTM_fix(2, 1)` is the moving-tape group of reversible Turing machines with one state on the
binary tape: homeomorphisms `f` of `X` with a radius `r` and a local rule `(u, v) ↦ (u', v')`,
`|u| = |v| = r`, `|u'| + |v'| = 2r`, such that `f(xu.vy) = xu'.v'y`
(`turing-machine-groups-contain-distortion-elements`, item 1). It is canonically isomorphic to the
Barbieri–Kari–Salo group `RTM(2, 1)`.

A *commensurating action* of a group `G` is an action on a set with a subset `A` such that
`ℓ(g) = |gA Δ A|` is finite for all `g`; this covers actions on CAT(0) cube complexes and wall
spaces. An element `f` of infinite order is *distorted* if `|f^N|_L = o(N)` in some finitely
generated subgroup `L ∋ f`.

## Statement

1. **(Identification.)** `Φ M_2 Φ^{-1} = RTM_fix(2, 1)` as groups of homeomorphisms of `X`. So
   `M_2 ≅ RTM(2, 1)`. The two descriptions of the same group agree on measure: `M_2` is the
   `λ`-preserving subgroup of `2V`, and Barbieri–Kari–Salo prove that a moving-tape machine is
   reversible iff it preserves the uniform Bernoulli measure, which is `Φ_* λ`.
2. **(Distortion in the Jacobian kernel.)** There are a finite set `F ⊂ M_2` and an element
   `f ∈ ⟨F⟩` of infinite order with `|f^N|_F = O(log^4 N)`. For every `n ≥ 2`,
   `f × id^{n−2} ∈ M_n` is distorted in the same way.
3. **(No proper commensurating action of the Jacobian kernel.)** Let `n ≥ 2`.
   - (a) No commensurating action of `M_n` has a proper function `ℓ`. In particular `M_n`, and
     `RTM(2, 1)`, act properly on no CAT(0) cube complex.
   - (b) For every subgroup `H ≤ nV`, if a commensurating action of `nV` has `ℓ` proper modulo
     `H`, then `(f × id)^d ∈ H` for some `d ≥ 1`.
   - (c) So the half "some cnd function on `nV` is proper on `M_n`" of item 5 of
     `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal` has no cubical witness: a wall count
     `ℓ` of `nV` that is proper on `M_n` restricts to a proper wall count of `M_n`, which (a)
     excludes. The same holds for the prerequisite "`M_2` is Haagerup".
4. **(The kill does not descend to the full-shift group.)** `[[X]] ≤ M_2` (item 3(c) of
   `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`), but `[[X]]` has no distorted element:
   if `L ≤ [[X]]` is finitely generated and `g ∈ L` has `|g^N|_L = o(N)`, then `g` has finite
   order. So the obstruction of item 3 (sublinear growth along a
   distorted cyclic subgroup, followed by the Haglund–Cornulier bounded-or-linear dichotomy)
   says nothing about `full-shift-topological-full-group-is-a-t-menable`. It switches on exactly
   when the machine may overwrite the tape: `[[X]]` is the subgroup of `RTM_fix(2, 1)` whose local
   rules only shift, with `(u', v')` a re-cut of the word `uv`.

## Where the cubical class now stands on the Jacobian/diagonal splits

The four halves of items 4 and 5 of `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`:

| half | cubical witness possible? | reason |
|---|---|---|
| (Q_J) proper modulo `M_n` | no | fibre element `z`, item 6(a) there |
| (Q_D) proper modulo `D` | no | fibre element `z`, item 6(a) there |
| proper on `M_n` | **no (new)** | item 3(c) here: Callard–Salo element inside `M_2` |
| proper on `D ≅ V_{2^n,1}` | not excluded | no distortion element of `nV` is known inside `D` |

So of the two splits "`nV` Haagerup ⟺ (Q_J) ∧ proper on `M_n`" and "⟺ (Q_D) ∧ proper on `D`",
the first is non-cubical in both halves. Only the "proper on `D`" half, where Farley-type counts
on the Higman–Thompson group live, survives this class kill, and its partner (Q_D) is non-cubical.

## Consequences

- **The question left open in `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`** ("whether
  the Callard–Salo distortion element of 2V can be conjugated into `M_2` is not checked") is
  settled: a polylog-distorted element lies in `M_2`, with Jacobian `0`. By item 1 the natural
  source of such elements is the Turing-machine picture itself. The identification is exact, so
  every element Callard–Salo build in `RTM(2, 1)` is in `M_2`.
- **A sharper necessary prerequisite.** The goal implies that `RTM(2, 1) ≅ M_2` is Haagerup
  (`reversible-turing-machine-groups-are-a-t-menable`, OPEN). That implies
  `full-shift-topological-full-group-is-a-t-menable` via
  `full-shift-full-group-a-t-menable-from-turing-machines`. The chain
  `[[X]] ≤ RTM(2, 1) = M_2 ≤ 2V` separates the two known class kills. Distortion (cubical
  methods) dies at `RTM(2, 1)` and not at `[[X]]`. The gap-class kill of
  `nv-gap-class-cocycles-are-coboundaries` runs through brick-local copies of `V`, which `M_n`
  lacks (item 6(c) of `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`), so it reaches neither.
- **What a proof for `[[X]]` may still use.** Commensurating actions of `[[X]]` are not excluded
  by distortion (item 4). A proper one cannot be the restriction of a proper commensurating action
  of `M_2` (item 3(a)). The restriction of a non-proper action of `M_2` is not excluded. Neither
  is an action of `[[X]]` that does not extend to `M_2`.
- **Precise statement of the kill (class, invariant, death step).** Class: cnd functions on `M_n`
  (or on `nV`, tested on `M_n`) of the form `ℓ(g) = |gA Δ A|`. Invariant: the sublinear word
  growth `|f^N| = O(log^4 N)` of the Callard–Salo element `f ∈ M_2`. Death step: item 1 of
  `cubical-coset-proper-actions-capture-distorted-elements` gives `ℓ(f^N) = mN + O(1)`, and
  `ℓ ≤ C|·|_F` forces `m = 0`. So `ℓ` is bounded on `⟨f⟩`, an infinite subgroup of `M_n`.
