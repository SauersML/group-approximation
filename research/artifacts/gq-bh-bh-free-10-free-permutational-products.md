# Free permutational products and finite-edge amalgams in the permutational Boone–Higman class

Lane bh-free-10, 2026-09-18. Lane proofs, not reviewed; no priority claimed. Nodes:
- `free-permutational-products-preserve-pbh` (claim) and its route
  `free-permutational-products-preserve-pbh-proof`;
- `pbh-wreath-closure-fails-over-undecidable-stabilizers` (claim, ESTABLISHED), which
  refutes `pbh-closed-under-permutational-wreaths-with-infinite-stabilizers` as stated;
- `pbh-closed-under-decidable-permutational-wreaths` (claim, OPEN), the corrected form.

## 1. The problem this answers

BFFHZ (arXiv:2503.21882v2, TeX l.457–458) point out that the permutational
Boone–Higman class `B_A` cannot be closed under general amalgams: the word problem of
an amalgam involves membership in the amalgamated subgroup. The class on main already
had several closures:
- free products (BFFHZ Cor. F);
- graph products and retract amalgams `X *_C (C × K)` with `C` a retract of `X`
  (`pbh-class-closed-under-graph-products`);
- common-retract amalgams;
- lamp wreaths over sets with finite stabilizers.

All the amalgam results need retractions. The simplest decidable case without them is
amalgamation over a finite subgroup, for example the centralizing HNN extension of
Thompson's `V` over an involution, or a double `V *_F V` over a finite `F`. `V` is
simple, so no retraction exists. `V` has no finite quotients, so the usual
finite-index argument for virtually free constructions fails too.

## 2. The construction

In the relative automorphism actor `Ω = Aut_M(M * F(x, y))` there are two families:
- transvections `ρ_a` (`x -> x a`), a copy of `M * <y>`;
- twisted conjugations `γ_m` (`x -> x m`, `y -> m^(-1) y m`), a copy of `M`.

`γ_m` normalizes the transvections: it acts on them by `σ_m`, which is conjugation by
`m` on `M` and fixes `y`.

For a free permutational product `(*_X K) ⋊ W`, the factor at `x` must go to a copy of
`K` on which the stabilizer `W_x` acts trivially under `σ`. The copies over different
points must also be free. The idea is to conjugate `K` by an element `g_x` that is
`σ(W_x)`-invariant and that knows which point it sits over.

A lamp does exactly this. In `Z/2 wr_X W` the lamp `δ_x` commutes with `W_x`, and its
centralizer in `W` is exactly `W_x`. With `g_x = y δ_x y`, the conjugates
`g_x K g_x^(-1)` are permuted by `σ(W)` like the points of `X`. Their products are
reduced words in `M * <y>`. The `y`-letters separate `K`-letters from the nontrivial
lamp products `δ_x δ_x'`. So the copies are free.

Everything is placed in one finitely presented simple MIF envelope `M` of
`(Z/2 wr_X W) × K` (BFFHZ Theorem C). So the only input about `X` is that this lamp
wreath lies in `B_A`. That is main's theorem when stabilizers are finite.

Amalgams and HNN extensions then follow by Britton's lemma:
- `X *_C Y <= M *_C (C × <t>)` through `y -> t y t^(-1)`, once `X` and `Y` share `C`
  inside some `M ∈ B_A`;
- `W *_θ <= M *_(C_2) (C_2 × <u>)` through `t -> u s`, once `θ` is conjugation by
  `s ∈ M`.

## 3. The side finding: wreath closure over arbitrary G-sets is false

The route above reduces centralizing amalgams over any subgroup `C` to the
lamplighter `Z/2 wr_(W/C) W`. This makes a gap in the open node
`pbh-closed-under-permutational-wreaths-with-infinite-stabilizers` visible: the
lamplighter's word problem decides membership in `C`, because
`δ_(gC) δ_C = 1` iff `g ∈ C`. Mihailova's subgroup of `F_2 × F_2` then gives a
finitely generated wreath product of two `B_A`-groups over a one-orbit set that has
unsolvable word problem. So the node's statement, "for every countable G-set", is
false. It is marked refuted, and the corrected statement with decidable stabilizers
is a new OPEN node.

## 4. What is left

- **The conjugacy step.** Given finite subgroups of `B_A`-groups and an isomorphism,
  identify them inside a common `B_A`-overgroup. That would make `B_A` closed under all
  finite graphs of groups with finite edge groups. It is automatic for doubles and for
  centralizing extensions, and for residually finite factors via finite-index closure.
  In `V`, cone-restriction self-embeddings change the fixed-point structure of finite
  subgroups. That suggests hosts with enough "local copies" satisfy it, but nothing is
  proved.
- **Decidable infinite stabilizers.** By Part 1, `pbh-closed-under-decidable-permutational-wreaths`
  would give centralizing HNN extensions and doubles over every subgroup with decidable
  membership. That is the permutational form of the centralizing case of the open
  `bh-embeddability-survives-decidable-edge-hnn`.
