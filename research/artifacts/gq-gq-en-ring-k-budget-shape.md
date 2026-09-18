# The UHF K-budget as ring conditions (lane gq-en-ring, 2026-09-17, round 3)

Target, from `gq-deep-adelic-1-k-budget.md`: a finitely generated (ideally finitely presented)
simple ring `R ⊇ Q` satisfying
- **(K1)** `ker(Q^x -> K_1(R))` is finitely generated;
- **(K2)** the symbols `{λ, x}` (`λ ∈ Q^x`, `x ∈ R^x`) generate a finitely generated subgroup
  of `K_2(R)`;

or a proof that none exists.

**Outcome of this round: neither.** It lands two ring conditions that pin down the shape, and
one corollary that removes every skew Laurent ring.

## 1. Landed

| Node | Status | Content |
|---|---|---|
| `rational-k1-detection-forces-infinite-order-unit-class` | ESTABLISHED (lane) | (K1) ⇒ `[1_R]` has infinite order in `K_0`, so `R^s ≇ R^(s+t)` for all `s, t` |
| `matricial-divisibility-kills-rational-k2-symbols` | ESTABLISHED (lane; textbook inputs: Tate, additivity) | if `R ≅ M_n(R_n)` for `n` divisible by every integer, then `K_2(Q) -> K_2(R)` is `0` |

So the budget wants `[1]` of infinite order and matricially divisible by every integer, as in
`U_Q`.

## 2. Corollary: no skew Laurent ring meets (K1) and (K2)

Let `R = B[u^±1; σ] ⊇ Q`, with `B ⊇ Q` and `σ` fixing `Q`. The map `Q^x -> K_1(R)` factors
through `K_1(B)`. So `ker(Q^x -> K_1(B)) ⊆ ker(Q^x -> K_1(R))`.
- If `R` satisfies (K1), the smaller kernel is finitely generated. The image of `Q^x` in
  `K_1(B)` is then `Q^x` modulo a finitely generated group, which is not finitely generated.
- That is the hypothesis of `laurent-rational-symbols-block-fp-elementary-groups`. So `R` fails
  (K2), and no `E_N(R)` is finitely presented.

Every crossed product by `Z` over a base containing `Q` is therefore out: tracial harmonic
rings, subshift and odometer crossed products with a harmonic element, and endomorphism
dilations. This relies on the trust surface T1 of that node.

## 3. What a host has to look like

`R` finitely generated and simple, with `Q ⊆ R`, satisfying all of the following:
- **Matricial divisibility.** `R ≅ M_n(R_n)` for a cofinal set of `n`. This handles the
  rational part of (K2).
- **Non-torsion unit.** `[1]` of infinite order. This is forced by (K1).
- **No index-type units.** No unit `x` whose symbols `{λ, x}` are infinitely generated.

Why the known mechanisms fail:
- **Isometric corners.** If `s` is an isometry with `ss* = e`, `ts = 1`, then `[e] = [1]`.
  A halving `R ≅ M_2(eRe)` made this way gives `[1] = 2[1]` (Leavitt, fails (K1)).
- **Endomorphism dilations.** A unital shift endomorphism made invertible is a crossed
  product by `Z`, which fails (K2) by §2.
- **Locally matricial rings, AF groupoid algebras.** These satisfy the budget but are never
  finitely generated.
- **What is left.** The isomorphisms `R ≅ M_n(R_n)` must be non-spatial ring isomorphisms
  that are encoded by finitely many generators and are not implemented by units of index
  type.

**Open question (precise).** Is there a finitely generated ring `R ⊇ Q` with unital ring
isomorphisms `R ≅ M_n(R_n)` for `n` divisible by every integer, `[1]` of infinite order in
`K_0(R)`, and no unit with infinitely generated rational symbols?
- In characteristic `p`, the first two conditions are met by subshift crossed products with a
  full odometer factor (`rational-eigenvalue-iff-subshift-ring-is-matrix-ring`), but only
  through the translation unit.
- A negative answer for finitely generated simple rings would close the ring-host route to
  `gl-n-q-embeds-in-fp-simple-group`. This lane has not proved one.

## 4. Sparks (not pursued)

- **Self-similar algebras with surjective restriction.** A finitely generated ring with a
  unital isomorphism `ψ: R -> M_d(R)` has `R ≅ M_d(R)` as rings. Bartholdi's self-similar
  algebras have `ψ` injective. Rings where `ψ` is also onto, for several coprime `d`, and where
  `[1]` stays of infinite order, would give matricial divisibility with no translation unit.
- **Perfect acting groups** (spark S1 of the budget artifact): `{λ, u_γ} = 1` for a perfect
  `Γ`. Combined with matricial divisibility from rational spectrum, this is the natural
  candidate. The open risk is that the generated ring acquires an index-type unit anyway.
