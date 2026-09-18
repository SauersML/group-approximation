---
rg: 2
id: permutational-host-forms-agree-for-countable-inputs-proof
kind: route
title: Rerun the finitary-alternating host proof with an arbitrary subgroup, and read off the simple host and the kernel gate
target: permutational-host-forms-agree-for-countable-inputs
requires:
  - fp-finitary-alternating-overgroups-have-type-a-actions
  - finitary-symmetric-extensions-of-oligomorphic-actions-are-fp
  - twisted-btb-clopen-action-is-type-a
  - twisted-brin-thompson-finite-presentation-criterion
  - type-a-action-gives-boone-higman-for-subgroups
  - abstract-btb-simple-quotient-fp-gate
---

Notation as in the target. Throughout, `H` is an arbitrary group. The only way
`H` enters is as a subgroup of the host.

**(2 ⇒ 1).** `Γ` is finitely presented with `Alt_fin(X) ≤ Γ ≤ Sym(X)`, `X`
infinite. By `fp-finitary-alternating-overgroups-have-type-a-actions`, item 3,
the action of `Γ` on `X` is of type (A). Since `H ≤ Γ`, `H ∈ B_A`. Items 1 and 2
of that node are statements about `Γ` alone.

**(1 ⇒ 2).** This is Steps 1–5 of `pbh-finitary-alternating-hosts-proof`,
copied with `H` arbitrary.
- `H ≤ Γ_0`, where `Γ_0` acts on `S` with type (A). `S` is countable, because
  `Γ_0` is countable with finitely many orbits on `S`.
- `SV := SV_{Γ_0}` is finitely presented (`twisted-brin-thompson-finite-presentation-criterion`).
  `g ↦ τ_g` embeds `Γ_0` in `SV`, since the action is faithful. So `H ≤ SV`.
- `P := FSym(Ω) ⋊ SV` is finitely presented and acts faithfully on the infinite
  set `Ω` of proper nonempty clopen subsets of `C^S`, with `Alt_fin(Ω) ≤ P`. The
  inputs are `twisted-btb-clopen-action-is-type-a` (items 3 and 4) and
  `finitary-symmetric-extensions-of-oligomorphic-actions-are-fp`.
- So `H ≤ SV ≤ P` witnesses 2. No step refers to generators of `H`.

**(1 ⇒ 3).** With `H ≤ Γ_0 ≤ SV` as above:
- `SV` is simple and finitely presented, since the action of `Γ_0` is faithful
  (`twisted-brin-thompson-finite-presentation-criterion`, last sentence).
- By `twisted-btb-clopen-action-is-type-a`, `SV` acting on `Ω` is of type (A),
  so `SV ∈ B_A`.
- Take `S := SV`.

**(3 ⇒ 1).** `H ≤ S ∈ B_A`, and `B_A` is closed under subgroups by definition.

**Simple envelope.** Under 1, `H ≤ Γ_0`, and Zaremsky's Corollary B
(`type-a-action-gives-boone-higman-for-subgroups`) embeds every subgroup of
`Γ_0` in the finitely presented simple group `SV_{Γ_0}`. Under 3 the envelope is
`S` itself.

**Kernel removal.** Let `G ↷ S` be of type `[A_2]` with kernel `K`, and let
`H ∩ K = 1`.
- `G/K` acts faithfully on `S`. Point stabilizers are
  `Stab_{G/K}(s) = Stab_G(s)/K`, because `K ≤ Stab_G(s)`, so they are
  finitely generated.
- The orbits of `G/K` on two-element subsets are those of `G`. There are
  finitely many of them, since `G` has finitely many orbits on `S^2`.
- `H` maps injectively to `G/K`.
- So if `G/K` is finitely presented, its action is of type (A), and `H ∈ B_A`.
- If `G/K` is not finitely presented, `abstract-btb-simple-quotient-fp-gate`
  says that the simple quotient `SV_{G/K}` of the finitely presented `SV_G` is
  not finitely presented.

**Consequences.**
- The hosts named in the target lie in `B_A` by (3 ⇒ 1).
- The universality sentence is quoted from the survey, which the user supplied
  verbatim.
- For `VA`, the target uses the Remark 3.5 description recorded in
  `bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh`. That is a citation, not
  re-derived here.
