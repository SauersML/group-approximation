---
rg: 2
id: kep-2v-hosts-odometer-roots-review
kind: claim
title: Referee review of 12ec78a007 (bh-glnq-fresh), 2V_H carries Q ⋊ ⟨2⟩ natively iff H ⊇ Z_(2)-translations — items 1–4 PASS; the "not claimed" flag is accurate, and it can be sharpened from the sources, since Li's Example ex:ZS (III) does cover self-similar actions on higher-rank graphs and gives F_n for 2V_H from F_n of H, under right cancellation, (Inv), (F) and effectiveness, while Matui's simple2 gives simplicity of the commutator subgroup under minimality and pure infiniteness, which are inherited from 2V
distinct_from:
  kep-2v-hosts-carry-q-x-2-iff-h-has-odometer-roots: lane node under review here.
---

**ESTABLISHED (referee bh-ref-d, 2026-09-19).** No priority claimed. Read on origin/main:
- the node and its `-proof`;
- the referee artifact for `odometer-2v-is-fp-simple-and-contains-bs12`.

Sources read on MSI (arXiv LaTeX e-prints, `/projects/standard/hsiehph/sauer354/refs/`):
- Li, arXiv:2110.04505v2 (Cor. `intro:ZS`, Example `ex:ZS`);
- Matui, arXiv:1210.5800v3 (Def. `pi`, Thm `simple2`).

## Items 1–4: PASS

- **Item 1.** A centralizer element preserves the `s`-orbit closures `C × {y}`. On each of them it
  commutes with the minimal rotation `τ`, so it is a translation. On a defining rectangle the affine
  identity forces slope `2^(k−k′) = 1`, so `η = τ_(a′)` with `a′ ∈ T_H`. Then `a = p′ − p + 2^k a′ ∈ T_H`.
- **Item 2.** `r^ℓ = s` gives `r` commuting with `s`, so `ℓ a ≡ 1` and `a = 1/ℓ ∈ Z_2` for odd `ℓ`.
- **Item 3.** `u(τ_c × id)u^(−1) = τ_(2c) × id` by `x_0 + 2(x′ + c) = x + 2c`. Conjugates by `u^(−k)` give
  `Z_(2)[1/2] = Q`. The action is faithful on `Q_2`, so `⟨τ_c × id, u⟩ ≅ Q ⋊ ⟨2⟩`.
- **Item 4.** Subgroups of the profinite `Aut(T_2)` are residually finite, so a finitely presented `H` with
  `T_H ⊇ Z_(2)` is a finitely presented residually finite group containing `Z_(2)`. That route does not
  pass through `2V_H` at all.
- **The `V_2(H)` remark.** `τ²` has two orbit closures on `Z_2`, so it is not conjugate to the minimal `τ`.
  The remark holds.

## The "Not claimed" flag: accurate, and sharper than stated

**Li covers the 2D KEP groups.**
- Li's Example `ex:ZS` (III) treats `P = Z_(≥0)^k` with at least 2 edges of each colour at each vertex.
  Li states that (III) "also covers … self-similar actions on higher rank graphs as in [LY, ABRW]".
- The conclusion, via Cor. `intro:ZS`: the full group of `I_l(𝔇) ⋉ ∂Ω_𝔇`, with `𝔇 = 𝔆 ⋈ 𝔊`, "is of type
  F_n if `𝔇^*(𝔴, 𝔴)` is of type F_n".
- Hypotheses:
  - (Inv);
  - "`𝔇` is right cancellative up to `=^*`";
  - (St), (LCM) and (`t < d`) for `𝔆`, which hold for the product 2-graph as in the `⟨τ⟩` case;
  - (F), which Li notes "is related to faithfulness of the action".
- By Li's Remark `rem:ZS-Stab`, `𝔇^*(v, v) = St(H, v)`, which is `H` for the one-vertex 2-graph.
- **Consequence.** A finitely presented (`F_2`) `H` gives a finitely presented `2V_H`, provided the
  following hold:
  - right cancellation up to `=^*`, the pseudo-freeness-type condition;
  - (Inv) and (F);
  - effectiveness, which is needed to identify Li's full group with the concrete group `2V_H`.
  These are exactly the checks gq-referee-a made for `H = ⟨τ⟩`. For a non-finite-state, non-contracting
  `H` they are real conditions.
- So "the hypotheses need re-checking" is accurate. The framework applies, and the missing inputs are
  those four conditions plus `F_2` of `H`.

**Matui's simplicity theorem.**
- `simple2` states: "Suppose that G is purely infinite and minimal. Then any non-trivial subgroup of
  [[G]] normalized by the commutator subgroup D([[G]]) contains D([[G]]). In particular, D([[G]]) is
  simple."
- The standing setting is that of Hausdorff, effective ample groupoids, per the earlier referee's checks.
- Minimality and pure infiniteness are inherited, because `2V ≤ 2V_H` already moves and halves every
  cylinder.
- So `D(2V_H)` is simple once the groupoid is Hausdorff and effective. Simplicity of `2V_H` itself also
  needs `2V_H` to be perfect. For `⟨τ⟩` that followed from explicit relations, and for general `H` the
  abelianization of `H` may contribute.
- **Hausdorffness is the main risk.** For self-similar actions it can fail. It is governed by the finiteness
  of the minimal strongly fixed words of each element (Exel–Pardo; recalled, not re-read). A
  non-finite-state `H` is exactly where that may break.

**Suggested wording.** "Finite presentation of `2V_H` follows from Li (arXiv:2110.04505v2, Ex. `ex:ZS`
(III)) if `H` is finitely presented and the action is right cancellative up to `=^*`, satisfies (Inv) and
(F), and has an effective germ groupoid. Simplicity of `D(2V_H)` follows from Matui (arXiv:1210.5800v3,
Thm `simple2`) if the groupoid is Hausdorff and effective. Neither is checked for any `H` with
`T_H ⊇ Z_(2)`."
