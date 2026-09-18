# Re-review (gq-referee-a, proof-gap lens): SL_n(Z_(l)) and GL_n(Z_(l)) in finitely generated RF elementary groups

**Reviewed:** `sl-n-z-localized-embeds-in-fg-rf-elementary-group` and its `-proof`, as corrected in 0db9f0179, read on
origin/main.

**My earlier PASS was wrong on item 2.** The original item 2 claimed that
`g ↦ diag(Θ(g), Θ(g)^(−1))` embeds `GL_n(Z_(l))` in `E_(2n)(R̄_l)`. That map is not a homomorphism on the
nonabelian group `GL_n(Z_(l))`, and I passed it without checking multiplicativity. It is the trap recorded in
`whitehead-diagonal-map-is-not-multiplicative`, and the same error as in `euler-base-embeds-in-fp-steinberg-group`
(FAIL, `gq-referee-a-euler-base-embeds-in-fp-steinberg-group.md`).

**Verdict on the corrected node: PASS.**

## Checks
- **The new item 2.** The map is `g ↦ Θ(diag(g, det(g)^(−1)))`.
  - `g ↦ diag(g, det g^(−1))` is a homomorphism `GL_n(Z_(l)) → SL_(n+1)(Z_(l))`: `det` is multiplicative into the
    commutative group `Z_(l)^×`, and block-diagonal matrices multiply blockwise. It is injective.
  - `SL_(n+1)(Z_(l)) = E_(n+1)(Z_(l))` by the local-ring reduction in the proof. It uses Whitehead only element by
    element, for `1×1` blocks, and a diagonal matrix of determinant 1 over a commutative ring is a product of
    `diag(…, a, a^(−1), …)` factors.
  - `Θ` is multiplicative and injective on `M_(n+1)(Z_(l))`, with `Θ(e_ij(c)) = e_ij(θ(c))`. So the image lies in
    `E_(n+1)(R̄_l)`. ✓
- **Whitehead's lemma, as now written.**
  - `[[1,a],[0,1]][[1,0],[−a^(−1),1]][[1,a],[0,1]] = [[0,a],[−a^(−1),0]]`, and multiplying by `[[0,−1],[1,0]]` gives
    `diag(a, a^(−1))`.
  - `[[1,−1],[0,1]][[1,0],[1,1]][[1,−1],[0,1]] = [[0,−1],[1,0]]`.
  - Both hold in blocks over any unital ring. The added sentence, that the lemma holds element by element but the
    map is not a homomorphism, is right. ✓
- **The summary line.** `GL_n(Z_(l))` inside `E_(n+1)(R̄_l)` for `n ≥ 2` lands in a finitely generated group, since
  `n + 1 ≥ 3` (item 3). `SL_2(Z_(l)) ≤ E_2 ≤ E_3` is also correct.
- Items 1, 3 and 4 are unchanged from my earlier review. They still pass.

## Nit
- The correction note credits gq-referee-b with the `G_l` error. Two reports found it independently:
  `gq-referee-b-euler-base-embeds-in-fp-steinberg-group.md` and `gq-referee-a-euler-base-embeds-in-fp-steinberg-group.md`
  (d10cfaf1b). Cite both.
