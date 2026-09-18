# Referee report (citation/hypothesis lens, with proof check): `prime-shift-affine-group-a1-is-not-finitely-presented`

Referee: lane gq-referee-b, 2026-09-18.

**Reviewed**, as landed at 72ea4a580 (gq-ring-fp-simple):
- the claim and its `-proof`;
- the refutation of `prime-shift-affine-group-a1-is-finitely-presented`;
- its effect on the route `aff-q-bh-via-prime-shift-type-a-action`.

## Verdict

**PASS.**
- The three inputs are used within their hypotheses.
- The germ argument is correct.
- The route is dead as stated.
- The `K_n` scope sentence is honest in its conclusion ("not decided here"), but its stated reason is imprecise (W1).

## Inputs

- **Baumslag, *Wreath products and finitely presented groups*, Math. Z. 75 (1961) 22–28.** A restricted wreath product
  `A ≀ B` with `A ≠ 1` and `B` infinite is not finitely presented. So `Z ≀ Z` is not finitely presented. This is the
  standard citation, used correctly. The primary was not re-read here.
- **"A quotient of a finitely presented group by the normal closure of finitely many elements is finitely
  presented."** Standard: add the finitely many relators. It is used twice, for `⟨⟨τ⟩⟩` and for the finite normal
  subgroup `F`, which is finitely normally generated because it is finite. **Correct.**
- **Item 1 of `prime-shift-hnn-groups-are-not-finitely-presented`.** `Π_1 = Aff(Q) *_{Q^×} (Q^× ⋊_σ ⟨s⟩)`.
  - The normal closure of `τ` in `Aff(Q)` is the translation group `Q`. That group meets the edge group `Q^×`
    trivially.
  - So `Π_1/⟨⟨τ⟩⟩ = Q^× *_{Q^×} (Q^× ⋊ ⟨s⟩) = Q^× ⋊_σ ⟨s⟩`.
  - `Q^× = {±1} × ⊕_ℤ Z`, and `σ` shifts the free part and fixes `−1`. So the quotient is `Z/2 × (Z ≀ Z)`.
  - **Correct.**

## Proof checks

**Generator germs.**
- `τ^{±1}` preserves every negative valuation, since `v_p(x ± 1) = v_p(x)` when `v_p(x) < 0`. It keeps non-negative
  valuations non-negative, and it never produces `0` from a deep point.
- `ι` preserves every valuation.
- `δ^{±1}` moves only `v_{p_0}`, by `±1`.
- `σ` shifts the prime indices.
- **Correct.**

**Words.** With margin `C + 3ℓ + 1`, every intermediate point of a word of length `ℓ` stays deep: shallow valuations
are `>= −C−ℓ`, and the deep one is `< −C−2ℓ`.
- The germ depends only on the permutation, since each deep enough `(j,v)` is realized by `p_j^v`.
- `g ↦ [φ_g]` is a homomorphism.
- **Correct.**

**The germ group.** `⟨[φ_δ], [φ_σ]⟩` is `{(j,v) ↦ (j+k, v+e_j)} ≅ Z ≀ Z`. Distinct `(e,k)` give distinct germs, and
`Φ(m_r) = (v_k(r))_k`. **Correct.**

**Item 3.** `Π_1/⟨⟨τ⟩⟩ → A_1/⟨⟨τ⟩⟩ → Z ≀ Z` is the projection with kernel `⟨ι⟩`, so `|F| <= 2`. If `A_1` were finitely
presented, then `Z ≀ Z` would be too, which contradicts Baumslag. **Correct.**

## Scope question 1: is `aff-q-bh-via-prime-shift-type-a-action` dead?

**Yes, as stated.**
- A type (A) action requires the acting group to be finitely presented. BFFHZ, arXiv:2503.21882v2, Introduction,
  verified earlier: "(i) The group Γ is finitely presented". The repo's `type-a-action-gives-boone-higman-for-subgroups`
  says the same.
- The route's first requirement is `prime-shift-affine-group-a1-is-finitely-presented`, which is now refuted.
- **Not killed:** routes through a different, finitely presented overgroup of `A_1` with a type (A) action. The
  refutation says nothing about those.

## Scope question 2: the `K_n` sentence

"Finite presentation of `K_n` is not decided here" is **honest**. The stated reason, "`GL_n(Z)` moves a deep
denominator between coordinates", is **imprecise**. Suggested replacement (W1):

- Define `v_p(x) = min_i v_p(x_i)` for `x ∈ Q^n`. `GL_n(Z)` **preserves** it, since an invertible integral matrix
  preserves `p`-adic lattices. Integer translations also preserve negative values. So moving a denominator between
  coordinates is harmless for a vector valuation.
- The germ fails for the **dilations** `diag(r, 1, …, 1)`. They change `v_p(x)` or not depending on which coordinate
  attains the minimum, and a `GL_n(Z)`-conjugate can move that coordinate. So there is no well-defined germ
  homomorphism of the `n = 1` kind.
- The "determinant valuation" remark is a heuristic about what invariant would be needed. Label it so.
