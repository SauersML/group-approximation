---
rg: 2
id: prime-shift-affine-group-a1-is-not-finitely-presented
kind: claim
title: The prime-shift permutation group A_1 is not finitely presented, because deep-denominator germs map A_1 modulo the translations onto Z wr Z
distinct_from:
  prime-shift-affine-group-a1-is-finitely-presented: that is the OPEN claim this refutes.
  prime-shift-hnn-groups-are-not-finitely-presented: that proves the HNN group Π_1 is not finitely presented and that finite presentation of A_1 would need a dilation in the normal closure of τ; this shows no dilation is there, so A_1 is not finitely presented either, whether or not Π_1 -> A_1 is injective.
  prime-shift-hnn-map-to-a1-is-injective: that asks whether Π_1 -> A_1 is injective; this settles finite presentation of A_1 without answering that, and confines the kernel.
---

**ESTABLISHED** through `prime-shift-affine-group-a1-is-not-finitely-presented-proof`
(lane proof, elementary; inputs are Baumslag's wreath product theorem and item 1 of
`prime-shift-hnn-groups-are-not-finitely-presented`; referee requests sent).

**Notation.** As in `gl-n-q-lies-in-prime-shift-permutation-group`:
- `A_1 = <τ, δ, ι, σ> <= Sym(Q)`, with `τ = (x ↦ x+1)`, `δ = (x ↦ 2x)` and
  `ι = (x ↦ −x)`;
- `σ` is the prime shift, `σ(p_k) = p_(k+1)`, `σ(−1) = −1`, `σ(0) = 0`;
- `m_r = (x ↦ rx)`, and `v_k = v_(p_k)` is the `p_k`-adic valuation.

**Statement.**
1. **Deep-denominator germs.** There is a surjective homomorphism
   `Φ : A_1 -> Z ≀ Z = (⊕_(k∈Z) Z) ⋊ Z` with:
   - `Φ(τ) = Φ(ι) = 1`;
   - `Φ(σ)` the generator of the top `Z`;
   - `Φ(m_r) = (v_k(r))_k`, the valuation vector of `r`, for every `r ∈ Q^x`.

   Here `Φ(g)` is the germ of the action of `g` on points with one very deep denominator:
   if `x` has `v_j(x) = v ≪ 0` and all other valuations bounded, then `g(x)` has exactly
   one deep denominator, at index `j'`, with valuation `v'`, and `(j', v')` depends only
   on `g` and `(j, v)`.
2. **No dilation is a product of translation conjugates.** `m_r ∉ <<τ>>_(A_1)` for every
   `r ∈ Q_(>0)`, `r ≠ 1`.
3. **A_1 is not finitely presented.** `A_1 / <<τ>>` maps onto `Z ≀ Z` with kernel of order
   at most `2`, the image of `ι`. So it is not finitely presented, and neither is `A_1`.

**Consequences.**
- `prime-shift-affine-group-a1-is-finitely-presented` is **refuted**. So the action of
  `A_1` on `Q` is not of type (A), and the route `aff-q-bh-via-prime-shift-type-a-action`
  fails in its stated form.
- **The kernel of `Π_1 -> A_1`.** The composite `Π_1 -> A_1 -> Z ≀ Z` is the quotient by
  `<<τ>>` followed by `Q^x ⋊ <s> -> Z ≀ Z`, which kills only `±1`. So
  `ker(Π_1 -> A_1) ⊆ <<τ>>_(Π_1)·<ι>`. Any hidden relation lies in the translation part.
  Whether one exists stays open (`prime-shift-hnn-map-to-a1-is-injective`).

**Scope.** The germ argument is specific to `n = 1`. For `n >= 2`, `GL_n(Z)` moves a deep
denominator between coordinates. The corresponding invariant would be a determinant
valuation, which points of `Q^n` do not see. So finite presentation of `K_n` is not
decided here.
