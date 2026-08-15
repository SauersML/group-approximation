---
rg: 2
id: parity-trap-window-proof
kind: route
title: Two Steinberg commutators write the marked element in slot-fixing letters
target: parity-trap-window
requires: [parity-flip-models-satisfy-two-point]
---

# Two Steinberg commutators write the marked element in slot-fixing letters

All identities are Steinberg relations in `EL_r(R)`, `r ≥ 3`, valid over
every base ring and in every characteristic:
`[e_{ij}(a), e_{jk}(b)] = e_{ik}(ab)` for `i, j, k` pairwise distinct, and
`e_{ij}(a)e_{ij}(b) = e_{ij}(a+b)`.

**Step 1: `e_13(x^{-m})` from one mixed conjugate.**  With `a = x^{-m}`,
`b = 1`:

```text
h e_23(1) h^{-1} = [e_12(x^{-m}), e_23(1)] · e_23(1) = e_13(x^{-m}) e_23(1),
```

so `e_13(x^{-m}) = γ'₁ γ₂` with `γ'₁ = h e_23(1) h^{-1} ∈ hΓh^{-1}` and
`γ₂ = e_23(-1) ∈ Γ` (constants lie in `R_+`).

**Step 2: `h` as a commutator.**  With indices `(1,3), (3,2) → (1,2)`:

```text
[e_13(x^{-m}), e_32(1)] = e_12(x^{-m}) = h,
```

and `γ₃ = e_32(1) ∈ Γ`.  Substituting Step 1,

```text
h = (γ'₁ γ₂) γ₃ (γ'₁ γ₂)^{-1} γ₃^{-1} = γ'₁ γ₂ γ₃ γ₂^{-1} γ'₁^{-1} γ₃^{-1}.
```

**Step 3: transport parities.**  Every `γ ∈ Γ` fixes `p = Γ`
(`γ·Γ = Γ`), so `τ(γ) = 0` where defined; every `γ' ∈ hΓh^{-1}` fixes
`q = hΓ` (`hγh^{-1}·hΓ = hγΓ = hΓ`), so `τ(γ') = 0` where defined.  These
clauses never conflict for this pair: an element fixing `p` and
transporting `q` to `p` would satisfy `p = γ·q = q`, false.  And
`τ(h) = 1` because `h·p = hΓ = q`.

**Step 4: the trap.**  Let `P` be additive on `F* × F*` with `P = τ` on
letters.  Additivity at `(1,1)` gives `P(1) = 0`; at `(γ, γ^{-1})` for the
three letter pairs (all in `F*`) gives `P(γ^{-1}) = P(γ) = 0`.  Walking
the prefix chain — each step is a product of two elements of `F*` —

```text
P(v₁) = 0, P(v₂) = 0, P(v₃) = 0, P(v₄) = 0, P(v₅) = 0,
P(h) = P(v₅) + P(γ₃^{-1}) = 0,
```

while `P(h) = τ(h) = 1`.  Contradiction; no such `P` exists.

**Step 5: flip models die.**  By the converse half of
`parity-flip-models-satisfy-two-point`, a flip model witnessing the
two-point clauses at `(F*, ε)` with `ε < 1` yields exactly such a `P`.
None exists, so none witnesses.

**Remark (why this does not yet refute the two-point claim).**  The trap
kills the one-bit models; a many-bit model can pay the six constraint
edges of the word at a vanishing fraction of basepoints and survive.
Turning the six-letter odd cycle into a refutation for all models is the
defect-robust expansion question left open by
`exact-models-cannot-separate-marked-pair` — the cycle supplies the
homotopy class, expansion would have to supply the ubiquity.
