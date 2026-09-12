---
rg: 2
id: two-point-fails-via-fixed-algebra
kind: route
title: The assembled projection contradicts the fixed-algebra rigidity
target: two-point-approximation-fails
requires: [two-point-data-yields-invariant-projection, normal-closure-fixes-gamma-fixed-algebra]
---

# The assembled projection contradicts the fixed-algebra rigidity

Immediate composition.  Suppose `two-point-orbit-approximation` held.
`two-point-data-yields-invariant-projection` assembles from its models a
sofic representation `σ : G → S_𝒰` and a projection `a ∈ D_𝒰` with
`σ(γ)a = a` for all `γ ∈ Γ` and `τ(a △ σ(h)a) ≥ c > 0`.  But
`h = u e_12(x_1) u^{-1} ∈ ⟨⟨Γ⟩⟩_G`, and
`normal-closure-fixes-gamma-fixed-algebra` makes every element of the
normal closure act trivially on `D_𝒰^{σ(Γ)} ∋ a`: `σ(h)a = a`,
contradiction.  Hence the two-point claim is false — which is exactly the
present target.

**Parity consistency, on the record.**  The refutation reproduces
`parity-trap-window` as a special case rather than colliding with
`parity-flip-models-satisfy-two-point`: if flip models existed at every
window, `P := lim_𝒰 P_n` would be a genuine homomorphism `G → ℤ/2` with
`P = τ` on pair-defined elements, and then
`P(γ₀) = P(u^{-1}hu) = P(h) = τ(h) = 1` while `τ(γ₀) = 0` — the trap in
one line, from the same `h ∈ ⟨⟨Γ⟩⟩` mechanism.  Flip models exist only at
windows below the trap, and the assembly here consumes models at all
`F_n ↗ G`.

Two scope notes the composition inherits.  The refutation is
**non-constructive in the window**: it spends the `∀F ∀ε` quantifier on a
sequence and exhibits no explicit failing `(F, ε)` — the same shape as
`coordinate-action-not-sofic`, and complementary to the fixed-window,
exact-model theorem `exact-models-cannot-separate-marked-pair`.  And it
inherits the unrefereed-preprint trust surface of Kun--Thom 2608.06222
through Theorem 4.1, exactly as `kun-thom-nonsofic-wreath` does.
