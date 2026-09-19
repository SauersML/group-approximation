---
rg: 2
id: parity-trap-window
kind: claim
title: An explicit thirteen-element window traps the transport parity of the marked pair
distinct_from:
  parity-flip-models-satisfy-two-point: that shows flip models succeed wherever the transport parity extends locally additively; this exhibits an explicit window of the Kun--Thom pair where no such extension exists, so the degenerate prover class dies there.
  exact-models-cannot-separate-marked-pair: that kills genuine actions by expansion; this kills one-bit parity models by a six-letter Steinberg identity, and the two mechanisms are disjoint — neither implies the other.
  congruence-transporter-girth: that bounds word lengths of kernel transporters in congruence quotients; this is an identity in G itself — the marked element is a short word in slot-fixing letters — and involves no quotient.
---

Let `(p,q) = (Γ, hΓ)` be the marked pair of the Kun--Thom Theorem E pair,
`h = e_12(x^{-m})`, `m = (1,…,1)`, `r ≥ 3`.  Set

```text
γ'₁ = h e_23(1) h^{-1} ∈ hΓh^{-1},     γ₂ = e_23(-1) ∈ Γ,     γ₃ = e_32(1) ∈ Γ.
```

**Theorem.**

1. **The marked element is a six-letter word in slot-fixing letters:**

   ```text
   h = (γ'₁ γ₂) · γ₃ · (γ'₁ γ₂)^{-1} · γ₃^{-1}
     = γ'₁ γ₂ γ₃ γ₂^{-1} γ'₁^{-1} γ₃^{-1},
   ```

   where each letter lies in `Γ` (fixing `p`, transport parity `τ = 0`) or
   in `hΓh^{-1}` (fixing `q`, transport parity `τ = 0`), while
   `τ(h) = 1` since `h·p = q`.

2. **Consequently the window**

   ```text
   F* = {1, h, γ'₁, γ₂, γ₃, γ'₁^{-1}, γ₂^{-1}, γ₃^{-1}, v₁, v₂, v₃, v₄, v₅}
   ```

   (the `v_i` being the proper prefixes `γ'₁`, `γ'₁γ₂`, `γ'₁γ₂γ₃`,
   `γ'₁γ₂γ₃γ₂^{-1}`, `γ'₁γ₂γ₃γ₂^{-1}γ'₁^{-1}` of the word in 1) admits
   **no** function `P : G → ℤ/2` that is additive on `F* × F*` and equals
   the transport parity on the letters where it is defined: additivity
   along the prefix chain forces `P(h) = 0`, while `τ(h) = 1` forces
   `P(h) = 1`.

3. **Hence every flip model fails at `(F*, ε)` for every `ε < 1`** (by the
   converse half of `parity-flip-models-satisfy-two-point`), and any
   witness of `two-point-orbit-approximation` at windows containing `F*`
   must be a genuinely non-parity, genuinely non-exact model: the two
   degenerate prover classes are now both dead at one explicit window.

The identity in 1 is the same mechanism as the finite-quotient collapse —
`h` lies in `⟨Γ ∪ hΓh^{-1}⟩` because negative monomials are commutators of
mixed-conjugate elementaries — but it is an identity in `G` itself, needing
no quotient, no girth, and no expansion.  It is the group-theoretic seed
that any defect-robust refutation of the two-point claim will amplify: the
six-letter word is a slot-admissible odd cycle available at every
basepoint of every model, and what remains open is only whether its
traversal can be forced to close approximately.
