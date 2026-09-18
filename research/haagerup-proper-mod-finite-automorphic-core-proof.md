---
rg: 2
id: haagerup-proper-mod-finite-automorphic-core-proof
kind: route
title: "Pull back along automorphisms, add, and intersect the coset covers"
target: haagerup-iff-proper-mod-subgroup-with-finite-automorphic-core
requires: []
---

Notation is as in the target. This is a direct proof from the definitions.

**Item 1.** If `ψ(g) = ‖b(g)‖²` for a cocycle `b` of `π`, then `b ∘ α` is a cocycle of `π ∘ α`,
so `ψ ∘ α` is cnd. If `{ψ ≤ R} ⊆ x_1 H ∪ ... ∪ x_s H`, then

```text
{ψ ∘ α ≤ R} = α^{-1}({ψ ≤ R}) ⊆ α^{-1}(x_1) α^{-1}(H) ∪ ... ∪ α^{-1}(x_s) α^{-1}(H).
```

**Item 2.** A sum of cnd functions is cnd (direct sum of the representations and cocycles).
Since `ψ_1, ψ_2 ≥ 0`,

```text
{ψ_1 + ψ_2 ≤ R} ⊆ {ψ_1 ≤ R} ∩ {ψ_2 ≤ R} ⊆ ⋃_{i,j} (x_i H_1 ∩ y_j H_2).
```

If `z ∈ x_i H_1 ∩ y_j H_2`, then `x_i H_1 = z H_1` and `y_j H_2 = z H_2`, so
`x_i H_1 ∩ y_j H_2 = z(H_1 ∩ H_2)`. Hence the sublevel set lies in at most `s t` cosets of
`H_1 ∩ H_2`.

**Item 3.**
- *Only if.* A proper cnd function is proper modulo every subgroup: a finite set lies in finitely
  many cosets.
- *If.* Let `ψ` be cnd and proper modulo `H`. By item 1 applied to `α_i^{-1}`, `ψ ∘ α_i^{-1}` is cnd
  and proper modulo `α_i(H)`. By item 2 and induction on `r`, `Ψ = Σ_i ψ ∘ α_i^{-1}` is cnd and
  proper modulo `F = α_1(H) ∩ ... ∩ α_r(H)`. Every sublevel set of `Ψ` lies in finitely many
  cosets of the finite group `F`, so it is finite. Thus `Ψ` is a proper cnd function, and `G`
  has the Haagerup property. ∎
