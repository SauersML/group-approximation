---
rg: 2
id: aut-free-embeddability-passes-to-finite-index-overgroups-proof
kind: route
title: Induce the action to a free product of copies indexed by cosets, and extend automorphisms by a free letter
target: aut-free-embeddability-passes-to-finite-index-overgroups
requires: []
---

**1. Induction.** Let `d = [G : H]` and choose `t_1 = 1, t_2, …, t_d` with
`G = t_1 H ⊔ ⋯ ⊔ t_d H`. For `g ∈ G` and each `i` there are unique
`σ_g(i) ∈ {1, …, d}` and `h_i(g) ∈ H` with `g t_i = t_{σ_g(i)} h_i(g)`. From
`(g g′) t_i = g t_{σ_{g′}(i)} h_i(g′) = t_{σ_g σ_{g′}(i)} h_{σ_{g′}(i)}(g) h_i(g′)`:

    σ_{gg′} = σ_g σ_{g′},      h_i(g g′) = h_{σ_{g′}(i)}(g) · h_i(g′).      (∗)

Let `B = A_1 ∗ ⋯ ∗ A_d` with isomorphisms `ε_i: A → A_i`. By the universal
property of free products there is a unique endomorphism `Φ(g)` of `B` with

    Φ(g)(ε_i(a)) = ε_{σ_g(i)}( ρ(h_i(g))(a) )      for all i and a ∈ A.

- **Homomorphism.** `Φ(g′)(ε_i(a)) = ε_{σ_{g′}(i)}(ρ(h_i(g′))a)`, and applying
  `Φ(g)` gives `ε_{σ_g σ_{g′}(i)}(ρ(h_{σ_{g′}(i)}(g)) ρ(h_i(g′)) a)`, which is
  `ε_{σ_{gg′}(i)}(ρ(h_i(gg′)) a) = Φ(gg′)(ε_i(a))` by `(∗)` and because `ρ` is a
  homomorphism. So `Φ(g)Φ(g′) = Φ(gg′)` on generators, hence on `B`. Also
  `σ_1 = id` and `h_i(1) = 1`, so `Φ(1) = id`. Each `Φ(g)` is therefore
  invertible with inverse `Φ(g^{-1})`, and `Φ: G → Aut(B)` is a homomorphism.
- **Factors.** `Φ(g)(A_i) = A_{σ_g(i)}`, because `ρ(h_i(g))` is onto `A`.
- **Injectivity.** Suppose `Φ(g) = id`. Distinct factors of a free product
  intersect trivially and `A ≠ 1`, so `A_{σ_g(i)} = A_i` forces `σ_g(i) = i` for
  all `i`. Then `Φ(g)` restricted to `A_i` is `ε_i ρ(h_i(g)) ε_i^{-1} = id`, so
  `ρ(h_i(g)) = id` and `h_i(g) = 1` by injectivity of `ρ`. With `i = 1`:
  `g = g t_1 = t_1 h_1(g) = 1`.

**2. Free groups.** For `A = F_k` the free product `B` is free of rank `dk`, so
`G ↪ Aut(F_{dk})`. For the equivalences: if `G` embeds in some `Aut(F_n)` then so
does every subgroup, by restriction; `G` is a finite-index subgroup of itself; and
item 1 passes an embedding of any finite-index subgroup up to `G`.

**3. Aut inside Out.** Write `F_{n+1} = F_n ∗ ⟨t⟩` with `n ≥ 1` and send
`β ∈ Aut(F_n)` to the class of `β ∗ id_⟨t⟩`. This is a homomorphism. If
`β ∗ id = ι_w`, then `w` commutes with `t`, so `w = t^k` since centralizers of
nontrivial elements of a free group are cyclic and `t` is not a proper power. For
`1 ≠ x ∈ F_n` the word `t^k x t^{-k}` is reduced in the free product and lies
outside `F_n` unless `k = 0`, while `ι_w(x) = β(x) ∈ F_n`. So `k = 0`, `ι_w = id`,
and `β = id`. This is the same argument as §1 of
`research/artifacts/bh-out-fn-into-aut-fm-2026-09-12.md`.

**Scope remark (Out hosts).** Given only `ρ: H → Out(A)`, choose representatives
`ρ̃(h) ∈ Aut(A)` and define `Φ(g)` factorwise as above. Then `Φ(g)Φ(g′)` and
`Φ(gg′)` differ by an automorphism of `B` acting on each `A_j` by an inner
automorphism of `A_j`. For `A` free of rank `≥ 2` and `d ≥ 2`, such an
automorphism with a nontrivial conjugator on one factor and the identity on
another is not inner in `B` (an inner automorphism fixing `A_2` pointwise is
conjugation by an element of the trivial centralizer of `A_2`). So this method
gives no homomorphism into `Out(B)`, and none is claimed.
