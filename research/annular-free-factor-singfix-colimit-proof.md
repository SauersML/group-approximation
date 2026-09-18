---
rg: 2
id: annular-free-factor-singfix-colimit-proof
kind: route
title: SingFix({p},{p}) is the strictly increasing colimit of the finitely presented amalgams V_p *_(B_n) B_n H
target: annular-free-factor-germ-extensions-fail-bhm-singfix
---

**Item 1.**
1. *Pieces.* The germ map `S_p -> (Γ)_p` is onto with kernel `K_p`: an element of `S_p` with
   trivial germ at `p` has no singular points, so it lies in `V` (condition 2) and is the
   identity near `p`. `V_p = Stab_V(p)` is the preimage of `<t>`, since `V`-germs fixing `p`
   are `0^k w ↦ 0^(k') w`.
   - `V_p` is finitely presented. It is `K_p x| <τ>`, with `τ B_n τ^(-1) = B_(n+1)` for
     `n >= 1`. So it is the ascending HNN extension of `B_2` by conjugation by `τ^(-1)`.
     `B_n` is Thompson's group of `n` disjoint cones, `≅ V_(2,n) ≅ V`, which is finitely
     presented.
   - `Ĥ` normalizes each `B_n`. For `h ∈ Ĥ` and `b ∈ B_n`, `h b h^(-1)` is the identity on
     `0^n C`, since `h` preserves it. It has no singular points, so it lies in `V`.
2. *Amalgam.* Put `P = K_p Ĥ = ⋃_n B_n Ĥ`. `K_p` is normal in `V_p` and in `P`, hence in
   `A = V_p *_(K_p) P`. Then `A/K_p = <t> * H = S_p/K_p`, and the natural map `A -> S_p` is the
   identity on `K_p`. So it is an isomorphism, and `S_p ≅ V_p *_(K_p) P`.
3. *Colimit.* Put `Q_n = V_p *_(B_n) B_n Ĥ`. Inclusions give surjections `Q_n -> Q_(n+1)`,
   and `S_p = colim Q_n`, because amalgams commute with directed unions.
4. *Case `H` not finitely presented.* By `bhm-singfix-condition-forces-fp-germ-groups`,
   finite presentation of `S_p` would force it on `(Γ)_p = <t> * H`, hence on `H`. So `S_p`
   is not finitely presented.
5. *Case `H` finitely presented.* `B_n Ĥ ≅ B_n x| H` is finitely presented, and `B_n` is
   finitely generated, so each `Q_n` is finitely presented. If `S_p` were finitely
   presented, the kernel of `Q_1 -> S_p` would be the normal closure of finitely many
   elements. These would die in some `Q_n`, making `Q_n -> S_p` an isomorphism. That
   contradicts step 6.
6. *Every `Q_n -> Q_(n+1)` has a kernel.* Take `1 != h ∈ Ĥ` and `b ∈ B_(n+1) ∖ B_n`, and let
   `c = h b h^(-1)`, computed in `S_p`, so `c ∈ B_(n+1) ⊆ V_p`.
   - In `Q_n`: `h ∈ B_n Ĥ ∖ B_n`, because `Ĥ ∩ B_n = 1` by faithfulness of germs, and
     `b ∈ V_p ∖ B_n`. So `h b h^(-1)` is a reduced word of length 3 and does not lie in
     `V_p`. In particular `h b h^(-1) c^(-1) != 1` in `Q_n`.
   - In `Q_(n+1)`: both `h` and `b` lie in the factor `B_(n+1) Ĥ`, a subgroup of `S_p`, where
     `h b h^(-1) = c` holds. So the element dies.

**Item 2.** Suppose `φ` exists, and let `g_1, ..., g_k` generate `G`.
- Germ equality means agreement near `p`, so there is `n_0` with
  `τ^(-1) ĝ_i τ = φ(g_i)^` on `A_n` for all `n >= n_0` and all `i`.
- On `A_n` with `n >= 1`, `τ^(-1) ĝ τ` acts by `ρ_(n+1)(g)`, in the coordinates `α_n`. So
  `ρ_(n+1) = ρ_n ∘ φ` on generators, hence on `G`, for `n >= n_0`.
- Then `ρ_(n_0+m) = ρ_(n_0) ∘ φ^m` takes values in the finite group `F = ρ_(n_0)(G)`.
- Faithfulness of germs puts each `g != 1` outside `ker ρ_n` for infinitely many `n`. So
  `G` embeds in a product of groups of order at most `|F|`.
- A finitely generated group has finitely many homomorphisms to groups of order at most
  `|F|`. So `G` embeds in a finite product and is finite, a contradiction.
- For `t`-normalization, apply this to the automorphism `g ↦ t^(-1) g t`.

For a virtual endomorphism `φ: U -> G`, the same computation gives only
`[G : ker ρ_(n+1)] <= [G : U] [G : ker ρ_n]`, and the argument stops.
