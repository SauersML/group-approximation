---
rg: 2
id: thompson-circle-kernel-outer-extensions-bffhz-q32-proof
kind: route
title: Enlarge the BFFHZ actor by B, identify the kernel's image as word automorphisms, discharge it by the circle lemma, and apply the two-generator-set normal-generation argument
target: thompson-circle-kernel-outer-extensions-reduce-to-bffhz-q32
requires: [micro-supported-word-automorphisms-are-pointwise-inner, relative-automorphism-action-is-highly-transitive, type-a-action-gives-boone-higman-for-subgroups]
---

Notation is from `research/artifacts/outer-extensions-mif-pbh-2026-09-16.md`, §§4--8.
Only the statements there that do not use MIF are used, and each is re-proved or
cited below.

**Setup.**
- `Γ_B = { γ ∈ Aut(S * F_m) : γ(S) = S, γ|_S ∈ B }`, with `ρ(γ) = γ|_S`.
- `hat(β)` is `β` on `S` and the identity on the free letters.
- `Γ_B` acts on `X` by `γ·f = ρ(γ) ∘ f ∘ γ^-1`.
- `K` is the kernel of this action, `K_A = K ∩ A`, `W = ρ(K)`, and `Λ_B = Γ_B/K`.

## 1. Facts that do not use MIF

1. **Split extension.** `Γ_B = A ⋊ hat(B)`, and the formula is an action extending
   the inverse of precomposition on `A` (artifact Lemma 3.1--3.2; the proof is two
   lines and uses only `γ(S) = S`).
2. **Finite presentation.** `Γ_B` is finitely presented.
   - `A` is finitely presented by BFFHZ Proposition 1.1, since `S` is finitely
     presented and centreless (imported, as quoted in the artifact §9).
   - `B` is finitely presented as an extension of `Inn(S) ≅ S` by `B/Inn(S)`.
3. **Inner part of the kernel.** `ι_s ∈ K` for `s ∈ S`, where `ι_s` is conjugation
   by `s` on `S * F_m`. So `Inn(S) <= W`. Indeed,
   `(ι_s·f)(w) = s f(s^-1 w s) s^-1 = f(w)`.
4. **`B` embeds.** `hat(B) ∩ K = 1`. If `hat(β)` acts trivially, then
   `β(f(x_1)) = f(x_1)` for all `f`, and `f(x_1)` ranges over `S`.
5. **Every element of `W` is a word automorphism.** Let `γ ∈ K` and `β = ρ(γ)`, and
   put `w = γ^-1(x_1)`. Let `u ∈ S * <y>` be the image of `w` under `x_1 -> y`,
   `x_k -> 1` for `k >= 2`. Let `f_t` send `x_1 -> t` and `x_k -> 1`. From
   `γ·f_t = f_t` we get `β(u(t)) = t`, so `β^-1(t) = u(t)` for all `t`. So `β^-1` is
   a word automorphism. Since `W` is a group, every element of `W` is one.
   (This is artifact Proposition 4.3, first half, which uses no MIF.)

## 2. The kernel is finitely normally generated

1. **(b).** By items 1.3 and 1.5, `W` satisfies the hypothesis of part (3) of
   `micro-supported-word-automorphisms-are-pointwise-inner`. So `W/Inn(S)` is
   finitely generated, hence finitely normally generated in `B/Inn(S)`.
2. **(a).** `A` is finitely presented and `A/K_A` is finitely presented by
   hypothesis, so `K_A` is finitely normally generated in `A`.
3. **Generators.** Choose:
   - `a_1, ..., a_p` normally generating `K_A` in `A`;
   - generators `s_1, ..., s_q` of `S`;
   - `k_1, ..., k_l ∈ K` whose images generate `W/Inn(S)`.

   Let `N` be the normal closure of all of these in `Γ_B`. Then `N <= K`.
4. **Image.** `ρ` is onto `B`, so `ρ(N)` is the normal closure in `B` of the
   `c_{s_j}` and the `ρ(k_i)`. That contains `Inn(S)` and all `ρ(k_i)`, so it
   contains `W`. Also `ρ(N) <= ρ(K) = W`.
5. **Conclusion.** `K_A` is normal in `Γ_B`, as the intersection of two normal
   subgroups. It is the normal closure in `A` of the `a_i`, so `K_A <= N`. Now
   `ker(ρ|_K) = K_A <= N` and `ρ(N) = ρ(K)`, so `N = K`.
6. Hence `Λ_B` is finitely presented.

## 3. Type (A)

1. **Faithful.** `Λ_B` acts faithfully on `X` by construction.
2. **Finitely presented.** §2.6.
3. **Stabilizers.** Fix `f ∈ X`.
   - `ρ : Stab_{Γ_B}(f) -> B` is onto. Given `β`, the action of `A` is transitive
     (BFFHZ Proposition 2.3, in `relative-automorphism-action-is-highly-transitive`),
     so some `α ∈ A` has `α·(hat(β)·f) = f`, and then `ρ(α hat(β)) = β`.
   - Its kernel `Stab_A(f)` is finitely generated (BFFHZ Proposition 2.6, same node).
   - So `Stab_{Γ_B}(f)` is finitely generated, and so is its quotient by `K`.
4. **Pair orbits.** The action of `A` on `X` is highly transitive, so it has finitely
   many orbits on `X × X` (two: the diagonal and its complement). Every `Λ_B`-orbit is a union of orbits of the image
   of `A`.
5. **`B` embeds.** Item 1.4 embeds `B` in `Λ_B`. So `B ∈ B_A`, which is item 1 of the
   claim.

## 4. Outer extensions

`S` is nonabelian simple, so `C_I(S)` is normal in `I` and meets `S` trivially.
It embeds in `Q` and acts trivially on `S`. Since `Q -> Out(S)` is injective,
`C_I(S) = 1`.

So conjugation gives an injection `I -> Aut(S)` with image `B`, `Inn(S) <= B` and
`B/Inn(S) ≅ Q` finitely presented (artifact Lemma 1). Item 1 gives `I ∈ B_A`.
`type-a-action-gives-boone-higman-for-subgroups` gives solvable word problem and
finitely presented simple overgroups for finitely generated subgroups. ∎
