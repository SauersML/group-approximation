---
rg: 2
id: n-adic-lodha-moore-groups-have-no-analytic-tree-coding-proof
kind: route
title: The finitary rule y(0kζ) = kζ forces y = g_0^(−1) on one side of ψ(0^∞), and the contracting rule y(00ζ) = 0y(ζ) then forces g_0 to fix that side pointwise
target: n-adic-lodha-moore-groups-have-no-analytic-tree-coding
requires:
  - analytic-codings-make-contracting-recursions-analytic
---

Fix `n ≥ 3` and a digit `k ∈ {1, …, n−2}`. Write "the lemma" for
`analytic-codings-make-contracting-recursions-analytic`.

**Step 1 (from `y_s` to `y`).** Put `s = (n−1)0`. `y_s` preserves the cone `sC_n` and fixes its
complement, so `Y` preserves `g_s(J) = ψ(sC_n)`. Define `Ŷ = g_s^(−1) ∘ Y ∘ g_s` on `J`.
- **It codes `y`:** `ψ(y(ζ)) = g_s^(−1)(ψ(s·y(ζ))) = g_s^(−1)(ψ(y_s(sζ))) = g_s^(−1)(Y(g_s(ψ(ζ)))) = Ŷ(ψ(ζ))`.
- **It is piecewise analytic:** if `Y` is, so is `Ŷ`, because `g_s` is an analytic diffeomorphism
  onto `g_s(J)`.

So it suffices to treat `y` itself.

**Step 2 (the two relations).** `ψ` is surjective and `ψ(iζ) = g_i(ψ(ζ))`, so Kodama's rules
`y(00ζ) = 0y(ζ)` and `y(0kζ) = kζ` give, on all of `J`,

- (R1) `Ŷ ∘ g_0^2 = g_0 ∘ Ŷ`;
- (R2) `Ŷ ∘ g_0 ∘ g_k = g_k`.

**Step 3 (the lemma).**
- **Apply it.** Use `u = 00`, `v = 0`, the finitary branch `w = 0k`, `z = k`.
- **The fixed point.** `p = ψ(0^∞)` is the unique fixed point of `g_0` in `J`, by Item 1 of the
  lemma with `u = 0`.
- **The map Φ.** On `g_0g_k(J)` the finitary branch gives `g_z ∘ g_w^(−1) = g_k ∘ g_k^(−1) ∘ g_0^(−1) = g_0^(−1)`.
  So `Φ` is the analytic continuation of `g_0^(−1)` to `S`, and `g_0 ∘ Φ = id` on `S`: the
  identity holds on `g_0g_k(J)` and propagates by the identity theorem.
- **What the Corollary gives.** `Ŷ = Φ` on `S`. Here `S` is `J` or one of `[a,p]`, `[p,b]`, and
  in every case it is a nondegenerate interval containing `g_0g_k(J)`.

**Step 4 (the contradiction).** `g_0^2` is increasing, as a composition of two maps with the same
monotonicity, and fixes `p`. So it maps each of `[a,p]` and `[p,b]` into itself, and
`g_0^2(S) ⊆ S`. Now take `x ∈ S`.
- **Using `g_0 ∘ Φ = id`:** `g_0^2(x) ∈ S`, so `g_0(Φ(g_0^2(x))) = g_0^2(x)`, and injectivity of
  `g_0` gives `Φ(g_0^2(x)) = g_0(x)`.
- **Using (R1):** `Φ(g_0^2(x)) = Ŷ(g_0^2(x)) = g_0(Ŷ(x)) = g_0(Φ(x))`.
- **Comparing the two:** `g_0(Φ(x)) = g_0(x)`, so `Φ(x) = x`. Then `g_0(x) = g_0(Φ(x)) = x`.

Therefore `g_0` fixes every point of the nondegenerate interval `S`. By Step 3, `g_0` has only one
fixed point in `J`. This contradiction shows no piecewise-analytic `Ŷ`, and hence no
piecewise-analytic `Y`, exists. ∎

**Consequences.**
- **Item 1.** A digit recoding through a complete prefix code `c`, followed by Lodha–Moore's `Φ`,
  is an analytic tree coding with `g_i = Φ_(c(i))`, a product of the two binary cone maps
  `t ↦ t/(1+t)` and `t ↦ t+1`. These lie in `PSL_2(Z)`. The n-ary Farey and Stern–Brocot codings
  have cone maps in `PSL_2(Z)` by construction, and PL codings have affine cone maps.
- **Item 2.** This restates what the argument excludes.
- **Item 3.** The proof used only (R1) and (R2).
