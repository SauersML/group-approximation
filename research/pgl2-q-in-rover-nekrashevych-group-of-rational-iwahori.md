---
rg: 2
id: pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori
kind: claim
title: PGL_2(Q) embeds in the Rover--Nekrashevych group V_p(Gamma_p) of the rational Iwahori group, a self-similar group that is neither finitely generated nor finite-state
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that asks for a finitely presented simple host of GL_n(Q); this puts PGL_2(Q) into a Rover--Nekrashevych group that is not finitely generated, and it shows that this device reaches neither SL_2(Q) nor GL_n(Q) for n >= 3.
  piecewise-commutative-linear-hosts-miss-linear-gl-n-q: that shows a finitely generated host with commutative-linear pieces misses divisible linear groups; the host here has Mobius pieces from the non-finitely-generated group Gamma_p, and any finitely generated replacement for Gamma_p must be non-linear.
  aperiodic-tree-almost-automorphism-fg-subgroups-are-rf: that kills varying-degree trees; this uses the regular p-ary tree, where level shifts supply p-divisibility.
---

**ESTABLISHED** through `pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori-proof`.
Lane proof, not independently reviewed. **No priority claimed.** That `PGL_2(Q_p)`
acts on `P^1(Q_p)`, the boundary of its Bruhat–Tits tree, inside Neretin's group
is classical. What this node records is the exact self-similar group of local
actions and the limits of the device.

## Setting

- `p` is a prime. `T_p` is the rooted `p`-ary tree, and `∂T_p = Z_p` through
  `p`-adic digits.
- The cone of level `k` at `a ∈ {0, ..., p^k - 1}` is `a + p^k Z_p`. Its
  canonical coordinate is `φ_{a,k}(u) = a + p^k u`.
- **The rational Iwahori group** is
  `Γ_p = { γ ∈ PGL_2(Q) : γ(Z_p) = Z_p and |γ(x) - γ(y)|_p = |x - y|_p for x, y ∈ Z_p }`,
  acting on `Z_p` by Möbius transformations. Bijective isometries of `Z_p` are
  exactly the automorphisms of the tree of balls, so `Γ_p <= Aut(T_p)`. The
  action is faithful.
- `V_p(Γ_p)` is the Röver–Nekrashevych group (Scott's `V_d(G)`; survey §4.2).
  It consists of the homeomorphisms of `Z_p` that, on the cones of some finite
  cone partition, have the form `φ_{b,k'} ∘ γ ∘ φ_{a,k}^{-1}` with `γ ∈ Γ_p`.

## Statement

1. **Self-similar.** For `γ ∈ Γ_p` and a cone `a + p^k Z_p`, write
   `γ(a + p^k Z_p) = b + p^k Z_p`. Then the section
   `φ_{b,k}^{-1} ∘ γ ∘ φ_{a,k}` lies in `Γ_p`.
2. **Iwahori description.** `Γ_p` is the image in `PGL_2(Q)` of the matrices
   `[[α,β],[c,δ]] ∈ GL_2(Z_(p))` with `c ∈ p Z_(p)`. Equivalently,
   `Γ_p = PGL_2(Q) ∩ I_p`, where `I_p` is the Iwahori subgroup of `PGL_2(Q_p)`.
3. **Embedding.** There is an injective homomorphism `PGL_2(Q) -> V_p(Γ_p)`.
   It is induced by the Möbius action of `PGL_2(Q) <= PGL_2(Q_p)` on
   `P^1(Q_p) = Z_p ⊔ D_∞`, where `D_∞ = {|z|_p >= p} ∪ {∞}`, with charts
   `φ_0 = id` on `Z_p` and `φ_∞(u) = 1/(pu)` on `D_∞`, followed by placing the two
   charts on the cones `0 + pZ_p` and `1 + pZ_p`. In particular
   `(Q,+) <= PGL_2(Q) <= V_p(Γ_p)`: the level shifts of `V_p` supply
   `p`-divisibility, and `Γ_p ⊇ Z_(p)` (translations) supplies the rest.
4. **Size.** `Γ_p` is not finitely generated. It is not finite-state: the
   element `u ↦ u/(1+pu)` has infinitely many distinct sections. So `Γ_p` lies
   in no contracting self-similar group, and Nekrashevych's finite-presentation
   theorem (FP2 of `rover-nekrashevych-finite-presentation-criteria`) cannot be
   applied to any self-similar overgroup of `Γ_p`.
5. **Limits of the device.**
   - (a) Every homomorphism from `SL_2(Q)` to `PGL_2(K)`, for any field `K`,
     kills `-I`. So `SL_2(Q)` and `GL_2(Q)` embed in no product of groups
     `PGL_2(K_j)`. The Möbius device gives `PSL_2(Q) <= PGL_2(Q)` and nothing
     larger in `GL_2(Q)`.
   - (b) For `n >= 3`, `diag(1, ..., 1, p) ∈ GL_n(Q)` acts on `P^{n-1}(Q_p)` by a
     homeomorphism that is **not** an almost automorphism of the tree of balls.
     So the device does not extend through projective spaces.

## Use

`psl2-q-fp-simple-via-rational-iwahori-rn-host` turns item 3 into a conditional
route to `psl2-q-embeds-in-fp-simple-group`. Its one open input is
`rational-iwahori-group-lies-in-fp-self-similar-group`: some finitely presented
self-similar group containing `Γ_p` whose Röver–Nekrashevych group has finite
abelianization.
