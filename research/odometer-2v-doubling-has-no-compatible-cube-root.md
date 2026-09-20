---
rg: 2
id: odometer-2v-doubling-has-no-compatible-cube-root
kind: claim
title: In the odometer host 2V_τ no cube root r of s = τ × id satisfies u r u^-1 = r^2, so its Baumslag–Solitar pair ⟨s, u⟩ extends to no Z[1/6] ⋊ ⟨2⟩ and to no Q ⋊ ⟨2⟩; the centralizer of s is LC(C, Z) ⋊ V
distinct_from:
  odometer-2v-is-fp-simple-and-contains-bs12: that builds the host 2V_τ, its BS(1,2) = ⟨s, u⟩ and a copy Q_τ of Q containing s, and leaves open whether u normalizes Q_τ; this shows that u normalizes no divisible extension of ⟨s⟩ at all, not even one cube root.
  affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q: that puts Z[1/2N] ⋊ ⟨2⟩ into the hosts 2V_(G_N) and excludes the natural Q ⋊ ⟨2⟩ from 2V_H for finitely generated affine H; this is the odometer host 2V_τ, where even Z[1/6] ⋊ ⟨2⟩ fails over the given pair.
  t-check-contains-no-q-rtimes-2-z: that excludes Q ⋊ ⟨2⟩ from T-check by boundary arithmetic in one real coordinate; here the dilation mixes two Cantor coordinates, and the obstruction comes from the centralizer of s being fibred over one coordinate with integer fibre translations.
---

**ESTABLISHED** by `odometer-2v-doubling-has-no-compatible-cube-root-proof` (lane bh-glnq-fresh,
2026-09-19). Elementary. Lane proof, not independently reviewed. No priority claimed.

## Why it matters

`Q ⋊ ⟨2⟩ = {x ↦ 2^k x + q}` is the first rung of the ladder
`Q ⋊ ⟨2⟩ → Q ⋊ Z^k → Aff(Q)` toward the stepping stone `aff-q-embeds-in-fp-simple-group` of
`gl-n-q-embeds-in-fp-simple-group`. It joins the two ingredients the critic rules ask for:
divisibility (`Q`) and the dilation that distorts it. The host `2V_τ` of
`odometer-2v-is-fp-simple-and-contains-bs12` is finitely presented, simple and `F_∞`, and it contains
both `Q` and `BS(1,2) = ⟨s, u⟩`. What was open is whether the doubling `u` normalizes a divisible
group containing `s`. It does not, and the reason is structural.

## Setting

`C = {0,1}^N`, `X = C × C`, `τ` the binary odometer, `s = τ × id`, and `u(x, y_0 y) = (y_0 x, y)`,
so `u s u^-1 = s^2`. Elements of `2V_τ` are the homeomorphisms of `X` of the form
`(p x, w y) ↦ (p' τ^n x, w' y)` on the rectangles of a finite partition.

## Theorem

1. **Centralizer.** `C_{2V_τ}(s)` consists of the maps `(x, y) ↦ (τ^{c(y)} x, v(y))` with `v ∈ V`
   acting on the second coordinate and `c : C → Z` locally constant. So
   `C_{2V_τ}(s) ≅ LC(C, Z) ⋊ V`.
2. **No compatible cube root.** No `r ∈ 2V_τ` satisfies `r^3 = s` and `u r u^-1 = r^2`.
3. **Consequence.** `u` normalizes no subgroup `A ≤ 2V_τ` with `s ∈ A` and `A` isomorphic to a
   subgroup of `(Q, +)` in which `s` is divisible by `3`, for instance `A ≅ Z[1/6]` or `A ≅ Q`.
   Conjugation by `u` would act on `A` as multiplication by `2`, because `u s u^-1 = s^2`. So
   `⟨s, u⟩` extends to no `Z[1/6] ⋊ ⟨2⟩` and no `Q ⋊ ⟨2⟩` in `2V_τ`, and `u` does not normalize the
   tower `Q_τ` of the host node.
4. **The general doubling conjugator.** Every `t ∈ 2V_τ` with `t s t^-1 = s^2` has the form `t = u g`
   with `g ∈ C(s)`. So **some** doubling conjugator `t` of `s` admits a cube root `r` of `s` with
   `t r t^-1 = r^2` iff some cube root `r` of `s` is conjugate in `C(s) ≅ LC(C, Z) ⋊ V` to
   `u^-1 r^2 u` (wording fixed by bh-ref-t0).
5. **Single roots: yes.** For every `m ≥ 1` and every `r ∈ 2V_τ` with `r^m = s`, the roots `r` and
   `u^-1 r^2 u` are conjugate in `C(s)`. So each single root `r` has its own doubling conjugator
   `t_r = u g_r` with `t_r r t_r^-1 = r^2`. The obstruction of item 2 is specific to `t = u`.
6. **Towers through the host's dyadic tower: no.** Let `S_2 = ⟨u^-j s u^j : j ≥ 0⟩ ≅ Z[1/2]`, the
   normal closure of `s` in `⟨s, u⟩ ≅ BS(1,2)`. Then `C_{2V_τ}(S_2) = S_2`. Hence every `t` that acts
   on `S_2` as multiplication by `2` lies in `u S_2`, and acts on every abelian `A ⊇ S_2` exactly as
   `u` does. By item 2, no `A ≅ Z[1/6]` or `A ≅ Q` with `S_2 ≤ A` is normalized by any element
   acting as `×2`. So `2V_τ` contains no `Q ⋊ ⟨2⟩` and no `Z[1/6] ⋊ ⟨2⟩` extending the host's
   `S_2 ⋊ ⟨u⟩ = BS(1,2)`.
7. **Still open.** Copies of `Q ⋊ ⟨2⟩` whose square-root tower of `s` is not conjugate in `C(s)` to
   `S_2`, and copies based at elements other than `s`. A possible invariant separating towers is
   the unique invariant measure of the tower's `y`-action: `S_2` gives dyadic cone masses.

## Mechanism

- In the bi-infinite coding `X ≅ {0,1}^Z` (the separator between `y` and `x`), `u` is the shift and
  `s` adds `1` with carries to the right. So `⟨s, u⟩` is the natural affine action of
  `Z[1/2] ⋊ ⟨2⟩`, and all of `Q_2 ⋊ ⟨2⟩` acts on `X` the same way. The natural cube root is
  `x ↦ x + 1/3`, which lies in `Homeo(X)` but not in `2V_τ`.
- Inside `2V_τ` the fibre translations of `C(s)` are integers, not `2`-adic integers. The equation
  `u r u^-1 = r^2` becomes a two-state carry recursion for the integer cocycle of `r`. Along the
  point `(10)^∞`, the `2`-adic digit pattern of `1/3`, it never terminates, so the cocycle cannot be
  locally constant.

## Lesson for general BH

Mixing coordinates does not by itself escape single-radix boundary arithmetic
(`t-check-contains-no-q-rtimes-2-z`). What decides is the centralizer of the divisible element. Here
it is fibred over one coordinate with integer translations along the other, so every root of `s`
lives in a `Z ≀ V`-type group, and the doubling forces a non-terminating carry.
- A host for `Q ⋊ ⟨2⟩` needs a divisible element whose centralizer is not of this fibred-integer
  form: for instance a base with `Z_(2)`-valued fibre translations, or a base that is not an odometer.
- Otherwise it needs a doubling that conjugates roots nontrivially inside the centralizer. Items 5–6
  show this works root by root but not along the host's own dyadic tower, whose centralizer is
  itself.

## Next host

The rule above points past `2V_τ` to a Katsura–Exel–Pardo host `2V_H` whose colour-1 group `H` is
finitely generated, self-similar and non-affine, and contains a copy of `Z_(2)` along which the
doubling acts. The affine hosts `2V_(G_N)` reach only `Z[1/2N] ⋊ ⟨2⟩`, by bounded denominators
(`affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q`). A finite-state `H` meets the constraints of
`contracting-groups-bound-roots-at-periodic-points` and the "exotic odometer" requirement for
`Z_(S)` in automaton groups. This is the open item "non-affine coefficient groups containing
`Z_(2)`" of `aff-q-embeds-in-fp-simple-group`, Attempt 9. The `2`-adic analogue of the rational
Iwahori input (`rational-iwahori-group-lies-in-fp-self-similar-group`) is one candidate source for
such an `H`.
