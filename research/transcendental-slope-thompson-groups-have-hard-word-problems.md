---
rg: 2
id: transcendental-slope-thompson-groups-have-hard-word-problems
kind: claim
title: A rotation commutator in D(V_λ) reads off the Sturmian word of λ, so for every recursive time bound some computable Liouville slope λ gives a 2-generated simple D(V_λ) with solvable word problem beyond that bound
distinct_from:
  stein-derived-groups-need-computable-modules: that shows the word problem of D(V_λ) is unsolvable when λ is noncomputable, via Grigorchuk--Medynets; this is the quantitative version for computable λ, by an explicit length-linear detector that needs no Grigorchuk--Medynets input.
  fp-pl-groups-with-f-have-no-transcendental-support-endpoints: that shows PL groups with hard transcendental data are never finitely presented (so they are not hosts); this shows their finitely presented simple overgroups, if any, inherit the hardness. D(V_λ) contains no dyadic F, so the F-bump detector used there is not available; a rotation replaces it.
  transcendental-slope-thompson-groups-satisfy-boone-higman: that is the open embedding question; this proves that its positive solution for all computable transcendental λ would settle the Birget root.
---

**ESTABLISHED** (lane proof, elementary, not reviewed). No priority is claimed. Finitely generated
simple groups with solvable word problem of arbitrarily high complexity are not new in themselves,
for example derived full groups of minimal subshifts with hard languages. The content here is that
the irrational-slope Thompson groups are such groups, and what that implies for their Boone--Higman
question.

## Setting

`λ ∈ (0,1)` is transcendental, `A = Z[λ,λ^{-1}] ⊂ R`, and `V_λ = V(A, ⟨λ⟩, 1)` is the group of
right-continuous PL bijections of `[0,1)` with slopes in `⟨λ⟩` and finitely many breakpoints, all
in `A` (Stein; Tanner, arXiv:2312.07375). `D(V_λ)` is its derived subgroup, 2-generated and simple
(Tanner). Commutators are `[g,h] = g h g^{-1} h^{-1}`. The characteristic Sturmian word of `λ` is
`c_λ(n) = ⌊(n+1)λ⌋ − ⌊nλ⌋ ∈ {0,1}`, `n >= 0`.

A word problem is *T-bounded* if, for some finite generating set, it has an algorithm running in
time `C·T(C·l) + C·l + C` on words of length `l`, for some constant `C`. For nondecreasing `T` this is
independent of the generating set and is the notion of `fp-simple-groups-with-arbitrarily-complex-word-problem`.

## Statement

1. **Sturmian detector.** There are `u', w', ρ ∈ D(V_λ)` such that for every `n >= 0`,

       [u', ρ^n w' ρ^{-n}] = 1   iff   c_λ(n) = 0.

2. **Hard slopes.** For every recursive `T` there is a computable Liouville number
   `λ ∈ (1/4, 3/4)` such that `D(V_λ)` has solvable word problem that is not `T`-bounded.
3. **Calibration.** If `transcendental-slope-thompson-groups-satisfy-boone-higman` holds, then
   so does `fp-simple-groups-with-arbitrarily-complex-word-problem`. Indeed, a finitely presented
   simple group containing `D(V_λ)` for the `λ` of item 2 (built from `T^+(m) = m + max_{k<=m} T(k)`)
   has a word problem that is not `T`-bounded (route
   `arbitrarily-complex-fp-simple-via-transcendental-slope-thompson`).

## Proof of 1

Fix integers `j, k >= 1` with `λ^j <= 1/3` and `λ^k <= 1/4`. Put

    b = λ^j,   α = λb,   ε = λ^k α,   y = b − α,   c' = y + ε.

All are in `A`, `0 < ε <= α/4`, and `0 < y < c' <= b − ε` (the last because `2ε <= α`).

**Bumps.** For `p < q` in `A` and `δ ∈ A` with `0 < (1+λ)δ <= q − p`, let `B(p,q;δ)` have slope `λ`
on `[p,p+δ)`, slope `1` on `[p+δ, q−λδ)`, slope `λ^{-1}` on `[q−λδ, q)`, and be the identity
elsewhere. It is continuous: `p+δ ↦ p+λδ`, the middle piece is `x ↦ x − (1−λ)δ`, and
`q−λδ ↦ q−δ`, `q ↦ q`. Its breakpoints are in `A` and its slopes in `⟨λ⟩`. It moves every point of
`(p,q)` strictly down and fixes everything else. Put `u = B(c', b; λ^k α)` and `w = B(0, ε; λ^k ε)`.
The size conditions hold because `λ^k(1+λ) < 1/2` and `α − ε >= 3α/4`.

**Rotation.** Let `R` be the rotation of `[0,b)` by `α`: `z ↦ z+α` on `[0, b−α)` and
`z ↦ z+α−b` on `[b−α, b)`. Regard `[0,b)` as the circle `C_b = R/bZ`. Then `R` is a rotation of
`C_b`, while `u` and `w` are homeomorphisms of `C_b` supported on the arcs `(c', b)` and `(0, ε)`.

**Into the derived subgroup.** For `h` supported in `[0,b)` and `s ∈ {1, 2}`, let
`h ⊕_s h^{-1}` be `h` on `[0,b)` together with the translate of `h^{-1}` to `[sb, (s+1)b)`. Let
`σ_s ∈ V_λ` swap `[0,b)` and `[sb,(s+1)b)` by translations. Then `[h, σ_s] = h ⊕_s h^{-1}`, so these
elements lie in `D(V_λ)` (`3b <= 1`). Put

    ρ = R ⊕_1 R^{-1},   u' = u ⊕_2 u^{-1},   w' = w ⊕_2 w^{-1}.

`ρ` acts only on `[0,2b)`. So `ρ^n w' ρ^{-n}` is `v_n := R^n w R^{-n}` on `[0,b)`, together with the
copy of `w^{-1}` on `[2b,3b)`. On `[2b,3b)` the copies of `u^{-1}` and `w^{-1}` have disjoint
supports `(2b+c', 3b)` and `(2b, 2b+ε)`, so

    [u', ρ^n w' ρ^{-n}] = 1   iff   [u, v_n] = 1   (as maps of C_b).

**Case analysis.** `v_n` is a homeomorphism of `C_b` supported on the arc `(x_n, x_n+ε)` (mod `b`),
where `x_n = nα mod b = b{nλ}`. It moves every point of that arc.
- If `x_n ∈ [0, y]`, the arcs `(x_n, x_n+ε) ⊆ [0, c']` and `(c', b)` are disjoint, so `u` and `v_n`
  commute.
- If `x_n ∈ (y, c')`, the arc of `v_n` contains `c'`. If `x_n ∈ (b−ε, b)`, it contains `0 ≡ b`.
  In both cases, if `[u, v_n] = 1` then `v_n` maps the arc `(c', b)` of `u` onto itself. An
  orientation-preserving circle homeomorphism mapping an arc onto itself fixes both endpoints, but
  `v_n` moves `c'` (first case) or `0` (second case).
- If `x_n ∈ [c', b−ε]`, the arc of `v_n` lies in `(c', b)`. If `[u, v_n] = 1` then `u` maps it onto
  itself and so fixes `x_n` and `x_n + ε`. At least one of these lies in `(c', b)`, where `u` moves
  every point.

These cases cover `[0,b)`, because `y < c' <= b − ε`. So `[u, v_n] = 1` iff `{nλ} <= 1 − λ`.
Equality is impossible: for `n = 0` since `λ < 1`, and for `n >= 1` since `(n+1)λ ∉ Z`. Finally,
`{nλ} < 1 − λ` iff `⌊(n+1)λ⌋ = ⌊nλ⌋` iff `c_λ(n) = 0`. ∎

*Aside.* Since `⌊Nλ⌋ = Σ_{n<N} c_λ(n)`, item 1 gives `λ ≤_T WP(D(V_λ))` directly. So it reproves
item 2 of `stein-derived-groups-need-computable-modules` for `V_λ` without Grigorchuk--Medynets.

## Proof of 2

Let `T` be recursive; replacing it by `T^+`, assume `T` is nondecreasing with `T(m) >= m`.
Put `M_k = 2^{(k+1)!}` and `E(k) = (k·M_k·T(k·M_k))^2 + M_k^3`, a recursive function.

**A hard set.** Enumerate Turing machines so that each occurs as `M_{π(k)}` for infinitely many
`k`. Let `S` be the set of `k` such that `M_{π(k)}` on input `k` does not halt with output `1`
within `E(k)` steps. Then `S` is decidable. No machine decides `S` within `E(k)` steps for all
large `k`: on a large `k` with `π(k)` equal to that machine, its answer would contradict the
definition of `S`.

**The slope.** Put `s_i = χ_S(i)` and `λ = Σ_{i>=1} (1 + s_i) 2^{-(i+1)!}`.
- `λ ∈ (1/4, 3/4)`, and its binary digits are computable from `S`, so `λ` is computable.
- The partial sums `p_k / 2^{(k+1)!}` satisfy `0 < λ − p_k/2^{(k+1)!} <= 4·2^{-(k+2)!}`. So `λ` is a
  Liouville number, hence transcendental.
- `D(V_λ)` therefore has solvable word problem, by the lane argument in
  `transcendental-slope-thompson-groups-satisfy-boone-higman`: comparisons `p(λ) < q(λ)` are
  decidable because `p(λ) ≠ q(λ)` for `p ≠ q`.

**Decoding.** Write `M_k λ = M_k P_{k−1} + (1 + s_k) + M_k τ_k`. Here `P_{k−1}` is the sum of the
terms with `i < k`, so `M_k P_{k−1} ∈ 2Z`. The tail satisfies `0 < M_k τ_k <= 4·2^{-(k+1)(k+1)!} <= 1/4`.
Hence `⌊M_k λ⌋ = M_k P_{k−1} + 1 + s_k`, and `s_k ≡ ⌊M_k λ⌋ + 1 (mod 2)`, with
`⌊M_k λ⌋ = Σ_{n<M_k} c_λ(n)`.

**Contradiction.** Suppose the word problem of `D(V_λ)` over a finite generating set `Σ` were
`T`-bounded with constant `C`. Write `u', w', ρ` as fixed words of length `<= K` over `Σ`. The word
`[u', ρ^n w' ρ^{-n}]` has length `<= K(4n+4)` and is written down in time `O(Kn)`. By item 1, `s_k`
is then computable on input `k` in time

    <= M_k · (C·T(8CK·M_k) + 8CK·M_k + C) + O(M_k^2),

including the running sum. For all large `k` (in particular `k >= 8CK`) this is `<= E(k)`, by
monotonicity and `T(m) >= m`; the square in `E` absorbs the overhead of composing machines. This
contradicts the choice of `S`. ∎

## Proof of 3

Let `D(V_λ) ≤ G` with `G` finitely presented and simple, and `λ` as in item 2 for `T^+`. Each
generator of `D(V_λ)` is a fixed word in the generators of `G`. So a `T^+`-bounded word problem for
`G` would give one for `D(V_λ)`, by the length-linear substitution of
`complexity-bounded-host-classes-are-not-universal-proof` (monotonicity of `T^+` absorbs the
constant). This contradicts item 2. So `G` is not `T^+`-bounded, hence not `T`-bounded. ∎

## What this says about the Boone--Higman test case

- **The general case.** A positive answer to `transcendental-slope-thompson-groups-satisfy-boone-higman`
  for all computable transcendental `λ` would produce finitely presented simple groups beyond every
  recursive bound. That is the Birget root, which is open. The host must consume the algorithm
  computing `λ`, as `compilers-cannot-drop-the-decidability-hypothesis` predicts. This is consistent
  with `fp-pl-groups-with-f-have-no-transcendental-support-endpoints`: PL groups carrying `λ` are never
  finitely presented, and any host must encode the digits by computation.
- **Specific slopes.** Items 2–3 say nothing about `λ = 1/e` or `λ = π − 3`, whose digits are cheap.
  There the question remains a clean test of whether transcendental PL data can sit inside a
  finitely presented simple group.
