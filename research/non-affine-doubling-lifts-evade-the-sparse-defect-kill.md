---
rg: 2
id: non-affine-doubling-lifts-evade-the-sparse-defect-kill
kind: claim
title: The sparse-defect kill of PL germ realizations of the Baumslag-Solitar chain holds exactly on the PL-conjugacy class of affine doubling; for a non-affine dyadic PL doubling lift the square map bends densely and the defect relations w_k survive, so the faithful-germ route to G_1 in B_A reduces to three prerequisites that can each fail
artifacts:
  - experiments/non-affine-doubling-lift-2026-09-17/fast.py
  - experiments/non-affine-doubling-lift-2026-09-17/overlap.py
  - experiments/non-affine-doubling-lift-2026-09-17/breakgaps.py
  - experiments/non-affine-doubling-lift-2026-09-17/out_overlap_5.txt
  - experiments/non-affine-doubling-lift-2026-09-17/out_overlap_6.txt
  - experiments/non-affine-doubling-lift-2026-09-17/out_overlap_7.txt
  - experiments/non-affine-doubling-lift-2026-09-17/out_overlap_8.txt
  - experiments/non-affine-doubling-lift-2026-09-17/out_breakgaps.txt
  - experiments/non-affine-doubling-lift-2026-09-17/germs.py
  - experiments/non-affine-doubling-lift-2026-09-17/scan.py
  - experiments/non-affine-doubling-lift-2026-09-17/support.py
  - experiments/non-affine-doubling-lift-2026-09-17/rgerm.py
distinct_from:
  scale-periodic-bs-chain-germ-representations-are-not-faithful: that kills w_k when the dilation is exactly δ = 2x, and its Lesson asserts that no PL germ host realizes the tower faithfully; this extends the kill to every δ PL-conjugate to affine doubling, shows that the class is exactly where its mechanism (sparse bends of s) works, and exhibits a dyadic PL δ outside the class where s bends densely and every w_k tested survives, so the general Lesson is unproved.
  pl-chain-germ-group-contains-thompson-f: that studies the germ group for δ = 2x and the odd square map, where the kill applies; this changes δ itself, which changes the germ group.
  bs-chain-configurations-exist-in-finite-germ-extensions-of-v: that builds the host with the affine dilation b = 2x; this shows the same construction works with any dyadic PL doubling lift in place of b, and that the choice of lift decides whether the kill applies.
---

**OPEN.** Lemmas 1–5 below have complete elementary proofs (lane proofs, not reviewed; no priority
claimed). The statement itself (survival of every `w_k` as a germ at `+∞`) is supported by exact
computation at four consecutive scales (5–8) and is not proved.

## Setting

Germs at `+∞` of increasing homeomorphisms of the line, as in
`scale-periodic-bs-chain-germ-representations-are-not-faithful` (the *kill node* below).
- `σ(x) = x + 1`.
- `δ` is a **doubling lift**: an increasing PL homeomorphism of `R` with `δ(x + 1) = δ(x) + 2`, that is
  `δ σ δ^-1 = σ^2`. Equivalently `δ` is the lift of a PL degree-2 circle covering `f`.
- `s` is a PL germ with discrete breakpoints and `s δ s^-1 = δ^2`.
- `G_1 = ⟨s, δ, σ | s δ s^-1 = δ^2, δ σ δ^-1 = σ^2⟩`, `θ : G_1 -> Q = ⟨σ, δ, s⟩` the germ map,
  `τ = s^-1 σ s`, `c_1 = [τ, σ]`, `w_k = [c_1, σ^k c_1 σ^-k]`.

**The example.** `δ_f(n + r) = 2n + d(r)` for `n ∈ Z`, `r ∈ [0,1)`, where `d` is PL with
- slope 1 on `[0, 1/2)`, slope 2 on `[1/2, 3/4)`, slope 4 on `[3/4, 1)`;
- `d(0) = 1/2`, `d(1/2) = 1`, `d(3/4) = 3/2`, `d(1) = 5/2`.

So `f(r) = d(r) mod 1` is a dyadic PL degree-2 circle map. Put `X = 4`, so `δ_f(X) = 17/2` and
`δ_f^2(16) = 65`. The fundamental-domain map `s_0 : [4, 17/2) -> [16, 65)` is dyadic PL with
- slope 8 on `[4, 8)` (onto `[16, 48)`),
- slope 4 on `[8, 33/4)` (onto `[48, 49)`),
- slope 64 on `[33/4, 17/2)` (onto `[49, 65)`).

The square map is `s(δ_f^n x) = δ_f^(2n) s_0(x)` for `x ∈ [4, 17/2)` and `n ≥ 0`.

## Statement

For the example, `θ(w_k) ≠ 1` for every `k ≥ 1`. That is, for every `k`, the support of `w_k` is
unbounded above.

## Lemma 1: every doubling lift carries a dyadic square map

For any doubling lift `δ`, any `X`, and any increasing PL bijection `s_0 : [X, δX) -> [Y, δ^2 Y)`, the
formula `s(δ^n x) = δ^(2n) s_0(x)` (`x ∈ [X, δX)`, `n ≥ 0`) defines an increasing homeomorphism
`s : [X, ∞) -> [Y, ∞)` with `s δ = δ^2 s`. It is PL with finitely many breakpoints on every compact set,
and it is dyadic PL if `δ` and `s_0` are.

*Proof.* The windows `W_n = δ^n [X, δX)` tile `[X, ∞)`, and their images `δ^(2n)[Y, δ^2 Y)` tile
`[Y, ∞)`. On `W_n`, `s = δ^(2n) s_0 δ^-n` is a composition of finitely many PL maps. For `x ∈ W_n`,
`δx ∈ W_(n+1)` and `s(δx) = δ^(2n+2) s_0 δ^-n x = δ^2 s(x)`. ∎

## Lemma 2: the kill extends to the PL-conjugacy class of affine doubling

Suppose the circle map `f` of `δ` is conjugate to `z ↦ 2z` by a PL circle homeomorphism (finitely many
pieces, any slopes). Then for every `s` as in the Setting there is `k_0` such that `θ(w_k) = 1` for all
`k ≥ k_0`, while `w_k ≠ 1` in `G_1` for `k ≥ 2`.

*Proof.* Lift the circle conjugacy to a PL homeomorphism `h` of `R` with `h(x + 1) = h(x) + 1`. Then
`h δ h^-1` is a lift of `z ↦ 2z`, so it is `x ↦ 2x + m` for an integer `m`. Replace `h` by `T_m h`, where
`T_m(x) = x + m`. Since `T_m` commutes with `σ`, this gives `h σ h^-1 = σ` and `h δ h^-1 = (x ↦ 2x)`.

Put `s' = h s h^-1`. It is PL with discrete breakpoints and `s'(2x) = 4 s'(x)`. Conjugation by `h` is
an isomorphism of germ groups at `+∞`, and it carries the germ representation for `(σ, δ, s)` to the one
for `(σ, 2x, s')`. So the two representations have the same kernel.

The proof in the kill node uses only three facts about `s'`: it is PL with finitely many breakpoints on
`[X, 2X)`, it has a positive least slope there, and `s'(2x) = 4 s'(x)`. Dyadic slopes are never used. So
that proof applies to `s'` verbatim and gives `w_k ∈ ker θ` for `k ≥ k_0`. Nontriviality in `G_1` is the
normal-form argument of the kill node, which does not involve the representation. ∎

## Lemma 3: a PL-conjugacy obstruction, and the example is outside the class

If `f` is conjugate to `z ↦ 2z` by a PL circle homeomorphism `ĥ`, then at every periodic point `p` of
`f` of period `q`, both one-sided derivatives of `f^q` at `p` equal `2^q`.

*Proof.* `f^q = ĥ^-1 D^q ĥ`, where `D(z) = 2z`, and `ĥ p` is fixed by `D^q`. By the chain rule for
one-sided derivatives of orientation-preserving PL maps,
`(f^q)'_±(p) = (ĥ^-1)'_±(ĥ p) · 2^q · ĥ'_±(p) = 2^q`. ∎

For the example: `f(5/6) = 3/2 + 4(5/6 - 3/4) = 11/6 ≡ 5/6`, so `5/6` is a fixed point with multiplier
`4 ≠ 2`. So the example is not PL-conjugate to doubling, and Lemma 2 does not apply to it. (The
period-2 orbit `{0, 1/2}` also fails: `(f^2)'_+(0) = 1 · 2 = 2 ≠ 4`.)

## Lemma 4: non-affine lifts must contract somewhere

If a PL doubling lift has all slopes `≥ 2`, it is affine, `δ(x) = 2x + c`. So every non-affine dyadic PL
doubling lift has a piece of slope `≤ 1`.

*Proof.* `∫_0^1 δ' = δ(1) - δ(0) = 2`. With `δ' ≥ 2` almost everywhere, this forces `δ' = 2` almost
everywhere. Dyadic slopes below 2 are at most 1. ∎

This is why the example has a slope-1 piece. Non-affine lifts are not expanding at the first step, only
after iterating: the slopes of `f^2` are at least 2.

## Lemma 5: bulk periodicity (used by the computation)

In the example, `s_0` is affine of slope 8 on `[4, 8)`. So for `z, z + 1 ∈ [4, 8)` and every `n`,
`s(δ^n(z + 1)) = δ^(2n)(s_0 z + 8) = s(δ^n z) + 8 · 4^n`, because `δ^m(y + j) = δ^m(y) + 2^m j`. So on
the bulk `δ^n [4, 7)`, `s` intertwines `T_(2^n)` with `T_(8·4^n)`. Hence `τ`, `c_1` and every `w_k`
commute with `T_(2^n)` wherever both sides stay in the bulk. So the germ picture at scale `n` is
`2^n`-periodic there, and one period `[P_n, P_n + 2^n)`, with `P_n = δ^n(5)`, is a certificate for the
whole bulk of that scale. ∎

## Evidence for the Statement (exact computation)

`fast.py` evaluates right germs (value, slope exponent, extent of the affine piece) of every word
exactly, in dyadic fixed point with `2^-400` resolution. Every division is asserted exact, and any
extent underflow aborts. Walking `x -> x + extent` therefore lists every affine piece of a word on a
window **exactly**. The affine control `δ = 2x` reproduces the kill node: `c_1` has no support in the
bulk windows, and every `w_k` is the identity there.

**The mechanism of the kill fails.** The kill needs the gaps between consecutive bends of `s` to tend to
infinity. For `δ = 2x` they grow like `2^n` (one bend per window). For the example (`out_breakgaps.txt`),
on the windows `W_n = δ_f^n [4, 17/2)`:

| n | length of `W_n` | bends of `s` | largest gap between bends |
|---|---|---|---|
| 3 | 34.5 | 4259 | 0.25 |
| 5 | 138.5 | 68218 | 0.125 |
| 6 | 277.5 | 272815 | 0.09375 |
| 7 | 554.5 | 1091315 | 0.0625 |

So the bends multiply by about 4 per window, which is faster than the window length, and the largest gap
shrinks. The bends of `s` are dense at the scale of `σ`, not sparse.

**The relations survive at every tested scale.** For one bulk period at δ-scale `n`, `overlap.py` does
three things. It computes the exact support of `c_1`, padded by `k_max + 4`. It computes the overlaps of
that support with its translate by `k`. Then it computes the exact support of `w_k` on those overlaps.
If the supports were disjoint, `w_k` would be the identity; outside the overlaps it is the identity
anyway. Results (`out_overlap_5.txt`, `_6`, `_7`, `_8`):

| scale n | period | comps of supp c_1 / period | measure | k tested | w_k nontrivial for |
|---|---|---|---|---|---|
| 5 | [170.5, 202.5) | 26 | 16.83 | 1–16 | **all** k |
| 6 | [341, 405) | 38 | 22.53 | 1–16 | **all** k |
| 7 | [682.5, 810.5) | 53 | 27.52 | 1–9 | **all** k |
| 8 | [1365, 1621) | 63 | 32.84 | 1–3 | **all** k |

For `k = 1`, `w_1` moves measure 3.09, 2.29, 1.59 and 1.19 per period at scales 5, 6, 7 and 8, in 93,
120, 138 and 154 components. So the moved set shrinks by a factor of about 0.7 per scale, while the number of moved
components grows. Every other `k` behaves the same way.

## Why the Statement is still OPEN

The computation certifies `w_k ≠ id` on bounded windows only. A germ statement needs every large scale.
The number of moved components is growing, which is the signature of survival rather than decay. But no
renormalization argument yet links scale `n` to scale `n + 1`.

The natural one is this. At scale `n`, pulled back by `δ^n`, `σ` becomes `r_n = δ^-n σ δ^n`, a
`2^n`-th root of `σ` (`r_n^(2^n) = σ`). In the bulk, `c_1` becomes `[D_8^-1 r_(2n) D_8, r_n]`. In the
topological linearization `u` of `f` (`δ -> 2u`), `r_n` is the translation by `2^-n`. That
linearization exists because `f^2` is uniformly expanding. But it is not PL (Lemma 3), and it is not
even Lipschitz. At the fixed point `5/6`, `u(p + 4t) - u(p) = 2(u(p + t) - u(p))`, so the increment
grows like `t^(1/2)`. So the limit pictures are genuinely singular.

## Decomposition of the faithful-germ route

The route: certify `G_1 ∈ B_A` through a finite germ extension of `V` whose germ group at `+∞` is `G_1`
itself. Then finite presentation of `Q` is free, and `bhm-singfix-condition-forces-fp-germ-groups`
reduces the host to the remaining BHM conditions. It splits into three prerequisites, each of which can
fail.

- **P0 (necessary, now proved).** `δ` is **not** PL-conjugate to affine doubling. This follows from
  Lemma 2, which rules out `δ = 2x` and every PL conjugate of it. Lemma 3 gives a checkable sufficient
  condition for P0: one periodic orbit of period `q` with a one-sided multiplier other than `2^q`.
- **P1 (open).** For some non-affine dyadic PL doubling lift `δ` and some `s` from Lemma 1, the germ
  representation `θ` is faithful. The Statement is the first test of P1: the known kernel elements
  survive. P1 fails if some *other* commutator of far-apart elements dies. The only mechanism known to
  produce such deaths is sparse support, and it is absent here.
- **P2 (plausible, not checked in full).** The host `⟨V, b_f, a_f⟩` is a finite germ extension of `V`
  whose only other singular germ group is harmless. Here `b_f = δ_f`, and `a_f` equals `s` near `+∞` and
  a translation by `Y - X = 12` near `-∞`.
  - Both maps are dyadic PL with bends accumulating only at `±∞`, so the local-form argument of
    `bs-chain-configurations-exist-in-finite-germ-extensions-of-v` applies.
  - At `-∞` the germ group is `⟨σ, δ_f⟩`. This is a quotient of `BS(1,2)` with base of infinite order,
    hence `BS(1,2)`, which is finitely presented.
  - What remains is the full BHM Theorem 2.1 check, as for the affine host.

If P1 fails for every non-affine lift, the Lesson of the kill node becomes true in general. If it holds
for one lift, the finite-presentation problem for `Q` disappears on that route.

## Lesson

The kill of PL germ realizations is a statement about the **conjugacy class of the middle level**, not
about PL towers in general. Bends of the square map are sparse exactly when the dilation is PL-rigid
(affine up to PL conjugacy). A dilation with a "wrong" multiplier at one periodic point forces the
square map to bend at every dyadic place, on every scale. Then far-apart defects overlap and stop
commuting.

## Attempts

- **2026-09-19, swarm-0917-w16-w16-bh-follow.** Found Lemmas 1–5, the example, and the exact
  computations at scales 5–8. An attempted renormalization proof of the Statement stalled at the
  non-Lipschitz linearization.
- **2026-09-19, swarm-0917-w17-w17-bh-follow.** Attacked P1 through invariants of `G_1`, recorded in
  `chain-group-abelian-rank-firewall-for-germ-hosts` (proof `chain-group-abelian-rank-firewall-proof`).
  - *Firewall (proved).* Every abelian subgroup of `G_1` is locally cyclic or `Z^2`, and
    `C(σ) = N_B`. `⟨σ, ρσρ^-1⟩` and `⟨σ, τ⟩` are free. So a faithful `θ` needs:
    - (F1) no germ of sparse support, and no `Z^3` or `F` in `Q`;
    - (F2) σ-periodic germs lie in `θ(N_B)`;
    - (F3) `⟨θρ, σ⟩` is not soluble.
  - *Kill of the smooth model (proved).* The square map `x^2` in the linearizing chart of `δ_f` dies at
    F3, since `ρ_meta` maps to 1.
  - *Computation.* For this node's PL `s`, `ρ_meta` moves the whole bulk period at scales 3, 5 and 6,
    and `τ_meta` survives, so F3 is passed as far as tested. F1 as stated is exactly the negation of the
    known kill mechanism. The claim that no *other* mechanism exists is still unproved. That is the
    whole of P1.
  - *P2 correction (proved).* With `a_f = T_12` near `-∞`, `a_f b_f a_f^-1 ≠ b_f^2`. The fix is a global
    dyadic square map `s_f`: it equals `s` on `[4, ∞)`, is extended through the unique fixed point
    `x_0 = -1/6` of `δ_f` (slope 4), and is generated by `2x + 1/2` on `[-1, -1/2)`. This gives a third
    singular orbit with germ group `BS(1,2)`, and `Q_-` is a second `G_1`-quotient. So P1 is needed at
    both ends. P1 stays OPEN.
