---
rg: 2
id: thompson-f-one-sided-forest-windows-are-norm-lossless
kind: claim
title: The pointed-forest windows S_n lose nothing for the norm of Thompson's F - the top eigenvalue of the move graph on S_n increases to 4||P||, so F is amenable iff it tends to 4
distinct_from:
  thompson-f-norm-bound-from-forest-renewal-test-vector: that certifies one lower bound (||P|| > 0.9397) with a product-form vector on E(S_n); this proves that the support E(S_n) itself costs nothing - the supremum over all vectors on the windows is exactly ||K|| - so the whole gap between any window ansatz and 1 lies in the amplitude class, never in the support.
  thompson-f-nonamenable-iff-some-monomial-set-doubles: that translates Følner sets into the positive monoid and reformulates amenability as small doubling of monomial sets; this is the spectral (l^2, norm-exact) statement for the induced subgraph of the Cayley graph on the positive monoid, identified with the move graph of pointed forests, with a degree-deficiency obstruction that has no Følner-counting analogue in that node.
  thompson-f-coarse-reiter-radius-is-one-ramsey-call-away: that concerns Reiter radii of ball-compressed walks; this is an exact norm identity for one explicit family of finite graphs.
  thompson-f-is-amenable: that is the open root; this is an exact reformulation of its Kesten form and decides nothing.
artifacts:
  - experiments/thompson-f-forest-lossless-2026-09-17/absorb_check.py
  - experiments/thompson-f-forest-lossless-2026-09-17/absorb_check_n7.out
  - experiments/thompson-f-forest-lossless-2026-09-17/window_spectrum.py
  - experiments/thompson-f-forest-lossless-2026-09-17/window_spectrum_n12.out
---

**ESTABLISHED.** Notation of `thompson-f-norm-bound-from-forest-renewal-test-vector-proof`:
- `G = <s_0, s_1>` in `PL(R)` is `F`.
- Cayley edges are `x ~ x o g` for `g` in `{s_0^{±1}, s_1^{±1}}`.
- `K = s_0 + s_0^{-1} + s_1 + s_1^{-1}`, so `||K|| = 4||P||`.
- `S_n` is the set of pointed forests with `n` leaves, `E : S_n -> G` is the window embedding,
  and the four moves (pointer right/left, merge, split) are Cayley edges.

Let `A_n` be the adjacency matrix of the move graph on `S_n`, and `rho_n` its largest
eigenvalue. Then:

1. **Norm-lossless windows.** `rho_1 <= rho_2 <= ...`, and `lim_n rho_n = sup_n rho_n = ||K||`.
   The induced subgraph of the Cayley graph on `E(S_n)` is exactly the move graph on `S_n`, and
   `E(S_n) ⊂ E(S_{n+1})`.
2. **Kesten form.** `F` is amenable iff `rho_n -> 4`.
3. **One-sided forest model.** `R = ∪_n E(S_n)` is the set of pointed forests `(T_0, T_1, ...; i)`
   on the roots `0, 1, 2, ...`, with finitely many nontrivial trees and pointer `i >= 0`. It is the
   image of the positive monoid of `F`. The compression of `K` to `l^2(R)` has norm exactly `||K||`.
   Its graph `Gamma_R` has pointer right and merge at every vertex, pointer left iff `i > 0`, and
   split iff the pointer tree `T_i` is not a leaf.
4. **Deficiency obstruction.** For unit `f >= 0` on `R`, let
   `delta(f) = sum f(v)^2 ([i = 0] + [T_i is a leaf])` and
   `energy(f) = sum over undirected edges of Gamma_R of (f(x) - f(y))^2`. Then exactly
   `<f, K f> = 4 - delta(f) - energy(f)`. Hence `F` is amenable iff there are unit `f >= 0` on
   one-sided pointed forests with `delta(f) + energy(f) -> 0`. A family of test vectors whose
   pointer-leaf plus pointer-at-root mass stays `>= c > 0` has Rayleigh quotients `<= 4 - c`,
   so it can never certify more than `||P|| >= 1 - c/4`.

Proof route: `thompson-f-one-sided-forest-windows-are-norm-lossless-proof`.

**What this changes.**
- *The ansatz front.* Every window test vector (w13's product form, w14's refinements) is
  supported on `E(S_n)`. Item 1 says the support is not the reason any such family stays below
  `1`. The earlier Attempts note ("a computable proxy ..., though it is not equivalent to it")
  is sharpened: the unrestricted window optimum `rho_n / 4` *is* equivalent to `||P||` in the
  limit. Only the amplitude class (product form, bounded tree size `N`) can lose.
- *Where a Følner-type vector must live.* By item 4, a near-eigenvector must put vanishing `l^2`
  mass on pointer-leaf states and on pointer-at-root states. A family that cannot concentrate
  its pointer on nontrivial trees is dead as a route to amenability, whatever its bulk weights.

**Numbers (floating point, illustrations only; `window_spectrum_n12.out`).**
`rho_n / 4` = `0.7075, 0.7372, 0.7599, 0.7779, 0.7925, 0.8047, 0.8149` for `n = 6..12`
(`|S_12| = 534888`). This is monotone, as item 1 requires. It is far below the certified `0.9397`,
because boundary loss decays slowly. So small exact windows are not a competitive certificate.
Item 1 is a statement about the limit.

**Scope.** This is a reformulation plus an obstruction on ansatz families. It proves neither
`||P|| = 1` nor `||P|| < 1`. The absorption step is the classical common-right-multiple (Ore)
property of the positive monoid (Step 0 of `thompson-f-nonamenable-iff-some-monomial-set-doubles-proof`),
proved here from scratch in the PL model so that the identification with the w13 windows is
exact.
