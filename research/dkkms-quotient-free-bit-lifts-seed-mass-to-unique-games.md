---
rg: 2
id: dkkms-quotient-free-bit-lifts-seed-mass-to-unique-games
kind: claim
title: The folded DKKMS 2-to-1 game has a canonical polynomial-time unique-games lift, the quotient free bit, whose NO value is at most the 2-to-1 value and whose YES value is at least one minus the class seed spread xi minus the outer loss, with no folding-compatibility hypothesis; xi tends to 0 at every fixed smoothing rate beta in (0,1) and l >= 3 as k grows, while it is at least 1 - 1/(2^l - 1) - 6d in the certified regime, so UGC reduces to 2-to-1 soundness of the DKKMS construction at heavy smoothing
distinct_from:
  dkkms-smoothing-leaves-the-branch-coordinate-untested: its Proposition 4 labels seeds with tau = 0 and needs the open folding-compatibility of the dominant germ; here the class label a + t phi_C lives on the quotient L + H_U, compatibility is automatic, the B-labels are honest, and the statement is unconditional.
  dkkms-seed-law-is-uniform-in-regime-and-far-in-window: that proves the conditional seed law is flat at beta = log log k / k (Theorem U) and that Proposition 4 fails there (Corollary P4); this is used, not re-proved, for the flat half, and adds the free-bit lift, the exact class-level posterior formula and the concentration theorem at fixed beta, which that node does not treat.
  near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp: that kills every selector in the regime (R), where beta = log log k / k; this exhibits an explicit selector that is near-perfect exactly where (R) fails badly (fixed beta), so the two together locate the selector problem entirely on the soundness side.
  orientation-lifts-sandwich-2to1-game-values: that is the general sandwich for orientations o_e(sigma) = sigma(x_e) xor g_e(sigma restricted to L'); the free bit is such an orientation with x_e the L-part of y_e and g_e the constant h_U of its H_U-part, and this node supplies the completeness bound that the sandwich leaves open.
  efficient-branch-selector-on-proved-2to1-instances: that asks for a near-perfect selector at parameter points where DKKMS soundness is proved; this gives one at points where soundness is not proved and shows that at the proved points the canonical choice has completeness about 1/(2^l - 1).
artifacts:
  - experiments/ugc-free-bit-2026-09-17/quotient_seed_posterior.py
---

**ESTABLISHED.** Route: `dkkms-quotient-free-bit-lifts-seed-mass-to-unique-games-proof`.

## Setting

The instance is the folded DKKMS game `G` of
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses` (TR16-198 §4.2),
at parameters `(l, k, beta)` with `beta` a free rate in `(0,1)`.

- `U` is a k-tuple of variable-disjoint 3-equations, `X_U = F_2^(3k)`,
  `H_U` is the span of the block all-ones vectors, and `h_U` is the
  right-hand-side functional on `H_U`.
- The quotient is `Y = X_U / H_U = ⊕ Y_i`, with `Y_i = F_2^3/<111> ≅ F_2^2`.
  `ebar_v` is the image of `e_v`, and `f_(i,v)` is the nonzero functional on
  `Y_i` with kernel `<ebar_v>`.
- An edge `e` joins the A-vertex `(U,L)` to the B-vertex `(V,L')`, where `L'` is
  a hyperplane of `L`, `L meet H_U = 0` and `L' <= X_V`.
- The class of `(U,L)` is `C`, with `S_C = L + H_U`. It is determined by the
  variable blocks of `U` and by `Lbar = S_C / H_U`.
- The class seed law is `w(Q | C) := Pr[L' + H_U = Q | class C]`. It is a law on
  the `2^l - 1` hyperplanes `Q` of `S_C` that contain `H_U`, which are the
  hyperplanes of `Lbar`.

The quantities:

- the seed spread `xi(l,k,beta) := E_C [1 - max_Q w(Q | C)]`, with `C` drawn
  by edge mass;
- `F(n) := (1 - beta) + (beta/3) 2^(l-1) n`;
- `n_i(Q) := #{v : f_(i,v) vanishes on the block-i image of Q}`.

**The quotient free bit.** Fix a canonical rule (lexicographic least) that
picks, from a space `S` and a hyperplane `P` of it, a vector `can(S, P)` in
`S \ P`. The lift `Lift(G)` has:

- the A-vertices `C` with labels `sigma_C in Fun(R_C)`, where `R_C` is the
  class representative. These unfold at `(U,L)` to `tilde sigma_U` on `S_C`,
  equal to `h_U` on `H_U`.
- the B-vertices `(V, L')` with labels `(sigma', b) in Fun(L') x F_2`.
- the edge constraint
  `tilde sigma_U restricted to L' = sigma'` and `tilde sigma_U(y_e) = b`, with `y_e := can(S_C, L' + H_U)`.

## Statements

**Theorem F (free bit).**

1. `Lift(G)` is a unique game on alphabet `2^l` and is computable from `G` in
   polynomial time.
2. `val(Lift(G)) <= val(G)`.
3. Suppose an assignment `a` satisfies every equation of the tuples carrying
   all but an `eps_out` fraction of the edge mass. Then
   `val(Lift(G)) >= 1 - xi - eps_out`.

   The labelling that achieves this is
   `B(V,L') = (a restricted to L', 0)` and `sigma_C = (a + a(y_C) phi_C)` restricted to `R_C`.
   Here `Q_C` maximises `w(. | C)`, `y_C = can(S_C, Q_C)`, and `phi_C` is the
   functional on `S_C` with kernel `Q_C`.

**Lemma P (class posterior).** For every class `C` and every hyperplane `Q` of
`Lbar`,

`w(Q | C) = prod_i F(n_i(Q)) / sum_(Q') prod_i F(n_i(Q'))`

up to a factor in `[1, 1 + 2^(l+1-k)]^(±1)`.

**Theorem H (heavy smoothing concentrates).** Let `l >= 3` and
`beta in (0,1)`. Put

- `lambda = ln(F(1)/F(0))`, `Lambda = ln(F(3)/F(0))`;
- `mu = (beta/2)(1 - 2^(2-l)) lambda`.

Then

`xi(l,k,beta) <= 2^l [exp(-k mu^2 / (8 Lambda^2)) + 2 exp(-k mu / 2)] + 2^(l+4-k)`.

In particular `xi -> 0` as `k -> infinity` at fixed `(l, beta)`.

**Corollary D (dichotomy and decomposition).**

- *Flat side.* In the regime (R) of
  `near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp`, which
  contains every certified point with `l >= 5`,
  `xi >= 1 - 1/(2^l - 1) - 6 d(l,k)`. This follows from Theorem U of
  `dkkms-seed-law-is-uniform-in-regime-and-far-in-window`, because
  `max_Q w(Q|C) <= E_(L|C) max_R w(R|L)`.
- *Concentrated side.* At fixed `beta` the canonical free bit is a
  polynomial-time orientation with YES lift value `-> 1`.
- *Decomposition.* Take Håstad's `Gap3Lin[1 - eps, 1/2 + eps]` with
  `eps <= eta/(4k)`. Then `unique-games-conjecture` follows from the single
  open statement `dkkms-2to1-game-sound-at-heavy-smoothing` (route
  `ugc-from-dkkms-soundness-at-heavy-smoothing`).
