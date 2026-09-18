---
rg: 2
id: rn-groups-of-affine-lamplighters-f-q-wr-z-are-fp
kind: claim
title: For every prime power q and a in F_q^*, the affine lamplighter automaton x -> tx + c on F_q[[t-a]] gives V_q(F_q wr Z) finitely presented, and V_q(AGL_1(F_q[t,1/t])) finitely presented although AGL_1(F_q[t,1/t]) is not
distinct_from:
  rover-nekrashevych-group-of-lamplighter-automaton-is-fp: that is the single case q = 2 (Theorem B); this is the infinite family over all F_q and all a, with a uniform proof, plus the extension by F_q^* where N is not K_infty.
  rover-nekrashevych-fp-iff-finite-lift-presentation: that is the general criterion; this applies it to an infinite family, including a case with N a finitely generated lift ideal different from K_infty.
  rover-nekrashevych-finite-presentation-criteria: that imports sufficient conditions (G f.p., or G contracting); no group here satisfies either.
  persistent-automata-rn-group-fp-iff-group-fp: that proves V f.p. iff G f.p. under persistence; this shows the conclusion fails without persistence, inside the Skipper-Witzel-Zaremsky affine family.
---

**ESTABLISHED (proof in `rn-groups-of-affine-lamplighters-f-q-wr-z-are-fp-proof`; unreviewed).**

## Setting

- `q = p^e` is a prime power, `a in F_q^×`, and `π = t - a`. The ring `O = F_q[[π]]` is the completion of `F_q(t)`
  at the degree-one place `t = a`. Writing `x = x_0 + π y` with `x_0 in F_q` identifies `O` with `F_q^ω`, the
  boundary of the `q`-regular tree `T_q`.
- **The affine lamplighter automaton `𝒜(q, a)`** has states `B_c` for `c in F_q`, where `B_c(x) = t x + c`. In
  wreath recursion:

  `B_c = β_c (B_x)_{x in F_q}`, where `β_c(x_0) = a x_0 + c`, i.e. `B_c(x_0 + π y) = (a x_0 + c) + π B_{x_0}(y)`.

  For `q = 2`, `a = 1`, this is the lamplighter automaton of Theorem B, after relabelling letters by `x ↦ 1 - x`.
- `G = G(q, a) = ⟨B_c⟩` is the group `{x ↦ t^n x + f : n in Z, f in F_q[t, t^{-1}]} ≅ F_q ≀ Z`.
- `G^+ = ⟨G, μ_u⟩` with `μ_u(x) = u x` for `u in F_q^×`, so that `μ_u = (x_0 ↦ u x_0)(μ_u, ..., μ_u)`. Then
  `G^+ = F_q[t^{±1}] ⋊ (F_q^× × t^Z) = AGL_1(O_S)` for `S = {0, ∞}`. This is the Skipper–Witzel–Zaremsky affine
  group of arXiv:1712.05361 §6, and the Kochloukova–Sidki group `PU(2, O_S)` when `a = 1`.

## Statement

1. **`G` is finite-state, self-similar and faithful, but neither contracting nor finitely presented.** For `A = B_0`
   we have `A^m|_{0^n} = A^m` for all `m` and `n`.
2. **`N = K_∞` for `𝒜(q, a)`.** Every relator of `F_q ≀ Z` in the states `B_c` dies after finitely many free
   splittings. Hence `V_q(F_q ≀ Z)`, for this action, is finitely presented by `V_q`, (C) and (S) alone
   (Theorem A, consequence 2). Explicitly, with `τ_c = B_c B_0^{-1}`:
   - `τ_c τ_{c'} τ_{c+c'}^{-1} in K_1`;
   - `[τ_c, A^k τ_{c'} A^{-k}] in K_∞` for every `k ≥ 1`, proved by induction on `k` through injectivity of the
     recursion of `F/K_∞`.
3. **`N^+` is a finitely generated lift ideal different from `K_∞`.** For `G^+` on the states `B_c, μ_u`, the finite
   section-closed set
   `R_μ = {μ_u μ_{u'} μ_{uu'}^{-1}, μ_u B_c μ_u^{-1} B_{uc}^{-1} : u, u' in F_q^×, c in F_q}`
   (with `μ_1` read as the empty word) satisfies `N^+ = ⟨⟨R_μ⟩⟩_lift`. No freely nontrivial element of `R_μ` lies
   in `K_∞`, so `N^+ ≠ K_∞`. Hence
   `V_q(AGL_1(F_q[t, t^{-1}]))`, for this action, is finitely presented, although
   `AGL_1(F_q[t, t^{-1}])` is of type `F_1` but not `FP_2` (Bux; SWZ Theorem 6.8 with `|S| = 2`).
4. **Persistence cannot be dropped from SWZ Theorem 5.8.** `G^+` on `T_q` is finite-state, self-similar and coarsely
   diagonal (SWZ Proposition 6.11), not of type `F_2`, and `V_q(G^+)` is of type `F_2`. After SWZ's Lemma 5.3
   persistent extension to `T_{q+1}`, `V_{q+1}(G^+)` is not of type `F_2`, by SWZ Theorem 5.8 or by
   `persistent-automata-rn-group-fp-iff-group-fp`. The same holds for `G` itself.

## Scope and consequences

- **New class.** As far as the sources read go, this is the first infinite family of finite-state actions that are
  neither contracting nor of finitely presented groups, and whose Röver–Nekrashevych groups are finitely presented.
  It covers every `F_q ≀ Z` and every `AGL_1(F_q[t, t^{-1}])`, each with its natural affine action.
- **What was known for these groups under other actions.** Almeida–Dantas–Oliveira-Tosti (arXiv:2609.01868,
  Theorem C and Example 4.8) state that `B ≀ G` has a contracting self-similar representation, for suitable
  contracting `G` and finite abelian `B`. Their example is `C_2 ≀ (C_2 ≀ Z)`, which rests on a contracting
  representation of `C_2 ≀ Z` on the 8-regular tree. For such actions `V` is finitely presented by Nekrashevych.
  - This result was not checked here.
  - It concerns different actions of the lamplighter groups: whether `V` of one action is isomorphic to `V` of
    another is not known.
  - It does not reach `AGL_1(F_q[t, t^{-1}])`, whose lamp module `F_q[t^{±1}]` with scalar `F_q^×`-action is not a
    permutation module.
- **Finiteness length of `V` can exceed that of `G`.** SWZ Theorem 4.15 gives `V_d(G)` at least as good as `G`. Here
  `V_q(G^+)` is `F_2` while `G^+` is only `F_1`. The obvious conjecture, that `V_q(AGL_1(O_S))` is `F_∞` for the
  natural action, is open. The case `S = {0, ∞}` includes `F_∞` for `V_2(Z/2 ≀ Z)`.
- `V_q(G^+)'` is simple (Nekrashevych) and of finite index (SWZ Theorem 3.3, since `G^+` is coarsely diagonal), so it
  is a finitely presented simple group.

## Attempts

- 2026-09-18 (w8-101): proved via Theorem A.
  - `τ_c = B_c B_0^{-1}` has root permutation `x ↦ x + c` and freely trivial word-level sections.
  - For `d_k(c) = A^k τ_c A^{-k}`, the section `d_k(c)|_x` equals `D_k(y + c) D_k(y)^{-1}`, where
    `D_k(y) = ∏_{j<k} d_j(a^{k-1-j} y)` and `y = a^{-k} x`. Once the lamps at distance `< k` commute, this is the
    constant `D_k(c)`, so `d_k(c)` commutes with `τ` in `F/K_∞`.
  - The composite `F_q ≀ Z -> F/K_∞ -> G` is the identity, which gives `N = K_∞` with no Hopficity argument.
  - Machine check: `experiments/affine-lamplighter-rn-2026-09-17/afflamp.py`, over the prime fields
    `(p, a) in {(2,1), (3,1), (3,2), (5,1), (5,2), (7,3)}` with `k ≤ 4..6`. All relators are in `K_∞`. With `--mu`,
    the `μ` relators are in `N` but not in `K_∞`. See `results.txt`.
  - Next: `F_∞` (or `F_3`) for `V_q(G)` and `V_q(G^+)`. The candidate route is a Stein–Farley complex whose vertices
    are decorated by points of the Bruhat–Tits trees at `0` and `∞`, with height the Busemann sum.
