---
rg: 2
id: jacobson-haar-character-restricts-to-orbit-relation-summand
kind: claim
title: On the affine subgroup V x| EL_n(J) of EL_(n+1)(J), every Haar rank character splits off the Haar orbit-relation trace of EL_n(J) as a convex summand
distinct_from:
  gl-infinity-f2-trace-simplex-is-extended-naturals: that computes the CE index set S_n inside the rank-character list for one fixed n; this compares consecutive ranks and shows S_(n+1) is contained in the CE locus of the orbit-relation traces psi_m of EL_n(J), which is contained in S_n.
  leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity: that shows one CE character seeing L forces hyperlinearity; this shows that the Haar character at rank n+1 forces Connes embeddability of the whole orbit-relation algebra L(R) of EL_n(J) on the Haar space, which contains the GNS algebra of the Haar character at rank n.
  jacobson-el-characters-are-symbol-or-finitary-extensions: that classifies characters of one EL_n(J); this is a restriction formula for the rank characters of EL_(n+1)(J) to the affine subgroup V x| EL_n(J), where the orbit-relation trace appears as a non-group-pulled-back summand.
artifacts:
  - research/jacobson-haar-orbit-relation-summand-proof.md
  - experiments/jacobson-affine-sandwich-2026-09-17/check_affine_rank_split.py
---

**ESTABLISHED** ([[jacobson-haar-orbit-relation-summand-proof]]).

**Setup.**
* `J = F_2<S,T | TS=1>`, `Q = 1-ST`, `E_n = EL_n(J)`, `n >= 2`.
* `V_n = (JQ)^n`, column vectors. `JQ` has basis `S^k Q` (`k >= 0`), so `V_n = F_2^(N x n)` with finite
  support. `E_n` acts faithfully by left multiplication; `L_n = GL_fin(V_n)` is its finitary kernel.
* `X_n = Hom(V_n, F_2) = F_2^(N x n)` with Haar measure `mu`. `E_n` acts by `g.xi = xi o g^(-1)`, measure
  preservingly. `R_n` is the orbit equivalence relation, and `L(R_n)` is its von Neumann algebra.
* `sigma_m(g) = 2^(-m rank(g-1))` on `L_n`, `e sigma_m` its zero extension to `E_n`, `m in {1,...,∞}`.
  `phi_1 = e sigma_1` is the Haar fixed-point character, `phi_1(g) = mu(Fix_(X_n) g)`.
* `S_n = {m : e sigma_m is CE on E_n}`, as in `gl-infinity-f2-trace-simplex-is-extended-naturals`.

**Theorem.**
1. **(Affine subgroup.)** `A_n = {[[g, v],[0, 1]] : g in E_n, v in V_n}` is a subgroup of `E_(n+1)`, isomorphic
   to `V_n x| E_n`. For `h = (v,g)` with `g in L_n`,
   `rank(h - 1) = rank(g - 1) + [v notin Im(g - 1)]`; for `g notin L_n`, `h notin L_(n+1)`.
2. **(Splitting.)** For every `m in {1,...,∞}`,

```text
(e sigma_m^(n+1))|_(A_n) = (1 - 2^(-m)) psi_m + 2^(-m) (e sigma_m^(n)) o pr,        (AS1)
psi_m(v, g) = e sigma_m^(n)(g) * [v in Im(g - 1)].                                 (AS2)
```

   Each `psi_m` is a trace on `A_n`.
3. **(Orbit relation.)** `psi_1(v,g) = ∫_(Fix g) chi_v dmu`, with `chi_v(xi) = (-1)^(xi(v))`. The map
   `(v,g) -> chi_v u_g` is a unitary representation of `A_n` in `L(R_n)` that generates it, so
   `W*(A_n, psi_1) = L(R_n)`. `R_n` is ergodic, so `L(R_n)` is a `II_1` factor.
4. **(Sandwich.)** Let `P_n(m)` mean that `psi_m` is CE on `A_n`. By part 3, `P_n(1)` says that `L(R_n)` is
   CE. Then

```text
m in S_(n+1)   =>   P_n(m)   =>   m in S_n.                                         (AS3)
```

   In particular: `phi_1` CE on `EL_(n+1)(J)` `=>` `L(R_n)` CE `=>` `phi_1` CE on `EL_n(J)`
   `=>` `EL_n(J)` hyperlinear.
5. **(Stable equivalence.)** `phi_1` is CE on `EL_n(J)` for all `n` iff `L(R_n)` is CE for all `n`.

**What this does for the hole (`agent-leavitt-not-bcs-negative-root-corner`).**
* The dead w4 transplant (`swarm-0917-w4-pull-nh-1`) tried to prove `phi_1` CE through the orbit relation
  `R_n`. It died at the permanence step: `R_n` is the hyperfinite `L_n`-tail relation extended by the Kazhdan
  quotient `EL_n(F_2[z^(±1)])`, and permanence of CE for such extensions is open.
* Part 4 shows that this step is **forced, not merely sufficient**. Any proof that `phi_1` is CE on
  `EL_21(J)` proves `L(R_20)` CE. For finite `m >= 2`, `m in S_21` proves CE of
  `W*(A_20, psi_m) = {L^∞(X_20) ⊗ 1, u_g : g in E_20}''` inside `L(R(E_20 ↷ X_20^m))` (proof, Remark 3).
* So a proof of `phi_1` CE at any rank at or above `21` pays for CE of the Haar orbit-relation algebra of
  `EL_20(J)`. That algebra is a cocycle crossed product of the tail factor
  `L(E_0) ≅ R` by the free action of `EL_20(F_2[z^(±1)])` (proof, Remark 4).
* Only the index `m = ∞` (hyperlinearity itself) escapes the sandwich, because `psi_∞ = delta_e` on `A_n`
  and (AS1) degenerates.

**What this does not give.** It does not decide whether `L(R_n)` or `phi_1` is CE. It does not show
`1 in S_n` for a hyperlinear `EL_n(J)`, because `S_n` could be `{∞}`.
