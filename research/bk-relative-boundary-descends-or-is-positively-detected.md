---
rg: 2
id: bk-relative-boundary-descends-or-is-positively-detected
kind: claim
title: The surviving-boundary property of a UCT Blackadar-Kirchberg counterexample descends down every quotient, and the filtration route to killing the boundary is blocked wherever a quotient detects it positively
distinct_from:
  bk-relative-lemma-b: that is the open ideal-relative killing tool; this is the established descent and the obstruction that scopes it, showing the filtration route works only in the ideal-captured case.
  bk-radical-projection-quotients-are-toeplitz-infinite: that is Theorems 8-9 on quotients of the radical; this propagates the no-annihilating-trace property down every quotient and reads off where the peeling route stalls.
  bk-radical-traces-vanishing-on-boundary-are-zero: that forbids a densely finite trace on the whole radical annihilating the boundary; this shows the same failure is inherited by every quotient and locates where the relative tool must stop.
artifacts:
  - research/artifacts/bk-relative-lemma-b-dichotomy-2026-09-13.md
---

**ESTABLISHED (lane proofs, not externally reviewed; conditional on the
unreviewed Theorem 7 = `bk-radical-traces-vanishing-on-boundary-are-zero`).**
Let `E` be separable, nuclear, stably finite and not quasidiagonal,
`R = R_qd(E)`, `H = ∂(K_1(E/R)) ⊆ K_0(R)`, with `E/J` UCT for every ideal
`J ⊆ R`.  For an ideal `J ⊆ R` put `A = R/J` and `G = (q_J)_*(H) ⊆ K_0(A)`.

1. **Descent.**  For every ideal `I ⊴ A` with quotient `π : A → A/I`, no nonzero
   densely finite lower semicontinuous trace on `A/I` annihilates `π_*(G)`.  The
   surviving property (no annihilating densely finite trace) is hereditary down
   every quotient.

2. **Absolute obstruction (Brown--Dadarlat, Spielberg).**  A faithful embedding
   of `A` into a stably finite quasidiagonal algebra with `G ↦ 0` exists only if
   `G` is singular in `K_0(A)` itself (`G ∩ K_0^+(A) = {0}`), since a nonzero
   projection class of a stably finite algebra is nonzero.  For the radical
   (`J = 0`) `H` is singular in `K_0(R)`, so there is no absolute obstruction at
   the top level; `G ∩ K_0^+(A) ≠ {0}` is equivalent to `E/J` not stably finite.

3. **Where the filtration route stalls.**  Let `τ` be an l.s.c. trace on `A`,
   faithful and densely finite on a proper ideal `I ⊊ A`, `+∞` beyond, with
   `τ̂(G_I)=0`, `G_I = G ∩ im(K_0(I) → K_0(A))`.  The filtration route peels `G`
   off level by level through `I`.  Exactly one holds.
   - **Ideal-captured:** `π_*(G) = 0`, so `G ⊆ im(K_0(I) → K_0(A))`, its lift is
     annihilated by the faithful densely finite `τ|_I`, and the killing reduces
     to Lemma B on `I` plus one Brown--Dadarlat gluing step.
   - **Escaping:** `π_*(G) ≠ 0`, and `(A/I, π_*(G))` is again surviving (item 1).
     If `π_*(G) ∩ K_0^+(A/I) ≠ {0}` then, with `K/J = I`, the descended subgroup
     is non-singular in `K_0(A/I)`, so the peeling route cannot continue through
     `A/I`, and `E/K` is not stably finite (Spielberg) — Theorem 9.

4. **The stall is forced.**  By Corollary 10 of
   `bk-radical-projection-quotients-are-toeplitz-infinite`, a type I
   counterexample has some `h ∈ H` with positive rank at every elementary point,
   so `π_*(H) ∩ K_0^+(R/K) ≠ {0}` there and the boundary is not ideal-captured.
   Hence the filtration/gluing route to `bk-relative-lemma-b` is blocked for type
   I counterexamples: the boundary cannot be peeled off through the quotient side,
   and the only remaining route is a single ideal-equivariant embedding
   (CGSTW-type) that does not factor through the infinite quotients.

Proof in the artifact: item 1 is a pullback to `R` plus Theorem 7; item 2 is the
Brown--Dadarlat remark after Definition 4.4 and Spielberg (Prop 4.1); item 3 is
six-term exactness `ker π_* = im(K_0(I) → K_0(A))` and Spielberg; item 4 quotes
Corollary 10.
