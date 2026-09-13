---
rg: 2
id: bk-relative-boundary-descends-or-is-positively-detected
kind: claim
title: The surviving-boundary property of a UCT Blackadar-Kirchberg counterexample descends down every quotient, and at the finiteness ideal the boundary is either ideal-captured or detected positively by the quotient
distinct_from:
  bk-relative-lemma-b: that is the open ideal-relative killing tool; this is the established descent and dichotomy that scope it, showing it can only work in the ideal-captured case.
  bk-radical-projection-quotients-are-toeplitz-infinite: that is Theorems 8-9 on quotients of the radical; this propagates the no-annihilating-trace property down every quotient and reads off the ideal-captured / positively-detected split of the boundary.
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

2. **Dichotomy at the finiteness ideal.**  Let `τ` be an l.s.c. trace on `A`,
   faithful and densely finite on a proper ideal `I ⊊ A`, `+∞` beyond `I`, with
   `τ̂(G_I) = 0` for `G_I = G ∩ im(K_0(I) → K_0(A))`.  Exactly one holds.
   - **Ideal-captured:** `π_*(G) = 0`, so `G ⊆ im(K_0(I) → K_0(A))` and the
     lift `G̃ ⊆ K_0(I)` is annihilated by the faithful densely finite `τ|_I`.
     The killing reduces to Lemma B on `I` plus one Brown--Dadarlat gluing step
     `0 → I → A → A/I → 0`.
   - **Escaping:** `π_*(G) ≠ 0`, and `(A/I, π_*(G))` is again surviving (item 1).
     If moreover `π_*(G) ∩ K_0^+(A/I) ≠ {0}`, then with `K/J = I` the quotient
     `E/K` is not stably finite (Spielberg), and no faithful embedding of `A`
     into a stably finite quasidiagonal algebra can kill `G`.

3. **The obstruction is forced.**  By Corollary 10 of
   `bk-radical-projection-quotients-are-toeplitz-infinite`, a type I
   counterexample has some `h ∈ H` with positive rank at every elementary point,
   so the escaping-with-positive-detection case occurs there.  Hence
   `bk-relative-lemma-b` cannot kill `H` unconditionally through a quotient; its
   scope is the ideal-captured case, and the shape it must avoid is a quotient
   `A/I` detecting a singular boundary class positively.

Proof in the artifact: item 1 is a direct pullback to `R` plus Theorem 7; item 2
is six-term exactness `ker π_* = im(K_0(I) → K_0(A))` and Spielberg's criterion;
item 3 quotes Corollary 10.
