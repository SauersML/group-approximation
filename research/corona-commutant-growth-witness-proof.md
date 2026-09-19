---
rg: 2
id: corona-commutant-growth-witness-proof
kind: route
title: Slow phase ramps along distorted compressed word length
target: corona-commutant-growth-witness
requires: []
artifacts:
  - research/artifacts/unified-mf-compression-external-2026-08-15.md
---

## Direct proof

Fix a finite symmetric generating set `S` of `L` and put `T = tSt^{-1}`,
a finite generating set of `L_1`.  Pick `g in L \ L_1`.

**Step 1: finite quotients equalize the subgroups.**  For every finite
quotient `q : H -> F`, conjugation by `q(t)` is an automorphism of the
finite group `q(H)` carrying `q(L)` onto `q(L_1) <= q(L)`; equal finite
cardinality forces `q(L_1) = q(L)`.

**Step 2: the compressed word length of `g` diverges.**  Every `T`-word
`w` of length at most `n` lies in `L_1`, so `g != w` in `H`.  Residual
finiteness supplies a finite quotient `q_n` separating `g` from these
finitely many words simultaneously; then the `q_n(T)`-word length of
`q_n(g)` inside `K_n := q_n(L_1) = q_n(L)` exceeds `n`.  Taking products
with further quotients, arrange also that `(q_n)` eventually separates
every fixed nonidentity element of `H`.

**Step 3: the slow wall.**  Let `ell_n` be the `q_n(T)`-word length on
`K_n` and define `f_n(y) = max(1 - ell_n(y)/n, 0)` on `K_n`, zero off
`K_n`.  On `l^2(F_n)` take the right regular representation
`R_n(h) : delta_y -> delta_{y q_n(h)^{-1}}` and the diagonal unitary
`V_n : delta_y -> exp(i alpha f_n(y)) delta_y` for a fixed
`alpha notin 2 pi Z`.  For `h in L_1`, right multiplication by `q_n(h)`
preserves `K_n` and changes `ell_n` by at most the fixed `T`-length
`m(h)`, so `‖R_n(h) V_n R_n(h)^* - V_n‖ <= |alpha| m(h)/n -> 0`: the class
`v = [V_n]` centralizes `Theta(L_1)`, where `Theta = [R_n ∘ q_n]`.  At the
basis vector `delta_e`: `f_n(e) = 1` while `f_n(q_n(g)) = 0`, so
`‖R_n(g) V_n R_n(g)^* - V_n‖ >= |e^{i alpha} - 1| > 0` and `v` does not
centralize `Theta(g) in Theta(L)`.  Diagonal operators commute, so all
`H`-conjugates of `v` (again diagonal) commute.  Step 2's separation makes
`Theta` faithful: a nontrivial permutation image keeps operator-norm
distance at least `sqrt 2` from the identity.

**Audit notes (this session).**  The three load-bearing steps were checked
independently: the cardinality equalization, the residual-finiteness
divergence argument (separating one element from finitely many words), and
the two displayed norm estimates.  The witness is Hilbert--Schmidt
invisible whenever `|B_n(n)|/|F_n| -> 0` along the chosen quotients, which
is why no conflict with `kazhdan-asymptotic-commutant-transport` arises:
transport concludes in the normalized 2-norm, where `v` commutes with
everything.
