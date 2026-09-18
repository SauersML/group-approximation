---
rg: 2
id: unimodular-line-pairs-detect-cyclic-quotients
kind: claim
title: Pairs of unimodular lines in R^N detect the modules R/bR ⊕ R^(N-2), so no group acting through E_N(R) is pair-finite on lines when R has infinitely many idempotent classes, which every ring of the divisible-unit gate has
distinct_from:
  faithful-pair-finite-steinberg-actions-need-noncentral-k2: that rules out every faithful pair-finite action of St_N(R) when K_2(N,R) is central, through the centre; this rules out the natural action on lines for E_N(R) and its quotients, through module invariants of pairs.
  q-algebra-with-fp-simple-projective-elementary-group: that is the finitely presented simple PE_N(R) premise for Boone--Higman, which needs no action; this concerns only the type (A) test on lines.
  fp-simple-resolvent-ring-with-divisible-unit-class: that is the ring gate; this shows that every ring meeting its items 3 and 4 fails the type (A) test on lines.
---

**ESTABLISHED** through `unimodular-line-pairs-detect-cyclic-quotients-proof`. Refereed: gq-referee-a PASS,
proof-gap lens (report 4652928f8, N1 applied); one referee. Elementary; no citation is needed except in the optional remark on purely infinite rings.

**Setting.** `R` is a unital ring and `N >= 2`. Vectors are columns and `R^N` is a right `R`-module. A *line* is a
submodule `vR` with `v` unimodular, meaning `wv = 1` for some row `w`. Let `Ω_N(R)` be the set of lines and
`Ω_N^0 = E_N(R) · e_1 R` the orbit of the standard line. `GL_N(R)` acts on `Ω_N(R)`.

**Statement.**
1. **A family of pairs.** For `b in R \ {0}`, `L_b = (e_1 + e_2 b) R = x_21(b) e_1 R` lies in `Ω_N^0`, differs from
   `e_1 R`, and
   `R^N / (e_1 R + L_b) ≅ R/bR ⊕ R^(N-2)`.
2. **The invariant.** For lines `L != L'`, the isomorphism class of `R^N / (L + L')` is an invariant of the
   unordered pair `{L, L'}` under `GL_N(R)`. So the number of `GL_N(R)`-orbits on two-element subsets of `Ω_N^0` is at
   least the number of isomorphism classes of the modules `R/bR ⊕ R^(N-2)`, `b != 0`. The same bound holds for
   `E_N(R)`, and for every group acting on `Ω_N^0` through a subgroup of `GL_N(R)`.
3. **Idempotent form.** For an idempotent `e != 1`, take `b = 1 - e`. Then `R/bR ≅ eR`, and
   `[eR ⊕ R^(N-2)] = [e] + (N-2)[1]` in `K_0(R)`. So if the idempotents of `R` take infinitely many classes in
   `K_0(R)`, no group acting through `GL_N(R)` has finitely many orbits of pairs on `Ω_N^0` or on `Ω_N(R)`.
4. **The gate rings.** Suppose `R ≅ M_n(R_n)` as unital rings for infinitely many `n`, and `[1]` has infinite order
   in `K_0(R)`. A diagonal matrix unit `f_n` of `M_n(R_n)` has `n[f_n] = [1]`, and the classes `[f_n]` are pairwise
   distinct. So item 3 applies.
   - This covers every ring meeting items 3 and 4 of `fp-simple-resolvent-ring-with-divisible-unit-class`, and every
     ring that contains `U_Q = colim M_(n!)(Q)` unitally and has `[1]` of infinite order.
   - For such `R`, `E_N(R)` and `PE_N(R)` are not of type (A) on `Ω_N^0` for any `N >= 2`,
     whatever its stabilizers are.

## Calibration

- **Fields and division rings.** `R/bR = 0` for `b != 0`, so the bound is `1`. That is consistent with the
  2-transitivity of `PGL_N(F)` on `P^(N-1)(F)`.
- **`R = Z`.** `R/bR = Z/b`, so `SL_N(Z)` has infinitely many orbits of pairs of primitive lines. This is the
  classical determinant (index) invariant.

## Scope and consequences

- **Only the natural line action is excluded.** A type (A) action of `E_N(R)` or `PE_N(R)` on some other set is not
  ruled out. The Boone--Higman route through a finitely presented simple `PE_N(R)`
  (`q-algebra-with-fp-simple-projective-elementary-group`) needs no action and is unaffected.
- **Remark, purely infinite rings.** For a purely infinite simple ring every class of `K_0(R)` is represented by an
  idempotent of `R` (Ara--Goodearl--Pardo; not read at source here). So item 3 applies to any such ring with infinite
  `K_0(R)`, in particular whenever `[1]` has infinite order.
- **For the B_A route through rings.** Any type (A) actor built from a gate ring must act on a set other than its
  lines, for example on a coset space chosen to kill the invariant `R^N / (L + L')`.
