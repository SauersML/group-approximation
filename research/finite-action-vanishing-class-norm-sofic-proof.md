---
rg: 2
id: finite-action-vanishing-class-norm-sofic-proof
kind: route
title: Twist exact finite actions by small-defect torsor cochains, amplify by separating quotients, and read words through van Kampen diagrams
target: finite-actions-with-vanishing-class-norm-make-extension-sofic
requires: []
artifacts:
  - research/artifacts/sk-deligne-sofic-2026-09-14-part1.md
---

Section 2 of the artifact.
1. **Presentation.** `Gamma~ = <S ∪ A | relations of A, [a,s], r = a_r>`, as in step 1 of Theorem S.
2. **Amplify.** Take `X_n` and `b_n` with defect `nu_n -> 0`. Pass to `V_n = X_n x Gamma/N_n` for a separating chain
   `N_n` with trivial intersection, pulling back `b_n`. The defect does not grow, and for each `g != 1` the action
   eventually moves every point. This is the residual amplification of Alekseev–Thom arXiv:2512.15494 Lemma 3.2.
3. **Permutations.** `tau(s)(v,t) = (s·v, t + b(s, s·v))` and `tau(a)(v,t) = (v,t+a)`. The `A`-relations and
   commutators hold exactly. `r = a_r` holds at `(v,t)` iff the cell `(v,r)` is not defective, because the base action
   is exact.
4. **Words.** A word trivial in `Gamma~` is `w' a` with `w'` trivial in `Gamma`. A van Kampen diagram of radius `C_w`
   maps into the action complex at every base point, and discrete Stokes makes the holonomy the sum of cell values.
   Outside a fraction `|B_(C_w)| |R| nu_n` of base points no cell is defective, so the word acts trivially. The same
   computation shows a nontrivial central `a` moves those points, and `g != 1` moves all points for large `n`.
5. **Conclusion.** `tau_n` is a sofic approximation of `Gamma~`.
