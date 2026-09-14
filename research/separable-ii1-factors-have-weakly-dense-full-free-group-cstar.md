---
rg: 2
id: separable-ii1-factors-have-weakly-dense-full-free-group-cstar
kind: claim
title: Every separable II_1 factor contains a weakly dense copy of the full C*-algebra of F_infinity, hence a weakly dense QD C*-subalgebra
distinct_from:
  property-t-factors-contain-weakly-dense-popa-algebras: that asks for a simple weakly dense subalgebra with Popa's internal finite-dimensional approximation property; this gives a non-simple residually finite-dimensional one and settles only the QD clause of Brown's Question 3.
artifacts:
  - research/artifacts/sk-free-5-brown-q3-2026-09-13-part1.md
  - research/artifacts/sk-verify-14-2026-09-13-part5.md
---

**ESTABLISHED (unreviewed, lane sk-free-5, 2026-09-13)** by route `separable-ii1-factors-weakly-dense-free-group-cstar-proof`.

Let `M` be a II_1 factor with separable predual. There is an injective unital *-homomorphism `π : C*(F_∞) → M` from the full group C*-algebra with `π(C*(F_∞))'' = M`. So `M` contains a weakly dense unital C*-subalgebra that is:
- residually finite-dimensional (Choi, through `F_∞ ≤ F_2`), hence quasidiagonal;
- equipped with the local lifting property (Kirchberg).

**Brown's Question 3** (arXiv:math/0111286, §Questions, item 3, read from the source on MSI): "Can a free group factor or a II$_1$ factor with property T contain a weakly dense, QD C$^*$-subalgebra? How about a Popa algebra?"
- **First clause:** settled for every separable II_1 factor, including the property (T) factors `L(G_X)` and `L(SL_3(Z))`, the free group factors, and factors that do not embed in `R^ω`.
- **Popa-algebra clause:** `property-t-factors-contain-weakly-dense-popa-algebras`, established for every separable II_1 factor through `separable-ii1-factors-have-weakly-dense-popa-combs` (2026-09-14).

**Statement fidelity** (checked against the source, math/0111286 v3, 2026-09-13):
- **No further condition.** The printed question adds none. Brown's following remark is only about where a Popa algebra can hide (McDuff room) and why non-amenability is no obstruction.
- **No trace condition can be meant.** Brown–Dykema's examples live in non-injective factors, and they answer the free group factor case positively with no such condition. (Corrected per sk-verify-20 §6. The reason given here before, that an amenable trace on a weakly dense subalgebra forces the factor to be `R`, is false as stated: `τ|_{A_s}` is amenable for Brown–Dykema's `A_s ⊆ L(F_s)` (Theorem `mainthm` (3)), yet `L(F_s) ≇ R`, and the memoir result at l.4630–4642 needs local reflexivity.)
- **Brown's six properties.** The Corollary after Theorem `arbitraryMcDuff` lists six properties of Brown's weakly dense subalgebras of McDuff factors; the memoir version says all but one follow from quasidiagonality. The algebra here has all six:
  - (1) the 2-norm local finite-dimensional approximation relative to `‖e‖_2`: the corners `q_j` reduce finite sets of polynomials exactly, with finite-dimensional compressions;
  - (2) finite-rank projections almost commuting in norm, (3) a centralizing state on `B(L²M)`, (5) normal ucp maps to matrices that are asymptotically multiplicative on `A`, and (6) a liftable ucp map to `R^ω` injective on `A`: all from quasidiagonality;
  - (4) hyperfinite `R_n ⊆ B(L²M)` approximating `A` in norm: the same construction inside `R` embeds `C*(F_∞)` in `R`, and Voiculescu's theorem does the rest.
- **What is missing** is simplicity, which is exactly the second clause of the question.

**Mechanism.**
- Put a norming sequence of finite-dimensional representations `ρ_j` of `F_∞` on corners `q_j` of trace `2^{-j-1}`, each representation repeated infinitely often.
- Generator `a_i` acts by `ρ_j(a_i)` on every corner `q_j` with `j ≥ i`. On the complementary projection `e_i` (trace `1 − 2^{-i}`) it is a unitary 2-norm-close to the `κ(i)`-th member of a generating sequence of unitaries of `M`.
- **Injective:** the corners `q_j`, `j ≥ m`, reduce the first `m` generators, so every universal norm is attained.
- **Weakly dense:** the generators converge in 2-norm to each member of the generating sequence.

**Context and contrast.**
- `C*_r(Γ)` is QD only for amenable `Γ` (Rosenberg), so a QD subalgebra of `L(Γ)` for non-amenable `Γ` avoids `λ(Γ)`.
- Brown's Theorem `arbitraryMcDuff` realizes every McDuff factor through a Popa algebra built from GNS representations of `C*(F_∞)`. Those GNS maps are quotient maps; here the map is injective.
- Brown–Dykema (arXiv:math/0207005) built weakly dense Popa algebras, which are QD, in the interpolated free group factors. Their introduction presents them as distinct from the previously known weakly dense C*-subalgebras.

**Status on main.** `research/artifacts/sk-answered-questions-2026-09-13-part1.md` lists Q3 as not answered. The QD clause is answered here (sk-verify-14 PASS), and the Popa clause by `separable-ii1-factors-have-weakly-dense-popa-combs` (sk-verify-20 PASS-WITH-FIXES).

**Review (sk-verify-14, 2026-09-13): PASS.** Re-derived: the norming family (N), the corners, Lemma U (`x*x = e − ey*(1−e)ye` and `1 − t ≤ 1 − t²`), unitarity of `z_i`, isometry on polynomials through the reducing corners `q_j`, the estimate `‖z_i − y_k‖_2 ≤ 5·2^(−i/2)`, and strong convergence. Brown's Question 3 wording confirmed in the e-print math/0111286 (l.3134). T1 is elementary: keep "not found in the bounded search", and do not call it new without a wider search (e.g. Hadwin and Shulman on RFD algebras). See `research/artifacts/sk-verify-14-2026-09-13-part5.md` §§1–2.
