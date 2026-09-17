---
rg: 2
id: twisted-linear-profile-dictionary-proof
kind: route
title: Semilinear translation makes the profile invariant, and the free summand spanned by the recovered site layer turns a deficit into an epimorphism onto a larger free module
target: twisted-linear-profile-deficits-are-rank-condition-failures
requires: []
artifacts:
  - research/artifacts/twisted-linear-entropy-profiles-2026-09-17.md
  - experiments/twisted-linear-entropy-profiles-2026-09-17/check_twisted_profile.py
---

Artifact Sections 0–2.

1. **Axioms (Lemma 1.2).**
   - Left multiplication by `u_g` is a `σ_g`-semilinear bijection of `R^k`. It maps the site-`h` layer onto the
     site-`gh` layer and `u_h v_j` to `α(g,h) u_{gh} v_j`, so it carries `span_K(S)` onto `span_K(gS)` and
     dimensions are invariant.
   - Finite restrictions are entropic. The coordinates lie in a finitely generated ring `A`. Invert the product
     `c` of one nonvanishing maximal minor per subfamily, and reduce at a maximal ideal of `A[1/c]`, whose residue
     field is finite. Ranks are kept, and ranks over `F_Q` are base-`Q` entropies of uniform inputs.
2. **Information identity (Lemma 2.1).**
   - `I(X_1;Y_F) = dim(L_1 ∩ span Y_F)`.
   - The union over `F` of `span_K Y_F` is the submodule `W = sum R v_j`.
3. **Deficit ⇒ failure (Theorem 2.2).** Let `m = dim(L_1 ∩ W) > s' = dim span v_j`.
   - A `K`-basis of `L_1` adapted to `L_1 ∩ W` is an `R`-basis of `R^k`, since `GL_k(K) ⊆ GL_k(R)`.
   - Its first `m` vectors span a free summand `P ≅ R^m` inside `W`. The modular law gives `W = P ⊕ (W ∩ P')`.
   - So `R^{s'} -> W -> R^m` is onto with `s' < m`.
4. **Failure ⇒ deficit.** Generators `v_1..v_r` of `R^d` with `r < d` give `k = d` and `I = d > r >= h(Y_1)`.
5. **All-or-nothing (Theorem 2.3).**
   - `f ⊕ id` composes `R^s -> R^{s+n(m-s)}` onto, so `Phi <= s/(s+n(m-s)) -> 0`.
   - With the rank condition, `Phi >= 1`, attained by `v_1 = e_1`.
6. **Gate (Corollary 2.4).** A profile-level proof applies to these profiles, which satisfy every axiom it is
   allowed to use. So it rules out deficits, hence failures of the rank condition.
7. **Nonemptiness (Proposition 0.3).** `k|B| <= |BF| h(Y_1) + |B| h(X_1|Y_F)` by the chain rule, subadditivity
   and invariance. Right Følner sets `B` finish it.

No imports beyond standard facts: finitely generated `Z`-algebras have finite residue fields at maximal ideals,
and amenable groups have right Følner sets.

Runnable check: `python3 experiments/twisted-linear-entropy-profiles-2026-09-17/check_twisted_profile.py`
brute-forces (E), (T) and identity 2 for `F_4 ⋊ Z` with Frobenius, and exits 0.
