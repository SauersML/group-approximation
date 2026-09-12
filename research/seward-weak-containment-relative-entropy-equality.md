---
rg: 2
id: seward-weak-containment-relative-entropy-equality
kind: claim
title: Adjoining an action weakly contained in all free actions leaves relative Rokhlin entropy unchanged
distinct_from:
  koopman-lambda-singular-part-has-zero-rokhlin-entropy: that imports Seward's Koopman vanishing theorem (arXiv:1804.05270); this imports his weak containment equality for relative Rokhlin entropy (arXiv:1602.06680).
  nontrivial-bernoulli-shifts-are-weakly-equivalent: that is weak equivalence of finite-alphabet Bernoulli shifts, a statement about actions; this is an entropy equality for products with an action that is weakly contained in all free actions.
artifacts:
  - research/artifacts/rokhlin-co-amenable-ascent-and-thompson-v-2026-09-12.md
---

**ESTABLISHED (import).** Let G be a countably infinite group, let `G ↷ (X, μ)` be a free p.m.p. action, and let F be a G-invariant sub-sigma-algebra. Suppose `G ↷ (Y, ν)` is a p.m.p. action that is weakly contained in all free p.m.p. actions of G. Then

    h_G(X, μ | F) = h_G(X × Y, μ × ν | F ∨ B(Y)).

Here the relative Rokhlin entropy is `h_G(X, μ | F) = inf { H(α | F ∨ I_G) : α a countable partition with σ-alg_G(α) ∨ F ∨ I_G = B(X) }`, where `I_G` is the sigma-algebra of invariant sets.

**Use on main.** Take X a free Bernoulli shift, F trivial and Y an independent Bernoulli shift, which is weakly contained in all free actions by `abert-weiss-free-actions-weakly-contain-bernoulli`. Then the Rokhlin entropy of X equals the Rokhlin entropy of `X × Y` relative to `B(Y)`.

Source: B. Seward, *Weak containment and Rokhlin entropy*, arXiv:1602.06680v2, Theorem 1.2 and the definition in the introduction. Verbatim text: [[seward-weak-containment-relative-entropy-citation]].
