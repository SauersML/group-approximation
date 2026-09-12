---
rg: 2
id: seward-rokhlin-entropy-subadditivity
kind: claim
title: Outer Rokhlin entropy is countably sub-additive along increasing invariant sigma-algebras
distinct_from:
  seward-per-group-rokhlin-entropy-of-bernoulli-shifts: that imports Seward's per-group computations for Bernoulli shifts (Theorems 1.10-1.12 and Corollary 4.1); this imports the countable sub-additivity of outer Rokhlin entropy (Corollary 2.5) from the same paper.
artifacts:
  - research/artifacts/rokhlin-co-amenable-ascent-and-thompson-v-2026-09-12.md
---

**ESTABLISHED (import).** Let `G ↷ (X, μ)` be a p.m.p. ergodic action and `F` a G-invariant sub-sigma-algebra.
- **Relative Rokhlin entropy:** `h^Rok_G(X, μ | F) = inf { H(α | F) : α a countable partition with σ-alg_G(α) ∨ F = B(X) }`.
- **Outer Rokhlin entropy:** for a collection `C` of Borel sets, `h^Rok_(G,μ)(C | F) = inf { H(α | F) : α a countable Borel partition with C ⊆ σ-alg_G(α) ∨ F }`.

**Corollary 2.5.** Let `C ⊆ B(X)`, let Σ be a G-invariant sub-sigma-algebra, and let `(F_n)_(n ∈ N)` be an increasing sequence of G-invariant sub-sigma-algebras with `C ⊆ ∨_n F_n ∨ Σ`. Then

    h^Rok_(G,μ)(C | Σ) <= h^Rok_(G,μ)(F_1 | Σ) + Σ_(n >= 2) h^Rok_(G,μ)(F_n | F_(n-1) ∨ Σ).

**Two-step form used on main.** Take `C = B(X)`, Σ trivial, `F_1 = F` and `F_n = B(X)` for `n >= 2`. For every partition α with `F ⊆ σ-alg_G(α)`, and every β with `σ-alg_G(β) ∨ F = B(X)`,

    h^Rok_G(X) <= H(α) + H(β | F).

Source: B. Seward, *Krieger's finite generator theorem for actions of countable groups II*, arXiv:1501.03367v4, Section 2. Verbatim text: [[seward-rokhlin-entropy-subadditivity-citation]] and Section 5 of the artifact.
