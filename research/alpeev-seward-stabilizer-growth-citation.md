---
rg: 2
id: alpeev-seward-stabilizer-growth-citation
kind: route
title: Alpeev–Seward, Krieger III, Theorem 1.11, read from the PDF
target: alpeev-seward-stabilizer-growth-kills-outer-entropy
requires: []
---

**Source.** A. Alpeev and B. Seward, *Krieger's finite generator theorem for actions of countable groups
III*, arXiv:1705.09707.
- **How it was read.** The PDF was fetched on MSI on 2026-09-12 with `curl -L`, and its text was extracted
  with ghostscript `txtwrite`. The quote is from the introduction, page 5, and Section 9 carries the
  proof. Spacing lost in extraction is restored, and subscripts are written inline.

Verbatim:

> Finally, we consider the effect of non-trivial stabilizers on entropy. It is a theorem of Meyerovitch
> that ergodic actions of positive sofic entropy must have finite stabilizers [21]. For Rokhlin entropy
> this is certainly not the case. If G y (X,µ) is a p.m.p. action and G is a quotient of Γ, then Γ acts
> on (X,µ) by factoring through G, and it is easily checked that hRok_Γ(X,µ) = hRok_G(X,µ). Nevertheless,
> outer Rokhlin entropy can detect when new stabilizers appear in a factor action.
>
> **Theorem 1.11.** Let G y (X,µ) be an aperiodic p.m.p. action. Consider a factor
> f : G y (X,µ) → G y (Y,ν).
> (i) If |Stab_G(f(x)) : Stab_G(x)| ≥ k for µ-almost-every x ∈ X then hRok_(G,µ)(Y,ν) ≤ (1/k)·hRok_G(Y,ν).
> (ii) If |Stab_G(f(x)) : Stab_G(x)| = ∞ for µ-almost-every x ∈ X then hRok_(G,µ)(Y,ν) = 0.

The paper also states:

> **Corollary 1.12.** Let G be a sofic group with sofic approximation Σ and let G y (X,µ) be a p.m.p.
> action. (i) If µ-almost-every stabilizer has cardinality at least k ∈ N, then
> hΣ_G(X,µ) ≤ (1/k)·hRok_G(X,µ). (ii) If µ-almost-every stabilizer is infinite then hΣ_G(X,µ) = 0.

Here `hRok_(G,µ)(Y,ν)` is the outer Rokhlin entropy of the factor sigma-algebra inside `(X, µ)`, as
defined in Part II (recorded on `seward-rokhlin-entropy-subadditivity`).
