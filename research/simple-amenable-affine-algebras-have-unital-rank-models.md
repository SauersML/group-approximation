---
rg: 2
id: simple-amenable-affine-algebras-have-unital-rank-models
kind: claim
title: A simple amenable affine algebra over any field has a unital rank model, in every characteristic
distinct_from:
  invariant-measure-gives-rank-function-in-char-zero: that produces a rank function from an invariant measure on a groupoid and is restricted to characteristic zero; this produces one from algebraic amenability of the ring, over any field, with no groupoid and no measure.
  elek-amenable-algebras-almost-have-fd-representations: that is Elek's imported statement, whose conclusion is stable finiteness via local almost-representations; this is the upgrade to a faithful embedding, which is Arzhantseva–Păunescu's (see Credit).
---

**ESTABLISHED (reviewed PASS, prior result).** Let `k` be any field and `R` a simple unital affine `k`-algebra that is
amenable in Elek's sense. Then `R` has a **unital rank model** over `k`: there are integers `d_n` and a
unital injective `k`-algebra homomorphism `Φ : R → ∏_ω M_(d_n)(k)` into the rank-metric ultraproduct.
Consequently `R` carries a faithful Sylvester matrix rank function and is stably finite.

**Why this matters for the program.** Rung (Σ) of `kazhdan-elementary-approximation-type-mirrors-ring-type`
needs a unital rank model. `invariant-measure-gives-rank-function-in-char-zero` supplies one only in
characteristic zero, and `invariant-measure-gives-rank-function-any-field` is open and contains Kaplansky
stable finiteness in characteristic `p`. But the Kazhdan groups exist only in characteristic `p`, because
EJZ needs `R` finitely generated as a ring and a field finitely generated as a ring is finite (Artin–Tate).
This claim supplies the missing half by a route that never mentions a measure.

**Credit (corrected at review).** The statement is PRIOR: G. Arzhantseva and L. Păunescu, *Linear sofic groups and
algebras*, arXiv:1212.6780v1, §11. Corollary 11.15: "A simple unital algebra with almost finite dimensional
representations is linear sofic." After Proposition 11.16: "We can construct a unital morphism Θ for any amenable
algebra. Therefore, amenable algebras have almost finite dimensional representations. [...] In particular, any
amenable or LEF algebra that is also simple is linear sofic." Their Definition 4.2 (an "injective morphism
Θ : A → Π_(k→ω) M_(n_k)(F)/Ker ρ_ω. Moreover, if A is a unital algebra we require that this morphism is unital")
is exactly a unital rank model. The compression construction and the ideal property of the rank radical are
Elek's (`elek-amenable-algebras-almost-have-fd-representations`). The proof route here is an independent
self-contained derivation; no novelty is claimed.

**Scope.** Amenability is sufficient, never necessary. Exponential growth does not imply non-amenability
(`k[Γ]` is amenable for every amenable `Γ`). A rank model over a fixed `k` is weaker than exact matriciality
over varying finite fields.

**Review (un-verify-open, 2026-09-13, `research/artifacts/un-review-open-2026-09-13-part1.md` §2.1): PASS,
PRIOR.** Steps (a)–(f) were re-derived: `(★)` from `1 ∈ B_n`, the defect rank bound
`dim(sQ_n+Q_n) − dim Q_n ≤ d_n/n` (using `W = Q_n ⊕ (W ∩ T_n)` for `W ⊇ Q_n`), the two-sided ideal `N`, and
faithfulness by simplicity. Credit moved to Arzhantseva–Păunescu, quoted from the PDF.
