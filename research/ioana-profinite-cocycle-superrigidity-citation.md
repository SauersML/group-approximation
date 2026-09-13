---
rg: 2
id: ioana-profinite-cocycle-superrigidity-citation
kind: route
title: Ioana, Cocycle superrigidity for profinite actions of property (T) groups, arXiv:0805.2998, Theorem B
target: ioana-profinite-cocycle-superrigidity
requires: []
---

Literature import. Read from the arXiv:0805.2998v1 PDF (20 May 2008), pp. 1--3, via text extraction.
Subscripts are restored from the extraction layout.

p. 2, hypotheses of Theorem A: *"Let Γ be a countable group with an infinite normal subgroup Γ_0 such
that the inclusion Γ_0 ⊂ Γ has relative property (T) and Γ/Γ_0 is finitely generated group. Assume that
Γ ↷^α X is a free ergodic measure preserving profinite action on a standard probability space X such
that the restriction Γ_0 ↷^(α|Γ_0) X is also ergodic."*

p. 3: *"Theorem B (Cocycle superrigidity). Let Γ ↷^α X be as in Theorem A. Suppose that α is the limit
of the actions Γ ↷^(α_n) X_n, with X_n finite, and, for every n, let r_n : X → X_n be the quotient map.
Let Λ be a countable group and w : Γ×X → Λ be a measurable cocycle for α. Then there exists n such that
w is cohomologous to a cocycle w′ : Γ × X → Λ of the form w′ = w′′∘(id×r_n), for some cocycle
w′′ : Γ × X_n → Λ."*

Definitions on p. 2: a measure-preserving action is *profinite* "if it is the inverse limit of actions
Γ ↷ X_n, with X_n finite probability spaces". The cocycle identity is
`w(γ_1γ_2, x) = w(γ_1, γ_2x) w(γ_2, x)`, and `w, w′` are cohomologous if
`w′(γ,x) = φ(γx) w(γ,x) φ(x)^(−1)` for a measurable `φ : X → Λ`.

Relative property (T) for `Γ_0 = Γ` is property (T) of `Γ`, as the paper notes on p. 2. The example
`Γ = SL_n(Z)`, `n >= 3`, is named there, and the action on a profinite completion along a normal chain
with trivial intersection is named as free, ergodic and profinite.

**Trust surface.** The journal version was not checked, so theorem numbering is taken from arXiv v1.
The consequence recorded in the claim, a homomorphism on the stabilizer of a point of `X_n`, is the
standard correspondence between cocycles over a transitive finite action and homomorphisms of a
stabilizer: `w''(δ_1δ_2, a) = w''(δ_1, a) w''(δ_2, a)` for `δ_i ∈ Γ_a`.
