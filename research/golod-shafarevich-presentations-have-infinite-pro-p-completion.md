---
rg: 2
id: golod-shafarevich-presentations-have-infinite-pro-p-completion
kind: claim
title: An abstract presentation satisfying the Golod--Shafarevich condition gives a group with infinite pro-p completion
distinct_from:
  sp21-golod-shafarevich-test-gives-infinite-pro-p-rank: that applies a quadratic Golod--Shafarevich--Vinberg bound from mod-p cohomology to arithmetic lattices; this imports the general degree-weighted criterion for abstract presentations
---

**Literature input.** Let `p` be a prime and `(X, R)` a presentation of an abstract
group `G`, with `X = {x_1, ..., x_d}` finite. Let
`ι: F(X) -> F_p⟨⟨u_1, ..., u_d⟩⟩^×` be the Magnus embedding `x_i -> 1 + u_i`
(through the free pro-p group), and define the degree function
`D(f) = deg(ι(f) - 1)`, the lowest degree of a nonzero monomial. Put
`H_R(t) = Σ_{r in R} t^{D(r)}`.

If there is `τ in (0,1)` with `1 - |X|τ + H_R(τ) < 0`, then the pro-p completion
`G_p̂` is infinite. In particular `G` is infinite.

Source: Ershov, *Golod--Shafarevich groups: a survey*, arXiv:1206.0490
(`gssurvey_revised.tex`), the degree-function definition, the GS-condition
definition with its Remark, and Theorem `GSinf`. The route quotes them.
