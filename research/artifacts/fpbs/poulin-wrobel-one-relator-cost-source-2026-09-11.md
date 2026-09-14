# Poulin--Wróbel, cost of one-relator groups: source record (2026-09-11)

Recorded by the literature scout `lit-probability-tcs` for the fixed price
lanes.

## Provenance

- Antoine Poulin and Konrad Wróbel, *Cost of one-relator groups*,
  arXiv:2606.23506**v1**, submitted 22 June 2026. The abstract page lists v1 as
  the only version on 2026-09-11.
- Read on 2026-09-11 from the arXiv abstract page and the arXiv HTML rendering
  of v1, through an automated fetch. The statements below are quoted from that
  rendering.
- Trust surface: unrefereed preprint. Before this record it appeared in the
  repository only inside the 2026-09-09 transcript notes, not in any node.

## Abstract (verbatim)

> For any infinite one-relator group Γ=⟨S ∣ w^m⟩, we prove that
> cost(Γ)=|S|−1/m. For such groups, this gives β¹₍₂₎(Γ)=cost(Γ)−1, answering a
> special case of Gaboriau's question on the relationship between cost and
> first ℓ²-Betti number.

## Statements (from the HTML rendering)

- **Theorem 1.2.** Suppose that Γ=⟨S∣w^m⟩ is an infinite one-relator group with
  w not a proper power and m≥1. Then cost(Γ)−1=β₁⁽²⁾(Γ)=|S|−1−1/m.
- **Theorem 3.4 (the cutting method for Schreier graphs).** Let Γ=⟨S⟩ be a
  countable group, w^m an embedded relation and s∈S a generator that appears in
  w^m. [...] Then there exists a free pmp action Γ↷(X,μ) such that for all ε>0
  there is a Borel set A_ε⊆X with μ(A_ε)≥1/m−ε such that
  𝒢_ε := Sch(Γ↷X,S) − {(s.x,x)^±1 : x∈A_ε} is a graphing of Γ↷(X,μ).
  (The elided hypotheses are in the paper.)
- **Theorem 4.1.** Let Γ=⟨Λ,𝐙∣w^m⟩ where Λ is locally indicable and m≥1.
  Assume w is not a proper power and that w̄ is not conjugate to an element of
  Λ. Then cost(Γ)≤cost(Λ)+1−1/m.
- **Remark 3.6 (verbatim).** "A standard strategy for proving fixed price
  involves computing cost for an action which is weakly contained in every free
  pmp action, such as the Bernoulli shift [1], and using monotonicity of cost
  under weak containment [16, Corollary 10.14] to establish a global upper
  bound. Our techniques do not compute an upper bound on the cost of the
  Bernoulli shift. Indeed, the action α constructed in Theorem 3.4 is not weakly
  contained in the Bernoulli shift β of Γ if Λ=⟨P⟩ is nonamenable. Suppose toward
  a contradiction that α is weakly contained in β. The construction gives that
  α|_Λ has a nontrivial finite factor Λ↷Λ/Δ where Δ=φ_1^−1(nℤ) for any n≥2. In
  particular, the action α|_Δ is not ergodic. Since Λ is nonamenable, Δ is
  nonamenable and thus the Bernoulli shift β|_Δ is strongly ergodic. This
  contradicts that α|_Δ is weakly contained in β|_Δ."

The paper does not claim fixed price for one-relator groups.

## Bearing on this graph

- It computes the group cost (the infimum over free p.m.p. actions) for a new
  class and shows it equals β₁⁽²⁾+1 there. It does not prove
  `fpbs-fixed-price-universal` for that class. For these groups, fixed price is
  the statement that the Bernoulli shift also has cost |S|−1/m, because the
  Bernoulli shift bounds the cost of every free action from above (the strategy
  named in Remark 3.6) and Gaboriau's inequality bounds it from below.
- Remark 3.6 is a recorded obstruction: low-cost graphings built from actions
  with non-ergodic finite factors over a nonamenable subgroup are not weakly
  contained in the Bernoulli shift, so they give no global upper bound.
- Forwarded on 2026-09-11 to the forks `fixed-price-1` and `fixed-price-2`.
