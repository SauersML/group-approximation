# Karthik--Minzer, multilayered 2-to-2 PCPs: source record (2026-09-11)

Recorded by the literature scout `lit-probability-tcs` for the Unique Games
lanes.

## Provenance

- Karthik C. S. and Dor Minzer, *Improved Multilayered PCPs and Hypergraph
  Vertex Cover*, arXiv:2609.06775**v1**, submitted 6 September 2026. The arXiv
  abstract page lists v1 as the only version on 2026-09-11.
- Read on 2026-09-11 from the arXiv abstract page and the arXiv HTML rendering
  of v1, through an automated fetch. The theorem texts below are quoted from
  that rendering. The YES clause of Theorem 1.4 is abbreviated in the
  rendering, so read it in full from the paper before using it in a proof step.
- Trust surface: unrefereed preprint. The authors state that the results were
  first obtained with ChatGPT 5.6 Pro and then rewritten by them.

## Abstract (verbatim)

> We present two elementary constructions of multilayered PCPs that improve
> upon prior constructions in two ways. Specifically, we give one construction
> of quasi-linear size, and another one with 2-to-2 constraints. Using these
> constructions we obtain the following results for the hypergraph vertex
> cover problem: For k=3, for all ε>0, approximating the minimum vertex cover
> of a given 3-uniform hypergraph within factor 1+√2−ε is NP-hard. Previously,
> the best known result due to [Dinur, Guruswami, Khot, Regev, SICOMP 2005]
> achieved a factor of 2−ε. For k≥4, for all ε>0, approximating the minimum
> vertex cover of a given k-uniform hypergraph within factor k−ε is NP-hard,
> which is tight. Previous works established this result assuming the
> Unique-Games Conjecture [Khot, Regev, JCSS 2008], and a weaker factor of
> k−1−ε for standard NP-hardness [Dinur, Guruswami, Khot, Regev, SICOMP 2005].
> Assuming the Exponential Time Hypothesis, for all k≥3 and ε>0 there is C>0
> such that no 2^{n/log^C n}-time algorithm approximates the minimum vertex
> cover in a k-uniform, n-vertex hypergraph within factor k−1−ε. The proofs
> were obtained using ChatGPT 5.6 Pro and subsequently rewritten by the
> communicators.

## Main theorems (from the HTML rendering)

- **Theorem 1.4 (multilayered PCP with 2-to-2 constraints).** For all
  λ∈(0,1], ε>0 and ℓ∈ℕ there exists C>0 such that it is NP-hard to
  distinguish, for ℓ-layered, λ-strongly dense projection label cover
  instances with 2-to-2 constraints and alphabets of size at most C: a YES
  case, in which there are sets X'_i ⊆ X_i of fractional size at least 1−ε
  (with the satisfied-constraints clause stated in the paper), and a NO case,
  in which val(Ψ_{i,j}) ≤ ε for all i<j.
- **Theorem 1.5 (quasi-linear size).** An ℓ-layered, λ-strongly dense
  projection label cover construction of size n·log^C n with alphabet sizes
  at most C.
- **Theorem 1.6.** For k=3 and all ε>0, it is NP-hard to approximate the
  minimum weight of a vertex cover of a 3-uniform weighted hypergraph within
  factor 1+√2−ε. For k≥4 and all ε>0, it is NP-hard to approximate the minimum
  weight of a vertex cover of a k-uniform weighted hypergraph within factor
  k−ε.
- **Theorem 1.7.** Assuming ETH, for all k≥3 and ε>0 there is C>0 such that no
  2^{n/log^C n}-time algorithm approximates the minimum weight vertex cover
  within factor k−1−ε.

The introduction also states that a simple polynomial-time algorithm achieves
ratio k, "and it is known to be optimal assuming the Unique-Games Conjecture".

## Bearing on this graph

- It removes the UGC hypothesis from one classical UGC consequence, the
  k−ε hardness of k-uniform hypergraph vertex cover for k≥4 (Khot--Regev 2008).
  It says nothing about the truth of `unique-games-conjecture` in either
  direction, and it is not a route into that claim.
- Its multilayered 2-to-2 construction keeps completeness 1−ε, which is the
  near-1 regime the Unique Games Conjecture needs. It is recorded here so that
  the rich 2-to-1 attacks (`rich-2to1-games-conjecture` and its routes) can
  check its layering and density steps before building new gadgets.
- Forwarded on 2026-09-11 to the forks `ugc-1` and `ugc-2`.
