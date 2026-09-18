---
rg: 2
id: moore-ramsey-criterion-for-amenability
kind: claim
title: "Moore's Ramsey criterion: a group is amenable iff every finite set has a finite 1/2-Ramsey set, and the Følner function is bounded by an iterate of the Ramsey function"
distinct_from:
  thompson-f-folner-function-exceeds-every-tower: that is Moore's lower bound on Følner sets of F; this is Moore's Ramsey reformulation of amenability for all groups, together with Towsner's bound of the Følner function by an iterate of the Ramsey function.
  thompson-f-nonamenable-iff-some-monomial-set-doubles: that is a doubling criterion on the positive monoid of F; this is a balancing criterion on finitely additive colorings of group balls, valid in every group.
---

**ESTABLISHED by citation** (`moore-ramsey-criterion-citation`). Source: J. T. Moore,
*Amenability and Ramsey theory*, Fund. Math. 220 (2013) 263–280, arXiv:1106.3127v4
(20 Oct 2011). Statements were read from the v4 PDF on 2026-09-17. The proofs of Section 2
((1⇒2⇒3⇒4⇒5) of Theorem 2.1) and Proposition 3.1 were re-read. The rest was not.

**Definitions, verbatim (Section 1).**

> If A and B are finite subsets of G and ǫ > 0, then B is ǫ-Ramsey with respect to A if
> whenever E ⊆ B, there is a ν in P(B) such that
> • P(A)ν ⊆ P(B) and
> • |μν(E) − μ′ν(E)| ≤ ǫ for all μ and μ′ in P(A).

Here `P(A)` is the set of finitely additive probability measures on `A`, and
`μν(A) = Σ_{xy∈A} μ({x})ν({y})`.

**Theorem 1.3, verbatim.**

> Let G be a group. The following are equivalent:
> (1) For every E ⊆ G and every finite A ⊆ G, there is a μ in P(G) such that μ(gE) = μ(E) for all g in A.
> (2) For every finite A ⊆ G, there is a B which is 1/2-Ramsey with respect to A.
> (3) For every finite A ⊆ G, there is a B which is 0-Ramsey with respect to A.
> (4) G is amenable.

**Theorem 1.5, verbatim.**

> For a group G, the following are equivalent:
> (1) G is non amenable.
> (2) There is a finite A ⊆ G and an unbalanced collection Y of subsets of A which is realized in G.
> (3) There is a finite A ⊆ G for which there is no finite B which is 0-Ramsey with respect to A.

**Section 3 (due to H. Towsner), verbatim.** `S` is a finite generating set, not required to
be symmetric, and `B_n` is the ball of radius `n` in the word metric.

> • FølG,S(k) is the minimum cardinality of a 1/k-Følner set with respect to the generating set S.
> • RG,S(m, ǫ) is the minimum n such that Bn is ǫ-Ramsey with respect to Bm.

> • FG,S(m, ǫ) is the minimum n such that there is a ν in P(Bn) such that P(Bm)ν ⊆ P(Bn) and
> Σ_{g∈Bm} ||gν − ν||ℓ1 < ǫ.
> • ˜RG,S(m, ǫ, l) is the minimum n such that if fi (i < l) is a sequence of functions from Bn
> into [0, 1], then there is a ν ∈ P(Bn) such that P(Bm)ν ⊆ P(Bn) and such that for every
> g, g′ ∈ Bm and i < l, |gν(fi) − g′ν(fi)| < ǫ

> FølG,S(k) ≤ (2|S| + 1)^{FG,S(1,1/k)}

> Set RG,S(m) = RG,S(m, 1/2) and ˜RG,S(m, ǫ) = ˜RG,S(m, ǫ, 1).

> Furthermore, it shows that ˜RG,S(m, ǫ, l) ≤ ˜RG,S(˜RG,S(m, ǫ, l − 1), ǫ)

> Proposition 3.1. FG,S(m, 2ǫ|S|) ≤ ˜RG,S(m, ǫ, |S|).

> Theorem 3.2. FølG,S(k) ≤ (2s + 1)^{R^{ps}(1)} whenever (3/4)^p < 1/(2ks) where s = |S|.

Here `R^{ps}` is the `ps`-fold composition of `R_{G,S}`. The ε-Følner convention in this paper is
left and summed: `Σ_{a∈A} |(aB)△B| ≤ ǫ|B|`.

**Concluding remark, verbatim (Section 7).**

> Theorem 1.3 was proved in part in hopes that the minimum cardinalities of 1/2-Ramsey sets
> for F might grow at a more moderate rate and be easier to construct these sets by an
> inductive argument.

**Two elementary facts used downstream** (checked directly from the definition).
- *Monotonicity in B.* If `B` is ε-Ramsey w.r.t. `A` and `B ⊆ B′`, then `B′` is too. Given
  `E ⊆ B′`, apply the hypothesis to `E ∩ B`. The measure `μν` lives on `B`, so
  `μν(E) = μν(E ∩ B)`.
- *Monotonicity in A.* If `A′ ⊆ A`, then `P(A′)ν ⊆ P(A)ν`.

Hence `R_{G,S}(m) < ∞` for all `m` iff `G` is amenable (Theorem 1.3 (2)⇔(4), since every finite set
lies in a ball). Moreover `m ↦ R_{G,S}(m)` is nondecreasing. For infinite `G`, `R_{G,S}(m) ≥ m`,
because `B_m x ⊆ B_n` forces `|B_m| ≤ |B_n|`.
