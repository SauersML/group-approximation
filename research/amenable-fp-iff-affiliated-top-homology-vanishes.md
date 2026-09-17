---
rg: 2
id: amenable-fp-iff-affiliated-top-homology-vanishes
kind: claim
title: An amenable group of cd n and type FP_{n-1} is of type FP iff H_{n-1}(G; U(G)) = 0; in dimension 2 Kropholler's question is exactly this vanishing
distinct_from:
  amenable-cd-two-solvable-iff-coherent-rational-group-algebra: that trades the domain hypothesis for coherence of Q[G], a property of all principal left ideals; this trades it for the vanishing of one homology group of the trivial module with coefficients in the algebra of affiliated operators
  amenable-principal-fp-group-algebras-are-domains: that turns zero divisors into a finiteness question about principal ideals via integral traces; this turns the finiteness step of Degrijse's Theorem B into exact (not merely dimension-zero) vanishing of L2-homology
  amenable-finite-cd-integral-group-rings-are-domains: that is the domain half H1; the vanishing here follows from H1 (item 3) and in dimension 2 is equivalent to it, but it is a statement about the trivial module only
  amenable-finite-cd-domain-groups-are-virtually-solvable: that assumes Z[G] is a domain; items 1-2 remove the domain hypothesis from Degrijse's finiteness theorem in every dimension
artifacts:
  - research/artifacts/kropholler-question-zero-divisor-split-2026-09-16.md
---

**ESTABLISHED** through `amenable-fp-iff-affiliated-top-homology-vanishes-proof`, from cited
theorems (Lück's dimension theory for `NG` and `U(G)`, Lück's dimension-flatness for amenable
groups, Tamari's Ore theorem, and Degrijse's proof of Theorem B after its first step).

`U(G)` is the algebra of operators affiliated to the group von Neumann algebra `NG`, a von Neumann
regular ring containing `Z[G]`. `H_q(G; U(G)) = Tor_q^{Z[G]}(U(G), Z)`.

1. **Finiteness from acyclicity (any group).** Let `n >= 2`, `cd_Z G = n`, and `G` of type
   `FP_{n-1}`. If `H_q(G; U(G)) = 0` for all `q`, then `G` is of type `FP`.
2. **Only one degree matters (amenable).** If moreover `G` is amenable, then `H_q(G; U(G)) = 0`
   automatically for every `q != n-1`. Hence `G` is of type `FP` if and only if
   `H_{n-1}(G; U(G)) = 0`.
3. **Domains give acyclicity.** If `G` is amenable and `Z[G]` is a domain, then `H_q(G; U(G)) = 0`
   for all `q`. So items 1-2 contain Degrijse's Theorem A (arXiv:1609.07635): "amenable, `Z[G]`
   a domain, `cd G = n`, type `FP_{n-1}` ⇒ type `FP`".
4. **Dimension 2.** Let `G = <x_1, ..., x_d | r_1, r_2, ...>` be a finitely generated amenable group
   with `cd G = 2`. The following are equivalent:
   - (a) `G ≅ BS(1,m)` for some `m != 0`;
   - (b) `G` is of type `FP_2`;
   - (c) `H_1(G; U(G)) = 0`;
   - (d) some finite set of relators `r_1, ..., r_k` has Fox Jacobian
     `(∂r_i/∂x_j) ∈ M_{k×d}(Z[G])` of von Neumann rank `d - 1`.

   Consequently Kropholler's question for groups of cohomological dimension at most 2 is
   equivalent to: **every finitely generated amenable group of cd 2 satisfies (c)**, equivalently
   is of type `FP_2`.

**What this isolates.** For amenable `G` the `L²`-Betti numbers vanish, so `H_1(G; U(G))` always
has `U(G)`-dimension 0. The ranks of the Fox Jacobians of the first `k` relators increase to
`d - 1` as `k → ∞`. A two-dimensional counterexample to Kropholler's question is exactly a finitely
generated amenable group of cd 2 where this supremum is never attained. The domain hypothesis
that Degrijse adds in Theorem B is used only to force attainment.
