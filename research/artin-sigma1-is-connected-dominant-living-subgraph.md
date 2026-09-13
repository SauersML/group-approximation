---
rg: 2
id: artin-sigma1-is-connected-dominant-living-subgraph
kind: claim
title: "The Sigma^1-conjecture: for every Artin group, Sigma^1 consists of the characters whose living subgraph is connected and dominant"
distinct_from:
  artin-sigma1-conjecture-known-families: that records specific graph families where this formula is proved; this asserts the formula for every finite labelled simplicial graph
  artin-sigma1-living-subgraph-bounds: that records Meier's general inclusions, sufficiency and a weaker necessity with the full living subgraph; this is the exact equality, whose missing half is the dead-edge necessity
---

Let `Γ` be a finite simplicial graph with labels `l(e) >= 2` and `A_Γ` its Artin
group. For a nonzero character `χ : A_Γ -> R` define:

- `Liv_0^χ`: the full subgraph on the **living vertices**, `χ(v) != 0`;
- a **dead edge**: an edge `e = {u, v}` with `l(e) >= 4` even and
  `χ(u) + χ(v) = 0`;
- `Liv^χ`: `Liv_0^χ` with the interiors of all dead edges removed;
- `Liv^χ` is **dominant** if every dead vertex (`χ(v) = 0`) is adjacent in `Γ`
  to a living vertex.

**Claim.** `Σ^1(A_Γ) = { [χ] ∈ S(A_Γ) : Liv^χ is connected and dominant }`.

Source: K. Almeida, *The BNS-invariant for Artin groups of circuit rank 2*,
J. Group Theory 21 (2018) 189–228, as quoted in Escartín-Ferrer
arXiv:2501.08692v3, Conjecture 1.1 and Conjecture 2.16 ("Liv^χ is disconnected
⇒ [χ] ∉ Σ^1(A_Γ)", equivalent given Meier's Proposition 2.15 there).

For right-angled Artin groups there are no dead edges and this is
Meier–VanWyk's theorem. For the dihedral group `l(e) = 2k >= 4` it says
`[χ] ∉ Σ^1` exactly when `χ(u) + χ(v) = 0`; writing `x = uv`, the group is
`<x, u | [u, x^k]>`, a non-ascending HNN extension of `<x>` over `<x^k>`, and
`χ(x) = 0`.

By `artin-sigma1-living-subgraph-bounds` only one implication is missing:
**if `Liv_0^χ` is connected and dominant but `Liv^χ` is disconnected, then
`[χ] ∉ Σ^1(A_Γ)`.** By Almeida–Kochloukova (Forum Math. 27 (2015), Corollary 2.9,
quoted as Proposition 2.18 in arXiv:2501.08692v3), it suffices to prove this for
discrete characters `χ : A_Γ -> Z`.

## Attempts

- **Deleting dead vertices.** Almeida's Lemma 2.14 (J. Group Theory 20 (2017);
  Proposition 2.11 in arXiv:2501.08692v3) gives an epimorphism onto `A_{Γ'}`,
  `Γ' = Liv_0^χ`, through which `χ` factors, and non-membership pulls back.
  So one may assume every vertex is living. Every edge between two components
  of `Liv^χ` is then dead: even label `>= 4`, `χ(u) = -χ(v)`.
- **Finite abelian twists** (Escartín-Ferrer arXiv:2501.08692v3, Theorem 4.4):
  a character `μ ∘ φ`, `φ : A_Γ -> G` finite abelian, whose values on `uv` are
  nontrivial `l(e)/2`-th roots of unity across a cut proves non-membership. This
  gives the prime-`p` and balanced families. It cannot work in general: odd
  edges force equal values, and cycles of dead edges with coprime halves conflict.
- **Dead-edge rings (2026-09-13, unreviewed):**
  `artin-sigma1-dead-edge-ring-obstruction`. Any nonzero ring `R` and
  `ρ : A_Γ -> R^×` that kill the cross dead-edge sums `1 + ρ(uv) + ... + ρ(uv)^{k-1}` of a
  vertex cut prove `[χ] ∉ Σ^1`; the tool is twisted Laurent homology over `R((t))`. This
  strictly extends finite abelian twists. The triangle `A(3,4,6)` is detected by a
  2x2 representation (`artin-346-dead-character-outside-sigma1-by-rank-two-rep`) and
  by no commutative ring (`artin-346-commutative-rings-miss-the-dead-cut`). Both
  "universal witness" routes are dead:
  `artin-sigma1-conjecture-via-commutative-ring-witnesses` and
  `artin-sigma1-conjecture-via-dead-edge-rings`.
- **Test case.** The four-vertex graph `K` (label-2 edges `u1u2`, `v1v2`; cross labels
  `4, 4, 4, 6`) has no ring witness
  (`artin-k4-dead-cut-admits-no-nonzero-dead-edge-ring`). Deciding
  `artin-k4-mixed-dead-character-is-outside-sigma1` either finds the next obstruction
  (module witnesses, artifact §4 Remark ii) or refutes the conjecture.
