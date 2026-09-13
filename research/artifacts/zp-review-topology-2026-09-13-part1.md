# ZP topology review, 2026-09-13, part 1

Reviewer lane: z-verify-topology. Scope: Zaremsky Problems 1.01, 1.03–1.06, 1.08, 1.09, 1.13, 1.14,
1.16–1.19, 1.21, 1.23, 1.24, Section 4, 2.04 and 2.05 (jointly with z-verify-groups), and the imports
for 1.15 and 4.03. Verdicts: PASS (argument and statement correct, graph wiring correct), GAP (a
precise defect to repair; the mathematics may still be fine), FAIL (false). Problem wording is checked
against the July 12, 2026 PDF (SHA-256 d14c2ce7…).

## 1. Problem 4.03 import (z-hub, 76a6da25c3): PASS

Nodes: `rips-complexes-of-integer-lattices-are-contractible` (+ `-citation`), `zaremsky-4-03-by-virk`,
root `zaremsky-4-03-rips-complex-of-zn-contractible`.

- Source read at arXiv:2405.09134v4 (HTML): the (closed) Rips complex has a finite σ as a simplex iff
  `Diam(σ) ≤ r`. Theorem 5.1, verbatim: "For each r≥n²(2n−1) we have Rips((ℤⁿ,d₁),r)≃∙."
  Theorem 3.2: "Let n∈{1,2}. Then for each r≥n, Rips(ℤⁿ,r)≃∙." Theorem 5.2: "For each r≥3,
  Rips(ℤ³,r)≃∙." `d₁` is the ℓ¹ metric, which the paper calls the natural word metric. All match the
  citation route.
- Wording: the root quotes Problem 4.3 verbatim, including the list's note crediting Virk. "For
  large enough Rips parameter" asks for some threshold r₀, and Theorem 5.1 gives r₀ = n²(2n−1). The
  convention remark is right: `d₁` is integer-valued, so the closed and open conventions differ by a
  shift of 1.
- Graph: the claim is established through its citation route, so `zaremsky-4-03-by-virk` fires and
  establishes the root. That is intended. The root correctly has no no-route.
- Note, no action needed: arXiv lists the journal reference as Trans. Amer. Math. Soc. (2024).

## 2. Problem 1.15 import (z-hub, d9fd96f9e7): PASS

Nodes: `stallings-bieri-groups-have-quadratic-dehn-function` (+ `-citation`),
`zaremsky-1-15-by-stallings-bieri`, root `zaremsky-1-15-quadratic-dehn-type-fn-not-fn-plus-1`.

- Source read at arXiv:1509.07539v2 (PDF pp. 1–2). The following match verbatim: the definition of
  `SB_n` as the Bestvina–Brady group of `F_2 × ⋯ × F_2` (the join of n copies of `S^0`); "Bieri [5]
  has shown that SB_n is of type F_{n−1} but not of type F_n"; "Note that SB_1 and SB_2 are not
  finitely presented"; Corollary 4.3 and the sentence after it ("In particular, SB_n has quadratic
  Dehn function for every n ⩾ 3."); Corollary 1.1.
- Mathematics: `G_n = SB_{n+1}` (n ≥ 2) is of type `F_n`, not of type `F_{n+1}`, and quadratic. This
  is exactly what the problem asks for.
- Not verified by me: the Math. Ann. DOI in the citation route. The PDF front page carries no
  journal data. This is harmless.

## 3. Problem 2.05 imports (z2-05-v-dehn, 572b501d74): PASS

Nodes: `thompson-f-has-quadratic-dehn-function`, `thompson-t-has-quadratic-dehn-function`,
`thompson-v-dehn-function-is-at-most-sextic` (each with a `-citation` route), open
`thompson-v-has-quadratic-dehn-function` and `thompson-groups-f-t-v-have-euclidean-higher-dehn-functions`,
route `zaremsky-2-05-by-euclidean-fillings`, root `zaremsky-2-05-dehn-functions-of-thompson-t-and-v`.

- Abstracts re-read at the source:
  - Guba, math/0211395: "the Dehn function … of the Richard Thompson's group F is quadratic";
  - Migliorini, arXiv:2410.23088 (Forum Math. Sigma 13 (2025) e109): "Thompson's group T and, more
    generally, all the Higman-Thompson groups T_n have quadratic Dehn function";
  - Lorrain, arXiv:2608.03813 (v1 4 Aug 2026, v2 5 Aug 2026): improves the V upper bound to `n^6`.
  The three claims say exactly this. I did not re-read the quoted page numbers or theorem numbers
  (Guba Theorem 1, Migliorini Theorem A, Lorrain Theorem 5.7) inside the PDFs.
- Mathematics in the root: "V ⊇ F ⊇ Z², so V is not hyperbolic and δ_V ≽ n²" is correct. F, T and V
  are of type F_∞, so the higher Dehn functions are defined. The three-part decomposition matches the
  problem text, and the root correctly treats "higher-rank" as k ≥ 2.
- Graph: the answer route requires two open claims, so nothing fires.

## 4. Problem 1.13 lemma (z1-13-sigma-inf, 1949e249c1): PASS

Node: `non-open-sigma-infinity-needs-unbounded-sigma-depth` (+ `-proof`).

- Re-derived, with δ(ψ) = min{n : ψ ∉ Σⁿ}:
  - {δ > n} = Σⁿ, because the invariants decrease, so δ is lower semicontinuous.
  - χ ∈ Σ^∞ is interior iff some neighbourhood of χ avoids finite-depth characters.
  - For ψ_k → χ, openness of Σⁿ ∋ χ forces δ(ψ_k) > n eventually.
  - A decreasing sequence with finitely many values is eventually constant, so Σ^∞ = Σ^N is open.
  All correct. The only input is openness of each Σⁿ (Bieri–Renz for Σⁿ(G;Z); Renz for the
  homotopical invariants), and the root takes that from the problem statement.
- The model test F₂^r (Σⁿ stabilizes at n = r, Σ^r = ∅) is illustrative only and not load-bearing.
- Wording: the root quotes the problem verbatim ("Every Σⁿ(G) is an open subset of the character
  sphere Σ(G), but what about Σ^∞(G)? Must that be open?"). Graph: both answer claims are open;
  nothing fires.
- Not an answer. It is a correct necessary condition: a negative answer needs infinitely many distinct
  Σⁿ. It makes 1.13's no side depend on 1.18-type phenomena, as the root says.

## 5. Problem 1.23 answered NO (z1-23-bb-dehn, fbb779bc37): PASS

Nodes: `raag-kernel-dehn-function-below-bestvina-brady` (+ `-proof`),
`bestvina-brady-dehn-function-classification` (+ `-citation`), `zaremsky-1-23-by-no`,
`bestvina-brady-dehn-bound-holds-up-to-quadratic` (+ `-proof`),
`dead-vertex-raag-kernels-retract-onto-subgraph-kernels` (+ `-proof`), refuted
`bestvina-brady-dehn-bounds-fp-raag-kernels`, open `bestvina-brady-dehn-bounds-kernels-with-no-dead-vertices`.

**Source.** Chang–García-Mejía–Migliorini, arXiv:2507.07566 (v1 10 Jul 2025, v2 30 Dec 2025; Geom.
Funct. Anal. 36, 1–58 (2026)), read on the arXiv abstract page and in HTML.
- Standing hypothesis: Γ finite with Δ(Γ) simply connected.
- Theorem 1: δ_{BB_Γ}(n) ≍ n^{d(Γ)}, where d(Γ) is the largest α with (D_α).
- (D1) Δ(Γ) is simply connected. (D2) Γ is not a tree. (D3) Γ contains a maximal reducible subgraph
  that is essentially 2-reducible. (D4) Γ contains a maximal reducible subgraph whose flag complex is
  not simply connected.
- "Essentially 2-reducible" means "a join of two irreducible subgraphs, each with at least two
  vertices".
- Corollary 1, verbatim: "If Γ is an essentially 2-reducible graph such that Δ(Γ) is simply
  connected, then BB_Γ has cubic Dehn function."
- Figure 1(a): Γ₁ is the suspension of a path of length three, and BB_{Γ₁} is cubic.

All of this matches the citation route and the classification claim.

**Counterexample, re-derived independently.** Γ = {A,B} * P with P = C–D–E–F.
1. {A,B} has no edge, so it is not a join of nonempty graphs. The complement of P is the path
   E–C–F–D, which is connected, and a graph is a join iff its complement is disconnected. So both
   factors are irreducible with ≥ 2 vertices, Γ is essentially 2-reducible, and Δ(Γ) = S⁰ * arc is a
   disc. By Corollary 1, δ_{BB_Γ} ≃ n³. This Γ is the paper's own Γ₁.
2. A_Γ = F(A,B) × A_P, and χ = (0, χ_P) with χ_P ≡ 1 on C, D, E, F. So χ is onto Z, and
   ker χ = F(A,B) × BB_P.
3. P is a tree, so the Bestvina–Brady level set is a contractible 1-complex with a free cocompact
   BB_P-action, and BB_P is free of finite rank. Counting orbits of level-set cells gives 4 vertices
   and 2·3 = 6 edges in the quotient, so χ = −2 and the rank is 3; the proof uses only rank ≥ 1.
4. ker χ ≅ F₂ × F₃ acts freely and cocompactly on a product of trees, so δ ≼ n². It contains
   Z² = ⟨A, CD⁻¹⟩, since A commutes with C and D and χ(CD⁻¹) = 0, so it is not hyperbolic and
   δ ≃ n².
5. n³ ⋠ n². So δ_{BB_Γ} is not a lower bound for all finitely presented kernels. Answer: NO.

**Reading.** Problem 1.23 asks about "all finitely presented kernels of maps onto Z", and its
premise ("if some kernel of a map onto Z is finitely presented then … BB_Γ is") is also about
arbitrary maps. So characters with dead vertices are admissible, and the counterexample answers the
literal question. The lane records the natural restricted version (χ(v) ≠ 0 for every v) as the open
claim `bestvina-brady-dehn-bounds-kernels-with-no-dead-vertices`. That is the right scope statement,
and main should relay the answer with this caveat.

**General family, checked.** Γ = T * Λ, with T a tree that is not a star and Λ irreducible on ≥ 2
vertices.
- T is irreducible: a tree that is a join has one side a single vertex, so it is a star.
- Δ(T) * Δ(Λ) is simply connected, since Δ(T) is connected and Δ(Λ) is nonempty.
- By Corollary 1, BB_Γ is cubic.
- K_χ = BB_T × A_Λ acts freely and cocompactly on tree × (the CAT(0) cube complex of A_Λ), and it
  contains Z², so K_χ is quadratic. Correct.

**Side lemmas.**
- `bestvina-brady-dehn-bound-holds-up-to-quadratic`: PASS. For d = 1 there is nothing to prove, since
  every Dehn function is ≽ n. For d = 2: Δ(Γ) is simply connected and Γ is not a tree, so Γ is
  connected and contains a cycle, and since Δ(Γ) ≠ Γ it contains a triangle. That gives Z³ ≤ A_Γ, so
  ker χ ∩ Z³ has rank ≥ 2, the finitely presented kernel is not hyperbolic, and δ_K ≽ n².
- `dead-vertex-raag-kernels-retract-onto-subgraph-kernels`: PASS. This is the standard retraction
  A_Γ → A_Λ (Λ induced), with χ_Λ∘r = χ. Retracts of finitely presented groups are finitely presented,
  and their Dehn functions are ≼ that of the group.

**Graph.**
- The classification is established through its citation, which establishes the counterexample
  claim, which fires `zaremsky-1-23-by-no` and establishes the root.
- The yes claim carries `refuted_by: raag-kernel-dehn-function-below-bestvina-brady`, and its route
  stays open.
- Correct as intended.

**Credit.** The cubic lower bound is Chang–García-Mejía–Migliorini's, and the example graph is
Brady's. The repository contribution is the comparison with the dead-vertex kernel. A novelty check
is requested from z-status-a before this is called a first answer.

## 6. Problem 1.03 literal reading (z1-03-qi-fn, 66853aaa23): PASS, with a reading note for main

Node: `every-fg-group-is-qi-to-a-contractible-proper-space` (+ `-proof`).

**Re-derived.** Take a spanning tree T of the Cayley graph Γ, with d = d_Γ restricted to T.
- The subspace topology of a subcomplex is its CW topology, so (T,d) is a contractible tree.
- Closed d-balls are T ∩ (compact Γ-balls), so (T,d) is proper.
- The inclusion is isometric with 1/2-dense image, so T ≃_QI Γ ≃_QI G.

Any finitely generated group that is not of type F_n (e.g. SB_n) is then a counterexample to the
literal statement, for every n ≥ 2. Correct.

**Reading note.** Problem 1.3 says "proper metric space", so the literal question has this trivial
negative answer. The lane does not wire it into the root. Instead the root is restated under the
geodesic reading, which is the setting of the converse Zaremsky cites. That is a defensible choice
and is recorded openly in the root. Main should know that the literal wording is answered (trivially)
and the geodesic version is what stays open.

The Attempts sketch for the positive n = 2 case (geodesic reading) is plausible: realize edges by
geodesics, fill by a uniformly continuous disc, triangulate finely, and project at bounded Rips scale.
It is not established yet and will be reviewed when it lands.

## 7. Problem 4.06 root lemma (z4-06-rips-finf-fcd, 70516b1b67): PASS

Node: `contractible-rips-complex-gives-finite-classifying-space` (+ `-proof`).

**Re-derived.**
- G acts freely on vertices. If gσ = σ, then g^{|σ|!} fixes the vertices, so g has finite order and
  g = 1 because G is torsion-free.
- Every simplex translates to one containing 1, which lies in B_S(r). So there are finitely many
  orbits and dim ≤ |B_S(r)| − 1.
- The action has trivial cell stabilizers, so the quotient is a finite CW complex. Its universal cover
  is contractible, so it is a finite K(G,1).
- Finite cd implies torsion-free.
- The model test Z/2 (a nontrivial setwise stabilizer) shows the hypothesis is needed.

**Root structure.** "4.6 yes ⇔ (1.21 yes) ∧ (4.7 yes)" holds under one consistent reading of "has a
contractible Rips complex": type F ⇒ F_∞ + finite cd, and a contractible Rips complex ⇒ type F.

**Open-claim prose, checked.**
- R_r(G,S) = R_1(G, B_S(r)∖{1}), which is the flag complex of that Cayley graph.
- A vertex-simply-transitive locally finite flag complex is such a complex.
- FJC for torsion-free G predicts K̃₀(ZG) = 0.
- Finitely presented FP groups are F_∞ with finite cd, so a yes would give FF for them.
All correct.

## 8. Problem 1.01 obstruction firewalls (z1-01-embed-neg, 938ae27b49): three GAPs, one wording fix

**8a. `standard-fn-not-fn-plus-1-groups-embed-in-type-f-groups`: GAP.**
- **Definition.** Abels' group is not "upper unitriangular with 1s in the corners"; unitriangular
  would force all diagonal entries to be 1. It is the group of upper triangular matrices over
  Z[1/p] with (1,1) and (n,n) entries 1 and the other diagonal entries powers of p.
- **Index to check at the source.** My recollection (Abels 1979; Abels–Brown, J. Pure Appl. Algebra
  44 (1987)) is that the n×n group is of type F_{n−2} but not F_{n−1}. The 4×4 group is finitely
  presented with infinitely generated center. The node says F_{n−1} but not F_n. Read the source and
  fix the index or the matrix size.
- **Overclaim.** The title and body say every family embeds in a group of type **F**. For Abels'
  groups the overgroup given is GL_n(Z[1/p]), which has torsion (−1 on the diagonal), so it is of type
  F_∞ but not of type F. Either weaken the claim to "type F_∞", which is all Problem 1.1 needs, or
  supply a torsion-free type-F overgroup.

The Bieri–Stallings and Bestvina–Brady items are correct.

**8b. `cardinality-does-not-obstruct-type-f-infinity-embedding`: GAP (wording).** The countability
argument is right. It kills only arguments from a cardinality gap. The claim body also says "no
counting, **diagonal**, or cardinality argument can exhibit" a counterexample. Countability does not
exclude diagonal arguments, which run over countable lists. Delete "diagonal" (and preferably
"counting"), matching the proof route's accurate sentence ("any argument whose only input is a
cardinality inequality").

**8c. `unsolvable-word-problem-does-not-obstruct-type-f-infinity`: GAP (claim stronger than proof).**
- What the proof shows: one group of type F with unsolvable word problem exists (Collins–Miller),
  so F_∞ does not imply a solvable word problem.
- What the claim says: word-problem complexity cannot obstruct embedding a type-F_n group into an
  F_{n+1} or F_∞ group. A finitely generated subgroup's word problem is Turing-reducible to the
  overgroup's. So the stronger statement needs F_∞ (or F_{n+1}) groups whose word problems reach every
  degree that type-F_n groups realize, e.g. an F_∞ group with r.e.-complete word problem.
- Fix: cite such a theorem at the source (it may be in Collins–Miller), or restate the claim as
  "type F_∞ does not force solvable word problem".
- The Higman embedding item is about F_2 and does not reach F_{n+1}.

**8d. `higman-rope-trick-group-is-never-fp3`: statement verified; title GAP (wording).**
- Read at arXiv:2607.21727v1 (HTML), Theorem B verbatim: "Let G=F/R, and let Higᵢ(G) be as in
  Definition 1.5. Suppose G is infinite and R≠1. Then H₃(Higᵢ(G),ℚ) is infinite-dimensional; in
  particular Higᵢ(G) is not of type FP₃(ℚ)."
- Definition 1.5: G finitely generated, F free, the double L = F₁ *_R F₂, an embedding ι: L → P into
  a finitely generated group, and Higᵢ(G) the HNN extension with vertex group P × G and edge group L.
- The node's body matches, with two fixes: "finitely generated" is missing, and the dependence on P
  and ι is not mentioned.
- The title's "infinite one-relator-quotient" is wrong. G is any infinite finitely generated group
  with a nontrivial relation module (R ≠ 1), not a one-relator quotient.
- The claim can stay established once the title is fixed. The node's own "to be confirmed" note can
  now cite this review.

None of 8a–8d touches an answer route: `some-type-fn-group-embeds-in-no-type-fn-plus-1-group` is open.
