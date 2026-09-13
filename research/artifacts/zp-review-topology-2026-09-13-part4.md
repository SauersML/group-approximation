# ZP topology review, 2026-09-13, part 4

Reviewer lane: z-verify-topology. Verdict conventions as in part 1.

## 15. Problem 1.9 top range (z1-09-pure-braid, 739e4ff6f2): PASS

Nodes: `pure-braid-top-bnsr-invariants-are-center-nonvanishing` (+ `-proof`),
`split-quotient-euler-obstruction-to-bnsr-invariants` (+ `-proof`),
`euler-characteristic-empties-top-bnsr-invariant` (+ `-proof`),
`pure-braid-bns-invariant-is-circle-complement` (+ `-citation`).

**Claim.** For n ≥ 3 and m ≥ n−2, Σ^m(P_n) = {[χ] : χ(Δ²) ≠ 0}.

**Lemma E (nonzero Euler characteristic empties the top invariant): PASS.** I checked proof B in detail.
- Suppose [χ] ∈ Σ^d(G;Z) with a finite d-dimensional K(G,1). By Novikov–Sikorav, the finite free Novikov
  chain complex over \widehat{ZG}_χ is acyclic in every degree, so it splits, and ⊕_even C_i ≅ ⊕_odd C_i.
- The coefficient-of-1 map τ is a trace on the Novikov ring: τ(xy) = Σ_g x_g y_{g⁻¹} is a finite sum.
  For χ(g) ≤ 0 only finitely many x_g ≠ 0, because supports are finite below every level; for χ(g) > 0
  only finitely many y_{g⁻¹} ≠ 0. The expression is symmetric in x and y.
- With AB = I and BA = I, τ(tr AB) = τ(tr BA) forces the ranks to be equal, so χ(X) = 0. Correct.
- Proof A, via Suciu arXiv:2010.07499 Theorem 1.1, is independent and plausible. I did not re-read its
  source.

**Lemma S: PASS on the quoted input.** Meinert 1997, Corollary 2.8, as quoted by Zaremsky
(arXiv:1507.08597v1, Citation 1.3): along a split epimorphism, membership of a pulled-back character in
Σ^m descends to the quotient. Combined with Lemma E, pulled-back characters miss Σ^d.

**Main computation.**
1. If χ(Δ²) ≠ 0, then χ is nonzero on the centre and [χ] ∈ Σ^∞ (Zaremsky, Corollary 3.8, quoted).
   In abelianized coordinates χ(Δ²) = Σ a_ij, since Δ² is the product of all A_ij.
2. P_n = H_n × Z with Z the centre, so a character vanishing on Δ² factors through the split projection
   onto H_n.
3. Forgetting a strand gives 1 → F_{n−1} → H_n → H_{n−1} → 1. The kernel survives the quotient by the
   centres because Δ_n² ↦ Δ_{n−1}². So χ(H_n) = (2−n)·χ(H_{n−1}), and with H_3 = F₂ this gives
   (−1)^n (n−2)! ≠ 0.
4. H_n has a finite (n−2)-dimensional K(π,1) (Aramayona–Martínez-Pérez, quoted).
5. Lemma S with d = n−2 gives [χ] ∉ Σ^{n−2}(P_n).

Correct. The consequence Σ²(P₄) = Σ^∞(P₄) = S(P₄) ∖ {Σ a_ij = 0} settles the case Zaremsky
(arXiv:1507.08597v1, p. 2) recorded as open, as quoted by the lane. I have not re-read that sentence.
Novelty check requested from z-status-a.

## 16. Problem 1.14, Σ¹ part (z1-14-rover-nek, 979b1f295a): three PASS

**`commuting-living-generators-give-sigma-one`: PASS.**
- Given two points of Cay_{χ≥0} and a path between them, push the path up by v_i^N, where v_i is a
  living generator commuting with the edge label s_i. Lifted edges exist by commutation.
- Joints between consecutive lifts go through δ_i v_i^N v_{i+1}^j and δ_i v_{i+1}^N v_i^j, which works
  because living generators pairwise commute. Every vertex has χ ≥ μ + Nc ≥ 0.
- Ascent and descent segments stay ≥ the endpoints. Correct.

**`rover-nekrashevych-characters-are-sum-invariant`: PASS.** Hom(V_d(G),R) ≅ {χ ∈ Hom(G,R) : ψχ = χ}.
Checked:
- ψχ is a homomorphism: (gh)|_x = g|_{h(x)} h|_x, and h permutes X.
- Tables are unique up to refinement: on a common piece, v g(w) = v′ g′(w) with v′ = vz forces z = ∅,
  because g maps C onto C; then faithfulness gives g = g′.
- Refinement invariance comes from iterating ψχ = χ along prefix codes. The homomorphism step follows
  from the composed table (u_i → v′_j f_j(z_i), f_j|_{z_i} g_i).
- (a) Real characters vanish on V_d, whose abelianization is finite (Higman).
- (b) g_(u) ~ g_(u′) by prefix replacement: both complements split into multiples of d−1 cones.
- (c) g_(u) = s ∘ ∏_x (g|_x)_(ux), with s ∈ V_d.
- (d) Φ = Φ_χ.

**`rover-nekrashevych-groups-have-full-bns-invariant`: PASS.** Σ¹(V_d(G)) = S(V_d(G)) for finitely
generated self-similar G.
- Step 1: cone-fixing elements generate V_d. For f ≠ 1 take a small cone c with c ∩ f(c) = ∅ and a
  cone left over; put t = f on c, f⁻¹ on f(c), and id elsewhere. Then t² = 1, t fixes a cone, tf fixes
  c pointwise, and f = t·(tf).
- Step 2: generation from S_V and s_(w_s), via (b) and (d).
- Step 3: a generating set with living generators (g₀)_(e_u) in disjoint small cones e_u ⊆ c_u.
- Step 4 verifies both hypotheses of the lemma: living generators have disjoint supports; each dead
  u ∈ S_V commutes with (g₀)_(e_u) (checked separately for y ∈ c_u and y ∉ c_u); dead s_(w_s) commute
  by disjointness.
- The corollary on finitely generated coabelian normal subgroups follows from BNS.
- Not an answer to 1.14, since the root asks for every Σ^m. Novelty unchecked.

## 17. Rips-complex lemmas for Problems 4.1, 4.4, 4.6 and 4.7: PASS, with duplicate hygiene

- **`thompson-f-has-no-contractible-rips-complex` (z4-01, 977c5cb6f6): PASS.** F is torsion-free
  (increasing homeomorphisms), contains Z^n through disjoint dyadic supports, has cd = ∞, and so has
  no contractible Rips complex. z4-01 retired its duplicate lemma `torsion-free-contractible-rips-complex-gives-type-f`
  at 69e968d38c. Its routes should require `contractible-rips-complex-gives-finite-classifying-space`;
  z-steward's cairn check will catch a dangling key. The conditional F routes require open claims and
  do not fire.
- **`fp-groups-have-simply-connected-rips-complexes` (z4-04, add9ced796): PASS.**
  - Fan triangles {g, p_i, p_{i+1}} reduce Rips edges to Cayley paths.
  - A relator loop of length ℓ ≤ L has vertex-set diameter ≤ ℓ/2 ≤ t, so it spans a simplex.
  - The result is independent of the generating set by Tietze moves.
- **`group-rips-complexes-are-cayley-graph-flag-complexes` (z4-04) and
  `rips-complex-of-a-group-is-a-flag-cayley-complex` (z4-07, 78bbac1172): both PASS.**
  - R_t(G,S) = Flag(Cay(G, B_S(t)∖{1})).
  - Vertex-simply-transitive locally finite flag complexes are Cayley flag complexes.
  - Item 2 of z4-07: finite stabilizers; free for torsion-free G, so X/G is a finite K(G,1).
  - Hygiene GAP: the two claims share item 1 and the (a)⇔(b)⇔(c) scheme, one for (n−1)-connected and
    one for contractible. Add a block-form `distinct_from` on one of them naming the other.
    z4-06 already retired its third copy.
- **`contractible-rips-groups-closed-under-direct-products` (z4-06, dc48b60c37 / f9154592e0): PASS.**
  - d_{S⊠T} = max(d_S, d_T), by padding with 1.
  - Simplices are exactly the sets whose projections are simplices, which is the categorical product.
  - The face-poset map to F(K)×F(L) has fibre over (a,b) equal to all nonempty subsets of a×b. That
    fibre has a maximum, so it is contractible, and Quillen's fibre lemma gives |K⊓L| ≃ |K|×|L|.
  - Model test (king graph: 1, 8, 12, 4, so χ = 0) checked.
- **`connected-rips-complexes-pass-to-direct-products` (z4-04, d140b64ad0): PASS on content, duplicate
  GAP.** It is the same theorem via the strong product and Quillen's lemma. Retarget its proof route
  to require `contractible-rips-groups-closed-under-direct-products` item 3 and keep only the
  (n−1)-connectivity consequence, or add `distinct_from`.
- **`counterexample-times-z-lacks-contractible-product-rips` (z4-06, f9154592e0): PASS.**
  - G × Z is of type F by 9a.
  - A contractible product Rips complex retracts onto |R_r(G,S)|, so all its homotopy groups vanish,
    so it is contractible (Whitehead). Then G is of type F, a contradiction.
- **`top-homology-of-free-complex-carries-wall-obstruction` (z4-06, f9154592e0): PASS.**
  - Dimension shifting gives Ext^i(K_j, M) ≅ H^{i+j}(G;M) = 0 for i ≥ 1 and j ≥ d, so K_N = im ∂_N is
    projective.
  - Hence Z_N = H_N(X) is a direct summand of C_N, and 0 → Z_N → C_N → … → C₀ → Z is a finite
    projective resolution with σ(G) = (−1)^{N+1}[H_N(X)].
- **Wiring routes (f9154592e0): PASS.** The equivalence cycles between 4.6 and (1.21 ∧ 4.7) are
  intended and do not fire, since a least fixpoint never fires a cycle.

## 18. Problem 1.13 stabilization (z1-13-sigma-inf, 982fdda9e3): PASS

**`bnsr-invariants-stabilize-at-cohomological-dimension`.**
- Novikov–Sikorav: Σ^q(G;Z) is the vanishing locus of Novikov homology in degrees ≤ q.
- pd_{ZG} Z = d kills Tor_i for i > d, so Σ^m(G;Z) = Σ^d(G;Z) for m ≥ d.
- Σ^m(G) = Σ²(G) ∩ Σ^m(G;Z) for m ≥ 2 (Bieri–Renz), which gives stabilization from max(d,2).
- Correct. Consequence: a negative answer to 1.13 needs cd = ∞.
- Model tests F₂^r and P_n are consistent (P_n: cd = n−1, and the sharper index n−2 of §15 agrees).

## 19. Problem 1.19 root now established (z1-19-raag-kernel, 53f5a8a98f and later): PASS

- **`bestvina-brady-main-theorem` (+ `-citation`)**, read from the publisher PDF. The quoted items
  are: (1) FP_{n+1}(R) ⇔ homologically n-connected; (2) FP(R) ⇔ acyclic; (3) finitely presented ⇔
  simply connected. H_L is the kernel of the all-ones character. This matches the standard statement.
- **`bestvina-brady-kernel-finiteness-theorem` (+ `-proof`): PASS.**
  - Item (2) is item (1) of the Main Theorem with the index shifted.
  - Item (1), n = 1: FP₁ = finite generation, which is equivalent to L being connected.
  - Item (1), n ≥ 2: F_n ⇔ finitely presented + FP_n(Z) (Brown VIII.7), which by Main Theorem (3)
    and (1) is L simply connected with H̃_{≤n−1}(L;Z) = 0. By Hurewicz that is (n−1)-connected.
- **Wiring.**
  - `raag-virtual-fn-kernel-conjecture-via-sigma-invariants` requires Theorem 7 (§14 PASS) and
    the finiteness theorem.
  - It establishes `raag-virtual-fn-kernel-implies-raag-fn-kernel`, which fires `zaremsky-1-19-by-yes`.
  - The negation `some-raag-virtual-fn-kernel-without-raag-fn-kernel` carries `refuted_by`.
  - The route body uses the Bieri–Renz kernel criterion (ker ψ of type F_n ⇒ [ψ] ∈ Σ^n(H)) without a
    node. It is standard, and the artifact flags it as recalled.
- **Verdict.** The establishment of the 1.19 root is correct. Zaremsky's conjecture 1.19 holds.
  Novelty check pending with z-status-a. Until it lands, relay as "reviewed, novelty unchecked".

## 20. Problem 1.18 reductions (z1-18-nested-bnsr, aab47dabcd): PASS

- **`bieri-sigma-property-forces-bnsr-constant-from-rank` (+ `-proof`): PASS.**
  - Definition: Zaremsky arXiv:1808.00634 Def. 1.4, conv_{≤m} of non-antipodal subsets.
  - Conic Carathéodory reduces a positive combination of non-antipodal classes to a linearly
    independent subfamily of size ≤ r = rank Hom(G,R), and subsets of non-antipodal sets stay
    non-antipodal.
  - So conv_{≤m} = conv_{≤min(r,s)} from there on, and the Σ-property turns that into a constant chain.
- **`type-f-bnsr-invariants-stabilize-at-dimension` (+ `-citation`): PASS.**
  - The quoted Ershov–Zaremsky §2.1 sentence ("if G is of type F with a finite classifying space of
    dimension n, then Σ^n(G) = Σ^∞(G)") matches the corroborating argument.
  - Superlevel subcomplexes Y ⊆ X have H_n(Y) = Z_n(Y) ⊆ Z_n(X) = 0 and nothing above, so essential
    acyclicity is automatic from degree n.
  - The homotopical half follows from Σ^m = Σ² ∩ Σ^m(−;Z) (§18).
- **`every-f-infinity-group-non-proper-bnsr-by-type-f-dichotomy`.** It requires one established claim
  and one open claim, so it does not fire. Correct.
- **Root reading.** The quote is verbatim, and the negation is correctly "some equality
  Σ^m = Σ^{m+1}", which is weaker than eventual constancy. The F₂^n chain example is right.
