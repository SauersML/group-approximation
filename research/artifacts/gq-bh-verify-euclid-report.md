# bh-verify-euclid: adversarial check of `euclidean-building-lattices-lie-in-permutational-bh-class`

Target: bh-groupoid 38b9f88f9. Consequence under check: bh-integrate's route de3934873 puts the Titz
Mite–Witzel C̃₂ lattices and their five simple kernels Γ̌ in B_A. This is a lane check, not an external
review. Sources read at source: Li arXiv:2110.04505v2 (§`s:Gars-deg`, `thm:deg`, `lem:deg--t<d`,
condition (F) at l.1454–1456) and Ciobotaru–Le Bars arXiv:2601.13092 (TeX in `gq/src/bh-groupoid/`).
Standard building facts are recalled, not re-read.

**Overall verdict: PASS, with two wording nits and one trust note.** No FAIL. No GAP that affects the
conclusion.

## (1) Box calculus and composition lemma: PASS

- **Tiles and boxes.** The tile `{0 ≤ α_i ≤ 1}` is bounded by walls `H_{α_i,0}` and `H_{α_i,1}`, so it
  is a union of alcoves. Translation by `ϖ_i ∈ P^∨` preserves the wall set, since `β(ϖ_i) ∈ Z`. It may
  permute special types, which is exactly why the node tracks phases.
- **Special vertices.** Base-type special vertices of a subsector are nonnegative integer combinations of
  the `ϖ_i`, because `Q^∨ ⊆ P^∨ = ⊕Zϖ_i`. So subsectors are tile-aligned.
- **Convexity (re-derived).** I checked that the box `⊕[0,m_i+1]ϖ_i` equals conv(C, D), where C is the
  alcove at the origin and D = v − A_0 is the alcove at the far corner v.
  - Every positive root is a nonnegative combination of the α_i. So on the box, β runs from 0 at the
    origin to β(v) at v.
  - Hence every root containing C and D contains the box.
  - For m = (1,0), m' = (0,1) and β = α_1+α_2 we get β(v_M) > max(β(v_m), β(v_{m'})). So the box of
    shape m∨m' is not conv(p ∪ p'), and minimal common extensions need not be unique. This is why the
    node's disjoint-ideal argument, rather than the Ã₂ girth argument, is the right one.
- **Composition lemma (re-derived).**
  - In the model, the two-leg curve has every positive root strictly increasing, so its gallery type is
    reduced.
  - In the building, p's and q's embeddings agree on the shared marked tile T, including the type map.
  - So the glued gallery has reduced type, hence is minimal, hence lies in any apartment Σ containing
    C_p and D_q.
  - Σ contains conv(C_p, D_p) = p. It contains conv(C_q, D_q) = q because C_q ⊂ T ⊂ p.
  - Uniqueness of the (m+m')-box is conv(C_p, D_q).
- **Finite alignment.** Two distinct boxes of shape M from one tile cannot both be the initial M-box of
  a common extension. With local finiteness, cℭ ∩ dℭ is a finite disjoint union. No link girth is needed,
  so the argument is correct in every type.

## (2) Cylinder exchanges: PASS

- Parallel sectors share a subsector. After moving to a base-type special vertex deep in it, that
  subsector is tile-aligned in both tilings, by (1).
- `U_{l,n}` and its complement are each determined by finitely many tiles, so they are clopen.
  Compactness gives finitely many pieces.
- On each piece, γ is the prefix replacement with group element `g_{d'}^{-1}γg_d`, which is a basic
  bisection of `𝒢_Γ^D`.

## (3) Complete reducibility: PASS (nit N1)

- I re-derived the counts:
  - column sums: `Σ_b M_j(b,a) = c_{φ(a)}`;
  - orbit–stabilizer: `Σ_a w_a M_j(b,a) = w_b c'_{φ(b)}`;
  - phase totals: `c_φ W_φ = c'_{φ+1} W_{φ+1}`, hence `Πc = Πc'` on each phase cycle.
- **Eigenvectors.** Phase-rescalings of 1 and of w are positive left and right eigenvectors of M_j for
  the same ρ = (Πc)^{1/L}.
- **Block argument (re-derived).** If class 1 accesses class 2:
  - the right eigenvector gives ρ(M_22) = ρ and forces ρ(M_11) < ρ;
  - the left eigenvector forces ρ(M_11) = ρ;
  - so there are no off-diagonal blocks, and no transient trivial classes since ρ > 0.
- **Regularity.** The counts depend only on phase because thick irreducible Euclidean buildings of
  dimension ≥ 2 are regular (panel sizes depend only on type).
  - Successor tiles correspond bijectively to chambers at fixed Weyl distance from the far chamber, with
    lengths adding. This holds because D_t lies on a minimal gallery C_t → D'.
- **N1.** The sentence "the same argument applied to Σ_j M_j" is not literally valid, since the phase
  rescalings of the Perron vectors can differ between colours. The conclusion still holds: each M_j is
  completely reducible, so every single-colour step can be reversed inside its colour class. By (UFP*)
  every morphism factors into such steps, so reachability is symmetric, and the pieces are strongly
  connected with no morphisms between them.
- **N2 (scope).** For dimension 1 (trees) the counts are not phase-only when valences vary. The statement
  should read "dimension ≥ 2". Tree lattices are virtually free and in B_A by other nodes.

## (4) Ciobotaru–Le Bars topological freeness: PASS (trust note T1)

- **Exact statements, live text.**
  - `prop minimal` (l.1156): G discrete countable, acting cocompactly by automorphisms on an irreducible
    locally finite affine building, need not be type-preserving (l.1096). Then Λ_F(G) = ch(X^∞) and G is
    of general type.
  - `prop top free general type` (l.1567): G of general type with a proper action gives a topologically
    free action on Λ_F(G).
  - Standing assumptions: thick, with thick X^∞ (l.405–430, `lem id bd id X`).
- **Match.** A discrete Γ ≤ Aut(X) acts properly, so the node's hypotheses are exactly these.
- **The node's use.** Step 5 needs only this: an element fixing an open set of chambers at infinity is
  trivial. An isotropy arrow (S,n,g,S) forces g to fix the endpoint of every sector in the cylinder.
- **T1.** 2601.13092 is an unrefereed preprint. Its TeX keeps many author notes ("redo with the new
  definition of barycenters", "does not seem correct"), all inside `\begin{comment}` blocks. I checked
  the comment ranges: 296–322, 396–407, 416–418, 619–775, 858–1039, 1042–1088, 1099–1153, 1257–1540,
  1779–1855.
  - The live chain behind topological freeness has no live flags: `def generic` l.777, the barycenter
    proposition, `prop generic full measure` l.834, `cor exist generic triple general type` l.1251,
    `cor everywhere generic triple` l.1556, `prop top free` l.1567.
  - That chain was not re-derived here.

## (5) Li `thm:deg` hypotheses: PASS

- **P = N^{r+1}.** It is left reversible and right Noetherian, has conditional lcms, and S_P = the
  nonzero {0,1}-vectors (Li's k-graph example).
- **The category ℭ.**
  - It is left and right cancellative. I re-derived both: compare γ, then initial parts.
  - Units are exactly degree 0, the finite K_a.
  - (UFP*) holds by the composition lemma.
  - There are finitely many objects (cocompactness) and finitely many morphisms of each degree (local
    finiteness).
- **(F).** It holds because ℭ is right cancellative (Li l.1456).
- **(t<d).** It follows from `lem:deg--t<d`, which needs at least two loops modulo right units at every
  object for every s ∈ S_P.
  - Loops mod units at a are counted by M^{(n)}(a,a). Step 3 plus thickness (ρ > 1) makes this ≥ 2 after
    rescaling.
  - Mixed degrees come from products of loops.
  - The O_2 colour contributes two loops.
- **Unit groups.** They are finite, hence F_∞.
- **Skew product (Step 4, cited construction).** I checked that L has finite index in Z^r, since each
  class has loops of every colour. I also checked that the image of the cycle semigroup in the finite
  group L/(⊕k_jZε_j) is a group, as a finite subsemigroup of a group.

## (6) Stabilized type (A) comparison: PASS (lane lemma, dependency not re-derived)

- **Scope match.** `degree-category-full-groups-stabilized-have-type-a-actions` (with route
  `degree-category-comparison-type-a-proof`) allows finite unit groups and several strongly connected
  pieces, and takes finite presentation as a hypothesis. That hypothesis is supplied by (5).
- **Type (A) as used on main.** The definition is: faithful, fp, fg stabilizers, finitely many orbits of
  2-subsets; no high transitivity.
  - Faithfulness comes from Step 5.
  - Pair orbits are recorded by Boolean atoms times pieces.
  - The stabilizer of U is a product of full groups of restrictions, each isomorphic to a piece's full
    group by comparison, so it is fp.
- **Not re-derived here:** Steps 4–5 of `stabilized-kgraph-full-group-clopen-action-proof`.

## (7) Titz Mite–Witzel lattices: PASS

- **Source.** `titz-witzel-simple-kazhdan-cat0-lattices-exist` quotes arXiv:2509.05054, Theorem A: the
  universal covers are exotic C̃₂ buildings of thickness q+1 (q = 2, 3). They are locally finite, with
  finite quotient complexes Y_i^q, and Γ_i^q acts freely and cocompactly.
- **Hypotheses.** C̃₂ is an irreducible type of dimension 2. So Γ_i^q is a discrete cocompact
  automorphism group of a locally finite, thick, irreducible Euclidean building, and the theorem applies.
- **The kernels.** The kernels Γ̌_i^q have finite index, so they are themselves such lattices. They are
  also subgroups of Γ_i^q ∈ B_A.
- **Conclusion.** The five TMW kernels lie in B_A, conditional on this lane proof and on T1.

## Lesson for general BH

- The general-type proof is sound in structure. Its only non-elementary imports are Li's `thm:deg`,
  whose hypotheses I checked line by line, and topological freeness from an unrefereed preprint.
- Complete reducibility comes from double counting.
- The one real subtlety across types is that minimal common extensions of boxes are not unique beyond
  Ã₂, and the disjoint-ideal argument handles it.
- The rank-2 "rigid coding" machine is therefore reliable input for the host program. The remaining risk
  for the TMW consequence is concentrated in T1, the preprint's barycenter machinery.
