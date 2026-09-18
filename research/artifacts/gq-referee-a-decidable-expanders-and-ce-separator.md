# Referee report (gq-referee-a, proof-gap lens): a decidable group with coarsely embedded expanders, and the CE separator

**Reviewed** (lane bh-refute, 8093ecc84), read on origin/main. Both proofs are inline:
- `decidable-group-with-coarsely-embedded-expanders-exists`;
- `coarse-embeddability-separates-boone-higman`.

**Verdict: PASS for both.** There are three nits, all on the first node. N1 matters for the singular-diagram case. For
the citation lens:
- the Osajda and Gruber–Sisto quotations;
- Lyndon–Schupp V.4.3;
- the fact that property A implies CE (Yu);
- the Haagerup-host nodes.

## 1. `decidable-group-with-coarsely-embedded-expanders-exists`
- **Gr'(1/24) from Theorem 2.7 (the author asked about this).**
  - Let `p` be a piece with essentially distinct lifts `p_1 ⊂ Θ_n` and `p_2 ⊂ Θ_(n')`. Essentially distinct implies
    `p_2 ≠ p_1` (N3).
  - If `|p| ≥ λ girth Θ_n`, Theorem 2.7 says the label of `p_1` occurs on no other path, a contradiction. So
    `|p| < λ girth Θ_n`, and likewise at `n'`.
  - A simple closed path `γ` containing a lift lies in that lift's component and has `|γ| ≥ girth`, so `|p| < λ|γ|`.
  - The labelling is reduced by Theorem 2.7, so `Γ` is Gr'(1/24).
  - `M = G(Γ)` equals Osajda's `⟨Γ | Θ⟩`: the fundamental cycles of a spanning tree are simple closed paths, and they
    normally generate all closed-path labels. ✓
- **The Greendlinger step (the author asked about this).**
  - A face with one exterior arc `e` and at most three interior arcs, each shorter than `λ|∂Π|`, has
    `|e| > (1 − 3/24)|∂Π| = (7/8)|∂Π|`.
  - The interior vertices of `e` have degree 2, so `e` is a contiguous cyclic subword of `w`.
  - `∂Π` lifts to a simple closed `γ` with `|γ| ≥ girth Θ_i`, so `girth Θ_i < (8/7)|w|`. ✓
  - *The singular case* (N1). An extremal disk component is attached to the rest of `D` at one vertex `v`, and a
    single Greendlinger face could have its exterior arc through `v`. Then `e` is not contiguous on `∂D`.
    - The classical argument uses the strong form: Lyndon–Schupp V.4.3 gives at least two such boundary faces in a
      component with more than one face, and one of them avoids `v`.
    - A one-face component is a single relator, whose boundary minus `v` is still one arc of length at least
      `|γ| > (7/8)|γ|`.
    - Say which form is used. As written, "applied to an extremal disk component" leaves this implicit.
- **The Dehn algorithm (the author asked about this).**
  - `N` is computable. Girths strictly increase, which is the standing hypothesis, and `Θ` and `m` are recursive
    (Remark 2.8). So compute girths until one reaches `(8/7)|w|`.
  - *Correctness.* A cyclic conjugate of `w` is trivial iff `w` is. At each nonempty trivial stage, the Greendlinger
    face gives a match with `i ≤ N`, since `|e| > |γ|/2`. So "no match" certifies `w ≠ 1`.
  - *Termination.* Each replacement multiplies by a relator, preserving the element, and shortens the word, because
    `|γ ∖ p| < |γ|/2 < |p|`. So the algorithm halts. It reaches the empty word iff `w = 1`.
  - Recomputing `N` from the new, shorter word each round is legitimate, since `N` is monotone in `|w|` (N2). ✓
- **Items 1 and 2.**
  - Theorem 3.2 and Corollary 3.3 (cited) give item 1.
  - For item 2, a finitely generated subgroup's inclusion is Lipschitz and uniformly proper, because word balls are
    finite. So it is a coarse embedding, and non-coarse-embeddability passes up to `K`. ✓

## 2. `coarse-embeddability-separates-boone-higman`
- **Subgroup-closure of CE (the author asked about this).** All proper left-invariant metrics on a countable group
  are coarsely equivalent. The restriction to a subgroup is again proper and left-invariant, and the inclusion is
  isometric. So CE is closed under subgroups and isomorphism. ✓
- **Item 1.**
  - `M ∉ CE` is finitely generated with solvable word problem, which gives (S2).
  - So CE separates iff every finitely presented simple group lies in CE. In that case Boone–Higman would put `M`
    inside a CE group, a contradiction. ✓
- **Item 2: the expander in `S`, with uniform control (the author asked about this).**
  - `Θ_n → Cay(M)` is isometric, and `M → S` is a coarse embedding with fixed control functions `ρ_±`.
  - So the composites `Θ_n → S` all satisfy `ρ_-(d) ≤ d_S ≤ ρ_+(d)` with the same `ρ_±`. That is a coarsely embedded
    expander with control independent of `n`.
  - The same holds for the Kazhdan host. ✓
- **The class kill (the author asked about this).**
  - Subgroup-closure and `M ∉ CE` mean `M` embeds in no member of a class inside CE.
  - *Haagerup ⊆ CE.* For a proper cocycle `b`, `‖b(g) − b(h)‖ = ‖b(h^(−1)g)‖`. This is bounded on finite balls, which
    gives upper control, and tends to infinity with `|h^(−1)g|` by properness, which gives lower control.
  - *Exact ⊆ CE.* This is Yu's theorem.
  - The listed Haagerup hosts are the cited nodes. ✓
- **Item 3.** The comparison with exactness is correct, including the Osajda cubical groups that are in CE but not
  exact.

## Nits
- **N1 (Greendlinger, the singular case).** State the two-face form, or the one-face-component argument above, which
  ensures the exterior arc avoids the attaching vertex.
- **N2 (Dehn).** Say explicitly that free and cyclic reduction and the computation of `N` are repeated each round.
- **N3 (Gr').** Note that "essentially distinct" implies "distinct", which is all that Theorem 2.7's "some other path"
  needs.
