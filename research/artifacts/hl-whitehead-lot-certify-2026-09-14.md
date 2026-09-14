# Certified asphericity census of labelled oriented trees (2026-09-14)

Lane hl-whitehead-lot-certify.

**Target.** Whitehead's asphericity conjecture in the ribbon case: every labelled oriented
tree (LOT) complex is aspherical.

**Method.** Run combinatorial asphericity tests with checkable certificates, exhaustively over
small reduced LOTs on MSI.

**Code and data.** `experiments/lot-asphericity-census/`, landed at 15ea956df, with outputs in
`out57/`.

## 1. Pinned sources

Every quotation below was read from the paper's PDF text (arXiv or the journal site).

### Definitions and reductions

Source: Harlander--Rosebrock, *Injective labeled oriented trees are aspherical*,
arXiv:1212.1943v6 (Math. Z. 287 (2017) 199--214), Section 1.

- **Relator convention.** "If e is an edge that starts at x, ends at y and is labeled by z,
  then r_e = xz(zy)^{-1}."
- **Reduced LOTs.** "A labeled oriented graph is called compressed if no edge is labeled with
  one of its vertices. It is called boundary reducible if there is a boundary vertex that does
  not occur as edge label, and boundary reduced otherwise. A labeled oriented graph is called
  interior reducible if there is a vertex with two adjacent edges with the same label that
  either point away or towards that vertex, and interior reduced otherwise. A labeled oriented
  graph which is boundary reduced, interior reduced and compressed is called reduced."
- **Reduction preserves homotopy type.** "Howie [7] observed that a labeled oriented tree G can
  be transformed into a reduced labeled oriented tree G_red so that K(G) and K(G_red) have the
  same homotopy type." Each move "amounts to a 3-deformation".
- **Why LOTs matter.** "Howie [6] showed that the finite case of the Whitehead conjecture
  reduces, up to the Andrews-Curtis conjecture, to the statement that presentations arising
  from labeled oriented trees are aspherical." Here [6] is Howie, Topology 22 (1983) 475--485.
- **Injective LOTs.** "Theorem 1.1 Injective labeled oriented trees are aspherical."

### Survey

Source: Rosebrock, *The Whitehead conjecture -- an overview*, Siberian Electron. Math. Rep. 4
(2007) 440--449.

- "On the other hand, any nonaspherical LOT is a counterexample to (WH)".
- "Each LOT-complex can be realized as a spine of a complement of a properly embedded
  ribbon-disc in the 4-ball."
- "(2) Howie 1985 [9]: LOTs of Diameter ≤ 3 are aspherical."
- **Complexity 2.** "Theorem 4.6. (Rosebrock 2007 [16]) LOTs of complexity 2 are aspherical."
- "Theorem 5.1. (Rosebrock 1990 [14]) There are reduced and compressed LOT-complexes, which
  are aspherical but not DR." So DR-based tests cannot certify every LOT.

### Local indicability

Source: Barreto--Minian, *Local indicability of groups with homology circle presentations*,
arXiv:2308.07447v1.

- "any connected 2-complex X with π1(X) locally indicable and H2(X) = 0 is aspherical
  (see [9, 10])".
- "Corollary 3.1. Let Γ be a LOT. If either I(Γ) or T(Γ) has at most one cycle, then G(Γ) is
  locally indicable." Here T(Γ) has an edge {λ(e), i(e)}, and I(Γ) an edge {λ(e), t(e)}.
- **Theorem 2.5.** Let P be a presentation of deficiency 1 with H1 = Z, whose relators are
  cyclically reduced with total exponent 0. If the minima multisets m(r_1), ..., m(r_k) of all
  relators but one are concatenable (Definitions 2.2 and 2.4), then G is locally indicable.
  - Remark 2.3 gives the maxima analogue.
- **Theorem 2.18.** Weakly concatenable relators (Definition 2.17), with H1 free abelian of
  rank n − k, give local indicability.
- "Local indicability of LOT groups is an open problem ... it is not even known whether all
  LOT groups are torsion-free."

### I-test

Source: Barmak--Minian, arXiv:1601.00604 (Proc. Roy. Soc. Edinburgh A 150 (2020) 871--895).

- Definition 2.5 defines the I-test.
- "Theorem 2.6. If P satisfies the I-test, it is aspherical." "Theorem 2.8. If P satisfies the
  I-test, K_P is DR."
- Remark 2.9: valid partial orderings extend.

### Weight test and relative vertex asphericity

Source: Harlander--Rosebrock, arXiv:1912.12512v2 (Canad. Math. Bull. 64 (2021) 292--305).

- **Definition 3.5.** Weights on corners, with (1) Σ ω(c_i) ≤ q − 2 on each 2-cell and (2)
  every reduced cycle in lk(L) of weight ≥ 2. It is introduced as the weight test "which implies
  the asphericity of L".
- "Theorem 2.4. If L is VA relative to K, then π2(L) is generated, as π1(L)-module, by the image
  of π2(K) under the map induced by inclusion. In particular, if K is aspherical, then so is L."
- **Theorem 3.4.** Let K = K_1 ∨ ... ∨ K_n ⊆ L, where the 2-cells of L have exponent sum 0 and
  the K_i are full. If lk+(L) is a forest relative to lk+(K), or lk−(L) is a forest relative to
  lk−(K), then L is VA relative to K.
  - Definition 3.2 collapses each lk±(K_i) to a point.
- Figure 1 is "A reduced injective non-prime LOT which does not satisfy the weight test (with
  any orientation of its edges)."

### Not pinned at primary source

- Howie 1985 (Trans. AMS 289): the AMS site returns a bot-check page, locally and from MSI.
- Rosebrock's complexity paper and his 2018 LMS Lecture Notes 446 chapter could not be fetched.
- So the diameter and complexity tests rest on the survey only, and `lot_primary.py` omits them.
- Whether small-vertex LOT censuses are already in print is not verified.

## 2. Checker and calibration

### `lot.py`: first tier

- `reduce_lot`: the three reductions.
- `test_diam`: survey only.
- `test_inj`.
- `test_IT`: Corollary 3.1.
- `test_cx2`: survey only.
- `test_itest`: for a LOT, v ⟂ q(r_e) = e_{i(e)} − e_{t(e)} forces v = ±(1, ..., 1).
- `test_weight`:
  - nonnegative weights, so simple cycles suffice;
  - a float linear program with cutting planes, then exact rational verification;
  - the minimum simple cycle is computed exactly with Dijkstra on G − e.

### `lot2.py`: second tier

- Theorems 2.5 and 2.18, on minima and on maxima (all generators inverted).
- **Label presentations.** Eliminate every non-label vertex by Tietze moves along the tree from
  a label root.
  - Each elimination is a 3-deformation, so K(Γ) ≃ K(P_L).
  - P_L has one generator per label and |L| − 1 relators of total exponent 0.
  - The construction asserts that each elimination relator becomes trivial.
- Theorems 2.5 / 2.18, the I-test and the weight test are then run on P_L, for every root.

### `lot3.py` / `lot_primary.py`: relative test

- Uses Theorems 3.4 and 2.4 with vertex-disjoint full sub-LOTs.
- lk± of a LOT complex are the graphs I(Γ) and T(Γ).
- Sub-LOTs are certified recursively.
- `lot_primary.py` uses only primary-pinned tests (no diameter or complexity shortcuts).

### Calibration (`controls.py`, 17/17; `controls2.py`, 13/13)

1. **Non-aspherical controls.** Both the I-test (over every v with entries in {−2, ..., 2}) and
   the weight test fail on:
   - the trefoil Wirtinger labelled oriented circle, where one relator is redundant;
   - a repeated-relator presentation.
2. **Barmak--Minian Example 3.1.** The I-test passes and the weight test fails.
3. **Barmak--Minian Example 2.3.** The weight matrix matches the paper and its orderings
   verify.
4. **Huck--Rosebrock Figure 1 LOT.** The weight test fails on all 64 orientations, as the paper
   states, and the LOT is injective.
5. **Barreto--Minian examples.**
   - Definition 2.2: m(r) = {b, c, b, a}.
   - Example 2.8: m(r1) = {a, b}, m(r2) = {d, b}, and Theorem 2.5 passes.
   - Example 2.19: weakly concatenable, and Theorem 2.18 passes.
   - All 81 labellings of the 5-vertex path where I or T has at most one cycle also pass the
     Theorem 2.5 test, consistent with Corollary 3.1 being derived from Theorem 2.5.

## 3. Census

### Enumeration (`census.py`)

- For each free tree shape on n vertices, all orientations with edge 0 fixed. Reversing every
  edge gives a homeomorphic complex via x ↦ x^{−1}.
- All labellings with compressed labels, keeping only boundary reduced and interior reduced
  LOTs.
- Classes are counted up to shape automorphisms and global reversal, and each class is
  certified.
- Every LOT on at most n vertices reduces to a reduced LOT on at most n vertices with
  homotopy-equivalent complex, so the census covers all LOTs on at most n vertices.

### First-tier results (job 779879)

| n | classes | diam | inj | IT | cx2 | weight | survivors |
|---|---|---|---|---|---|---|---|
| 5 | 206 | 78 | 58 | 70 | 0 | 0 | 0 |
| 6 | 6234 | 496 | 1636 | 4102 | 0 | 0 | 0 |
| 7 | 279943 | 3016 | 46934 | 229404 | 436 | 52 | 101 |

### Second tier on the 101 survivors (job 780536)

- 86 pass Theorem 2.5 on a label presentation.
- 15 remain. All have I(Γ) and T(Γ) with cyclomatic number exactly 2, and 4 or 5 distinct
  labels.
- 12 of the 15 contain a twin pair: edges x→y labelled z and x→z labelled y, or the terminal
  version.
  - A full check corrected an earlier "every sampled survivor" remark.
- The full list is in `out57/survivors2_n7.txt`.

### Relative and Tietze steps (jobs 781706, 784058)

- **Relative test on the 15.** Harlander--Rosebrock Theorems 3.4 and 2.4, with vertex-disjoint
  full sub-LOTs certified recursively (`survivors3.py`, `lot3.py`). It certifies 10; 5 remain.
- **Tietze closure on the 5.** Breadth-first elimination (`lot4.py`): whenever a generator occurs
  once in a relator, substitute and delete. Each move is a 3-deformation. All 5 reach a
  presentation satisfying Barreto--Minian Theorem 2.5 (`survivors4_n7.txt`).

### Primary-only pipeline (`census_primary.py`, `lot_primary.py`; jobs 781699, 784526)

- **Tests used.** Primary-pinned tests only, with no diameter or complexity shortcut.
- **Presentation-level and relative results.** For n = 3 to 6, (inj) or (IT) certifies every
  class.
  - n = 3, 4, 5, 6 give 2, 8, 206 and 6234 classes.
  - For n = 7, the first passing test is:
    - inj 48142, IT 231212;
    - itest 51, weight 159;
    - L-bm25 354, relative 12;
    - none 13.
- **Tietze closure.** `survivorsp4.py` certifies all 13 remaining classes (`outp57/survivorsp4_n7.txt`).
  - Only 2 of these 13 contain a twin pair.

## 4. Status and gap

- **ESTABLISHED (unreviewed) at most six vertices.** `lot-complexes-with-at-most-six-vertices-are-aspherical`
  (ead4a8919). This is the primary-only pipeline: the injectivity and one-cycle criteria certify
  all 8450 classes on 3 to 6 vertices.
- **ESTABLISHED (unreviewed) at most seven vertices.** `lot-complexes-with-at-most-seven-vertices-are-aspherical`.
  The primary pipeline (job 781699) certifies 279930 of 279943 classes. The Tietze closure (job
  784526) certifies the last 13.
- **Not done: eight vertices.** The first-tier arrays 780531 and 783971 ran out of memory on
  most shapes (a class dedupe set in the first, a certificate map in the second) and were
  cancelled. `census8p.py` (constant memory, cheap tests only) was written but never run.
- **Open.** The general LOT asphericity question is untouched by a finite census;
  `contractible-2-complex-minus-a-cell-is-aspherical` contains it.
- **Exact structural gap.** No infinite class was proved.
  - The 13 hard seven-vertex classes share no structural feature identified so far (only 2 have a
    twin pair).
  - What is known: every one of them has a Tietze presentation whose minima are concatenable.
  - Candidate theorem, not attempted: every reduced LOT has a Tietze presentation satisfying
    Barreto--Minian Theorem 2.5 or 2.18. It would give local indicability of all LOT groups, which
    is open according to their introduction.
