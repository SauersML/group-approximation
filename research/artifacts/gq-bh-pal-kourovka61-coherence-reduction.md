# bh-pal-kourovka61, pass 2: the F_∞ route, the Bleak–Quick template, and a sharper coherence gap

Lane bh-pal-kourovka61, 2026-09-18 (afternoon). Target: T8 of `gq-bh-pal-scope.md`, i.e. an
explicit, literature-free finite presentation of `CT_P(Z)` (Kourovka 17.61) for Lean. No priority is
claimed. Notation follows `class-transposition-presentation-has-central-kernel`. `Γ_P` is the
transposition presentation (R1)–(R3), `ε: Γ_P → CT_P(Z)` its evaluation map, and `K = ker ε`, which
that node proves central. `PC` is the group of piecewise-canonical permutations, which equals `CT_P(Z)`
by `piecewise-canonical-permutations-are-transposition-products` (elementary).

## 1. The "type F_∞" route to 17.61 (checked first, as asked)

The referee remark in `ct-p1-and-ct-p2-always-generate-ct-p1-union-p2` (fac0259d6) points to item 2
of `ct-p-z-is-a-one-vertex-k-graph-full-group`. That item is already the positive answer to 17.61 on
main, and it is literature-dependent: type `F_∞` comes from Li, arXiv 2110.04505.
- **Read at source this pass** (`gq/src/li2110/main.tex`):
  - l.2171, Cor. `cor:OneVertex`, a finite one-vertex higher rank graph;
  - l.2140, the general finite-k-graph form;
  - l.2125, the `Z^k_{≥0}` Garside specialization it comes from.
- **Hypotheses that match:**
  - `Λ_P` is a finite one-vertex `(|P|+1)`-graph with `p ≥ 2` edges of colour `p`;
  - `X = ∂Ω` is closed and invariant.
- **To confirm at referee time:**
  - The choice `Y = X`. The node writes `e_P = ∅`. We did not locate Li's definition of `X(v; 𝔢)`,
    so whether the right choice is `e_P = ∅` or `e_P = {0}` (with `d^{-1}(0) = {1}`) is unchecked.
  - The identification `I_l ⋉ ∂Ω = G_Λ`, which the node marks "not re-read".
- **Verdict.** The route is sound modulo those two reading checks. It settles 17.61 only with Li
  (and Matui, and Farsi–Kumjian–Pask–Sims) as inputs, so it cannot be the Lean route: Mathlib has
  none of this. It deserves a referee pass as its own node, as the remark says.

## 2. The P = ∅ template does not exist elementarily

Bleak–Quick, arXiv 1511.02123 (TeX read; `gq/src/bq/bq.tex`), Thm `thm:infpres` (l.477). They prove
exactly our (R1)–(R3), with cones for boxes, for `V`. Their proof (§§3–6, l.1068–1118, l.2210ff)
does two things:
1. It verifies Thompson's finite presentation of `V` in the Cannon–Floyd–Parry form (CFP Lemma 6.1,
   fourteen relations) inside the presented group.
2. It derives the infinite presentation from that.

So even for `P = ∅` the infinite presentation rests on a known finite presentation. For `P ≠ ∅` the
only printed presentations are Martínez-Pérez–Matucci–Nucinkis's (1609.07058, via Stein complexes
and Geoghegan's theorem). An elementary proof has to supply the Stein-complex step itself.

## 3. New lemmas (lane proofs, elementary)

**Lemma T (every lift is a transport).** Let `h ∈ Γ_P` and let `β` be a box partition such that
`g = ε(h)` is canonical on every cell of `β`. Then `h t(E,F) h^{-1} = t(gE, gF)` for all disjoint
boxes `E, F`, each contained in a cell of `β` (possibly the same cell).

*Proof.*
1. Write `h` as a word `w`.
2. By Lemma 4 of the central-kernel node, some refinement `S` of `β ∧ {E, F, Z∖(E∪F)}` has all
   cells regular along `w`.
3. Choose `k ∈ N_{P'}` such that `U_k(E)` and `U_k(F)` refine `S`.
4. By Lemma 2, `t(E,F) = ∏_{u ∈ U_k(Z)} t(κ_E u, κ_F u)`.
5. By Lemma 3, each factor goes to `t(g κ_E u, g κ_F u) = t(κ_{gE} u, κ_{gF} u)`, since `g` is
   canonical on `E` and on `F`.
6. Lemma 2 reassembles the product into `t(gE, gF)`. ∎

This removes all word bookkeeping from the transport argument: regularity is a property of
`ε(h)`, not of the word. Item 2 of the central-kernel node is the case `g = 1`.

**Lemma P (permutation relations are free).** Consider the Higman–Thompson-type presentation of `PC`
from the Ore category of ordered natural bases. Its generators are the splits `x_{n,i,p}` and the
permutations `σ ∈ Sym(n)`. Its relations are:
- (a) the relations of `Sym(n)`;
- (b) far commutation of two splits;
- (c) the colour exchange `p`-then-`q` = `q`-then-`p`, with the residue bijection
  `j + pl ≡ j' + ql' (mod pq)`;
- (d) naturality of permutations under splits.

Fix frames `β_n`. Send `σ` to its canonical copy in `Γ_{β_n} ≅ Sym(n)`, and send `x_{n,i,p}` to
*any* lift `X_{n,i,p}` of the frame change `β_{n+p−1} → β_n·(i,p)`. Then (a) and (d) hold exactly
in `Γ_P`.

*Proof.*
- (a) is Lemma 1 of the central-kernel node.
- For (d), split each cell transposition of `β_n` by (R3) into transpositions of sub-boxes of cells
  of `β_n·(i,p)`, conjugate by `X^{±1}` with Lemma T, and reassemble with (R3). ∎

**Corollary R (sharp form of the gap).** Assume the Ore presentation above presents `PC`. Call this
Fact O. It is the MMN infinite presentation for the complete laws `Σ_P`. An elementary proof needs:
- validity: two trees with the same leaf set are related by (b) and (c), by induction on the root
  prime, sketched in the lane notes;
- Ore's theorem for the category of ordered natural bases;
- the free `PC`-action on chart bases.

Then `K` is generated by the *defects* of the relations (b) and (c) for the chosen lifts, that is,
by the central elements `L R^{-1}`, where `L = R` is an instance of (b) or (c).

By (d) and centrality, a defect depends only on `(n, p, q)`, not on the positions. Hence:

    (R1)–(R3) present CT_P(Z)  ⟺  for some choice of lifts, every far-commutation and
    colour-exchange square closes exactly in Γ_P.

*Proof.* The lifts define a homomorphism from the Ore presentation to `Γ_P / ⟨defects⟩`, inverse to
`ε` on generators. So `K ⊆ ⟨defects⟩ ⊆ K`. ∎

**Lemma C (canonical lifts of doubled elements).** Let `s = t(0(2), 1(2))`, and let `φ_a` be the
compression homomorphism `Γ_P → Γ_P`, `t(A,B) ↦ t(κ_{a(2)}A, κ_{a(2)}B)`. It is well defined because
(R1)–(R3) are preserved.
- For `g ∈ PC` choose natural ordered bases `b` and `c = g b` of the same size. Put
  `I(g) := ∏_k t(φ_0 b_k, φ_1 c_k)`. This is a product of commuting transpositions, independent of
  `(b, c)` by (R3), and a lift of the involution `2x ↔ 2g(x)+1`.
- For every `γ ∈ Γ_P`: `φ_1(γ) s φ_1(γ)^{-1} = I(ε(γ)) = φ_0(γ)^{-1} s φ_0(γ)`.
  *Proof:* by (R3), `s = ∏_k t(φ_0 b_k, φ_1 b_k)`; apply Lemma T to each factor.
- Consequently `φ_1(γ) φ_0(γ)^{-1}` depends only on `ε(γ)`. This is the first choice-free lift of a
  non-torsion family (`φ_0(g^{-1})φ_1(g)`) that we know of.
- It reproves `φ_0(z) = φ_1(z)` for `z ∈ K`. It does not by itself kill `K`: every identity it gives
  is between compressed copies, and `z` itself never appears uncompressed.

## 4. What is left, and the plan

- **Gap 1 (Fact O).** The Ore-category presentation of `PC`. It is elementary, but it is several
  pages: validity, Ore localization, and covering by a free action. No literature theorem is needed.
- **Gap 2 (squares).** Close the (b) and (c) squares exactly for one explicit frame system. The comb
  frames `β_n = (0(2), φ_1 β_{n−1})` are self-similar: every `X_{n,i,p}` with `i ≥ 2` can be chosen
  as `φ_1(X_{n−1,i−1,p})`, and (b)/(c) instances away from cell 1 are then `φ_1`-images of smaller
  instances. So induction on `n` leaves only the instances touching cell 1. Those still need a
  proof.
- **Only then:** the finite truncation (`ct-p-z-has-a-finite-class-transposition-presentation`), in
  the Bleak–Quick "deep relations are conjugates of shallow ones" style, and the Lean.
- **Lean status.** Nothing written. Per the rules, Lean comes after the research closes. The one
  formalizable piece today is the central-kernel theorem together with Lemmas T, P and C, which is
  about 1–2 kLOC on top of box arithmetic; the repo has no box/RCWA library yet. The kourovka59
  lane's `Statement.lean` is not on main yet, so there is nothing to reuse.

## Lesson for general BH

A presentation-by-involutions of a full group is exactly as hard as the simple connectivity of its
Stein complex. Local tools, even in exact form, reduce the question to the 2-cells of the Ore
category and no further:
- transport (Lemma T): conjugation acts correctly on everything fine enough;
- finite symmetric subgroups;
- choice-free doubled lifts.

The kernel is central and generated by the defects of the far-commutation and colour-exchange
squares. For BH host design this is the right bookkeeping. A host of type (A) built as a full group
of a complete `k`-graph-like Cantor algebra gets its finite presentation from finitely many square
checks plus self-similarity, not from global geometry. And a central defect that is
position-independent must be killed by one explicit computation per colour pair.
