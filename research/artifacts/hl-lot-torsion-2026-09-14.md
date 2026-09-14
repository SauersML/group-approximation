# Torsion in LOT groups: crossing-pair class, free splittings, exact gap (2026-09-14)

Lane hl-lot-torsion. Target: `lot-groups-are-torsion-free` (OPEN). This lane executes the top survivor of
ideas-bridges-2. No famous problem is decided, and nothing here has been reviewed.

## 1. Result

**Proved (ESTABLISHED, unreviewed, no novelty claimed).**
- `crossing-pair-two-cycle-lot-groups-are-locally-indicable` (route `crossing-pair-two-cycle-lot-li-proof`).
  - Hypotheses: a compressed, interior reduced LOT whose left graph `T(Γ)` has cyclomatic number 2 and
    contains a crossing pair `e = (v, u, t_e)`, `f = (u, v, t_f)` with `t_e ≠ t_f`, plus the separation
    condition of the claim.
  - Conclusions: `G(Γ)` is locally indicable, hence torsion-free, and `K(Γ)` is aspherical.
  - The mirror form uses `I(Γ)`.
- `lot-group-free-splittings-force-torsion` (route `lot-group-free-splittings-torsion-proof`).
  - A free splitting `G(Γ) ≅ H * Z` with `H ≠ 1` forces `H` to be perfect with torsion (Klyachko).
  - So torsion-freeness of LOT groups implies free indecomposability.

**Imports added.**
- `barreto-minian-concatenable-minima-give-local-indicability`: Theorem 2.5, pinned from the TeX source.
- `locally-indicable-2-complex-with-h2-zero-is-aspherical`: pinned from Barreto--Minian's introduction.
  The primary Howie papers were not read.

**Open node added.**
- `reduced-lots-have-concatenable-tietze-presentations`, with route
  `lot-torsion-free-via-concatenable-tietze-presentations` into the target.
- This is the census lane's "candidate theorem", now a Cairn node.

## 2. Sources

### Barreto--Minian, arXiv:2308.07447v1, TeX source `locind.tex` (e-print fetched 2026-09-14)

- Definitions 2.2 and 2.4, Theorem 2.5, the I-value remark, and the LOT minima sentence: quoted verbatim in
  `barreto-minian-concatenable-minima-citation` and `crossing-pair-two-cycle-lot-li-proof`.
- Corollary 3.1, verbatim: "Let $\Gamma$ be a LOT. If either $I(\Gamma)$ or $T(\Gamma)$ has at most one
  cycle, then $G(\Gamma)$ is locally indicable."
- Their Theorem 3.x (`\label{ciclosetiq}`) handles several cycles of `T(Γ)`.
  - Hypotheses: the other components of `T(Γ)` are trees whose vertices label properly labelled cycle edges.
  - Method: products of cycle relators (Lemma `ciclo`) and Theorem 2.18.
  - That class is different from the crossing-pair class; overlap was not measured.
- Open status, verbatim: "Local indicability of LOT groups is an open problem (that would imply asphericity
  of the associated presentations). In fact, it is not even known whether all LOT groups are torsion-free."

### Rosebrock, *The Whitehead conjecture – an overview*, Siberian Electron. Math. Rep. 4 (2007), 440--449

Fetched from semr.math.nsc.ru; the text below comes from pdftotext.

- p. 445, verbatim: "If K is a 2-complex and g ∈ π1 (K) a nontrivial element of finite order, then
  π2 (K) ≠ 0. If g k = 1 and g k is trivialized by r in π1 (K) then (1 − g)[r] is nontrivial in π2 (K)."
  The pdftotext rendering reads `g k` for `g^k` and `6=` for `≠`, and is interleaved with the caption of
  Figure 4.
- p. 445, verbatim: "Is there a LOT-group with a nontrivial element of finite order? This also is still
  open."
- p. 445, verbatim: "A LOT is a subcomplex of an aspherical 2-complex because if one adds x1 = 1 as a
  relator then one has a balanced presentation of the trivial group which 3-deforms to a point."

### Not pinned

- Howie 1982 (Math. Z.) and Howie 1985 (Trans. AMS): AMS bot-check, not read.
- Recalled and not used in any node:
  - Yajima's characterization of ribbon 2-knot groups by Wirtinger presentations of deficiency one;
  - Kim's and Satoh's identification of virtual and welded knot groups;
  - Stallings' theorem on lower central quotients.
- The arXiv API search from this machine returned no entries, so no systematic literature search was done.

## 3. Method and observations

**(a) Levels of the infinite cyclic cover.**
- Take `t = x_r` and `a_{v,k} = t^k x_v t^-(k+1)`. The relators become
  `a_{i,k} a_{λ,k+1} = a_{λ,k} a_{t,k+1}` for every edge and level.
- The system expressing level `k+1` through level `k` has as exponent matrix the reduced incidence matrix of
  `I(Γ)`. It is triangularly solvable exactly when `I(Γ)` is a spanning tree.
- In that case `G(Γ)` is an ascending HNN extension of a finitely generated group. That class is already
  inside Corollary 3.1, so this route gives no new class.
- Finite level strips of the cover have `χ = 2 - n`, `H_2 = 0` over every field and `H_1 ≅ Z^{n-1}`. Any
  torsion in `G(Γ)` lives in the fundamental group of such a finite subcomplex. This was not landed; it is a
  reformulation, not a narrowing.

**(b) Elimination is contraction.**
- Eliminating `v = i(e)` through `v = λ(e) t(e) λ(e)^-1` changes every multiset of minima by contracting
  the left edge `{v, λ(e)}`.
- The one exception is the crossing partner of `e`, whose multiset becomes the four-letter multiset
  `{u, u, t_e, t_f}`. The case analysis is Step 2 of the proof route.
- A four-letter multiset with a private letter can be concatenated where a 2-cycle of pairs cannot. That
  is the whole mechanism.

**(c) Census data.** Of the 13 seven-vertex classes that needed Tietze closure
(`experiments/lot-asphericity-census/outp57/survivorsp4_n7.jsonl`):
- all have `T` and `I` of cyclomatic number 2;
- 12 were certified after one elimination, and 12 satisfy the crossing-pair criterion on one side;
- the one that fails is `[(0,5,1),(1,5,3),(2,6,0),(4,2,6),(4,6,2),(5,1,3)]`, which the census needed two
  eliminations for.

## 4. Model test

`experiments/lot-torsion/crossing_pair_check.py`, seed 20260914, 300000 random trees on 8--10 vertices
(Prüfer codes, random orientations and labels), keeping compressed, boundary and interior reduced LOTs.
Log: `experiments/lot-torsion/crossing_pair_check-run.log`.

- **Scale.** 4409 reduced LOTs, 16902 (crossing pair, omitted relator) instances on `T(Γ)` and on the
  reversed LOT.
- **Minima.** The Step 2 prediction equals `lot2.minima` after `lot4.eliminate` in every instance. A first
  run showed 40 mismatches, all a bug in the test script (a `Counter` merged the keys when `t_e = t_f`).
  After the fix: 0.
- **Criterion.** The Step 5 criterion agrees with `lot2.concat_order` in every instance, passing and
  failing. This is the negative control.
- **Tester.** Every predicted pass passes `lot2.test_bm25`.
- **Coverage.** 124 sampled reduced LOTs have both graphs of cyclomatic number at least 2. All 124 have one
  side exactly 2, and 65 satisfy the criterion. The sample is not uniform over isomorphism classes.

## 5. Exact gap

- **G1.** LOTs where both `T(Γ)` and `I(Γ)` have cyclomatic number at least 2 and no side of cyclomatic
  number 2 carries a separated crossing pair. This includes every LOT with both sides at least 3.
- **G2.** Iterated eliminations. After the first one the labels are words, and the case analysis of Step 2
  must be redone for weakly labelled trees.
  - The one hard seven-vertex class outside the criterion needs two eliminations.
  - A general form is `reduced-lots-have-concatenable-tietze-presentations` (OPEN).
- **G3.** Torsion itself. Nothing here produces a torsion candidate. By
  `lot-group-free-splittings-force-torsion`, a search for free splittings `H * Z` is a special case of a
  torsion search.
- **Review items.**
  - Confirm the Howie 1982/1985 statements behind `locally-indicable-2-complex-with-h2-zero-is-aspherical`.
  - Compare the crossing-pair class with Barreto--Minian Theorem 3.x and with Howie 1985 for novelty.
