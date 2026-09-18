# Where the proved 2-to-2 instances come from, verbatim (2026-09-18)

> **CORRECTION, 2026-09-18 (post-referee).** Section 1's conclusion is wrong and
> the question in the title is **not** answered by this file. Section 1 rules out
> TR18-006's references `[4]` and `[2]` but never identifies `[12]`, although the
> abstract line quoted below names it. `[12]` is Khot--Minzer--Safra, *On
> Independent Sets, 2-to-2 Games and Grassmann Graphs*, ECCC TR16-124 / STOC
> 2017, and it **does** construct a 2-to-2 game (its Definition 1.4, Transitive
> 2-to-2 Game; its Theorem 1.8, a reduction from regular `Gap3Lin`), already
> single-alphabet with `l`-spaces on both sides meeting in an `(l-1)`-space.
> TR18-006's own Appendix C says "The Grassmann graphs and their potential
> application to the 2-to-2 Games problem were proposed in `[12]`." So a second,
> natively 2-to-2 instance family exists, and section 1's own hedge -- "the only
> 2-to-2 *instances* named anywhere are those of the papers it cites" -- includes
> it. The claim was returned to OPEN; see its `## Attempts` section. The
> quotations below are accurate and are kept; only the inference drawn from them
> in section 1 is withdrawn.

Citation file for `kms-2to2-instances-are-padded-dkkms-selector-lecs`. It answers
the part of live need `1cb0e45a` that
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses` left open: whether
the Khot--Minzer--Safra 2-to-2 instances satisfy hypotheses (E) and (M) of
`efficient-branch-selectors-list-decode-honest-outer-labels`.

Two PDFs were fetched on 2026-09-18 and their text extracted:

* **KMS** = Subhash Khot, Dor Minzer, Muli Safra, *Pseudorandom Sets in
  Grassmann Graph have Near-Perfect Expansion*, ECCC Report No. 6 (2018),
  `https://eccc.weizmann.ac.il/report/2018/006/download/`, 56 pages.
* **DKKMS** = Irit Dinur, Subhash Khot, Guy Kindler, Dor Minzer, Muli Safra,
  *Towards a proof of the 2-to-1 games conjecture?*, ECCC Report No. 198
  (2016), `https://eccc.weizmann.ac.il/report/2016/198/download/`, 33 pages.

All credit for the constructions and theorems quoted is theirs. Nothing below
reproves anything of theirs. Quotation marks mark text copied from the PDFs;
mathematical symbols are transliterated (subscripts flattened, `\ell -> l`,
`F_2` for the binary field), and nothing else is altered.

## 1. KMS builds no instance: the finding

**KMS contains no reduction and no instance construction.** Its content is the
Grassmann Expansion Hypothesis (its Theorem 1.8 / Theorem 2.4) and the Fourier
machinery that proves it. Searching the extracted text, the only 2-to-2
*instances* named anywhere are those of the papers it cites. The relevant
verbatim lines:

* **Abstract, page 1.** "We prove that pseudorandom sets in Grassmann graph
  have near-perfect expansion as hypothesized in [4]. This completes the proof
  of the 2-to-2 Games Conjecture (albeit with imperfect completeness) as
  proposed in [12, 3], along with a contribution from [2]."
* **Page 3.** "The focus of this paper is the combinatorial hypothesis itself,
  which we are able to prove, in turn proving the 2-to-2 Games Conjecture,
  completing this line of work."
* **Appendix C, "Grassmann Graphs to the 2-to-2 Games Theorem", page 55.**
  "We summarize the chain of implications from the Grassmann graphs to the
  2-to-2 Games Theorem. The chain is roughly: Grassmann Expansion Hypothesis
  =[4]=> Linearity Testing Hypothesis =[2]=> 2 to 2 Games Conjecture [12, 3]."
  And: "In [3], the authors formulated a Linearity Testing Hypothesis and
  showed that it implied the 2-to-2 Games Conjecture (with imperfect
  completeness)."
* **References, page 48.** "[3] Irit Dinur, Subhash Khot, Guy Kindler, Dor
  Minzer, and Muli Safra. Towards a proof of the 2-to-1 games conjecture?
  Electronic Colloquium on Computational Complexity (ECCC), 23:198, 2016." and
  "[4] Irit Dinur, Subhash Khot, Guy Kindler, Dor Minzer, and Muli Safra. On
  non-optimally expanding sets in Grassmann graphs. Electronic Colloquium on
  Computational Complexity (ECCC), 24:94, 2017." and "[2] Boaz Barak, Pravesh
  Kothari, and David Steurer. Small-set expansion in shortcode graph and the
  2-to-1 conjecture. Personal communication."

So the instance family behind the 2-to-2 Games Theorem is the one built in
[3] = DKKMS ECCC TR16-198, which is exactly the family whose membership is
already established in
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`. Reference [4] is
about expansion in Grassmann graphs and builds no game; [2] proves one
hypothesis from another.

## 2. The statement KMS proves, and the shape it is stated in

* **Definition 1.3, page 2.** "An instance `U_(2<->2)` of the 2-to-2 Game
  `[F_2^l]` problem consists of `n` variables `x_1,...,x_n` taking values over
  (the alphabet) `F_2^l` and `m` constraints `C_1,...,C_m` where each
  constraint is of the form `T_ij x_i (+) T'_ij x_j in {b_ij, b'_ij}`,
  `T_ij, T'_ij` are `l x l` invertible matrices, and `b_ij, b'_ij in F_2^l`."
* **Theorem 1.4, page 2.** "For every constant `eps > 0`, there exists a
  sufficiently large integer `l = l(eps)` such that Gap 2-to-2 `[F_2^l]`
  `(1-eps, eps)` is NP-hard."
* **Footnote 2, page 2.** "(2) It was proposed with more general constraints
  (rather than the special case with linear structure described herein) and
  with `2-to-1` constraints (rather than with `2-to-2` constraints described
  herein; the conjecture was referred to as the 2-to-1 Conjecture). Both these
  are non-issues however: the current and preceding works [12, 3, 4] now prove
  the conjecture with linear structure and the constraints are easily
  reinterpreted as being 2-to-1 constraints (hence proving the 2-to-1
  Conjecture as well, which in any case is morally equivalent to the 2-to-2
  Conjecture)."

Footnote 2 is the only place where the passage between the 2-to-1 and the
2-to-2 presentations is discussed, and it is an assertion, not a construction.

## 3. What DKKMS actually builds

* **Section 4.2, "The Full Reduction", page 23.** "In this section we construct
  the instance of the 2-to-1 game `G_folded`. The construction follows the
  reduction described in the introduction, but is written formally as a
  constraint graph and not a two player game. We first describe a constraint
  graph that is not folded, `G_unfolded = (A,B,E,Pi,Sigma_A,Sigma_B)`, and then
  change it into the final instance `G_folded = (A~,B,E~,Pi~,Sigma_A,Sigma_B)`
  by identifying sets of vertices in `A`."
* **Vertices, page 23.** "`A = {(U,L) | U in U, L in Gr(X_U,l), L cap H_U =
  {0}}`" and "`B = {(V,L') | V in V, L' in Gr(X_V,l-1)}`".
* **Constraints, page 23.** "We let `Sigma_A = {0,1}^l` and
  `Sigma_B = {0,1}^(l-1)`. `sigma in Sigma_A` is interpreted as a linear
  function `sigma : L -> F_2` and `sigma in Sigma_B` is interpreted as a linear
  function `sigma : L' -> F_2`. This can be done, say, by fixing an arbitrary
  basis for each subspace `L, L'`. The constraint between `(U,L)` and `(V,L')`
  accepts pairs `(sigma,sigma')` iff `sigma|_(L') = sigma'`. It is clear that
  this is a `2 : 1` constraint."
* **Folded constraints, page 24.** "The constraints in `G_folded` are defined
  to be the aggregate of the constraints in `G_unfolded`: a constraint between
  `C` and `(V,L')` accepts a pair of assignments `(sigma,sigma')` if the
  unfolding of `sigma` satisfies all of the constraints between members of `C`
  and the assignment `sigma'` for `(V,L')`. The weights are summed up as well."
  And: "It is clear that the constraints are at most `2 : 1` but it might seem
  that some or many of the constraints are completely unsatisfiable. The
  following claim implies that this is not the case."
* **Claim 4.3, page 24.** "Let `C in A~`, let `sigma = A~(C)`, and for each
  `(U,L) in C` let `A(U,L) = sigma~_U|_L` be its unfolding. Then for any
  subspace `D` and for any `(U_1,L_1),(U_2,L_2) in C` such that
  `D subseteq L_1 cap L_2`, `A(U_1,L_1)|_D = A(U_2,L_2)|_D`."
* **Theorem 1.2, page 4.** "Assume Hypothesis 3.6. Then for every constant
  `delta > 0`, for a sufficiently large constant `|Sigma_A|`, given a
  2-to-1-Game `G = (A,B,E,Pi,Sigma_A,Sigma_B)` it is NP-hard to distinguish
  between: YES case: there is a coloring satisfying `1-delta` fraction of the
  constraints of `G`. ... NO case: no coloring satisfies more than `delta`
  fraction of the constraints of `G`."

DKKMS therefore delivers a **bipartite constraint graph with two alphabets of
different sizes**, `|Sigma_A| = 2^l` and `|Sigma_B| = 2^(l-1)`, and 2-to-1
constraints. That is not literally an instance of KMS Definition 1.3, which
wants one alphabet `F_2^l` on both sides and `l x l` invertible matrices.

## 4. The gap, stated precisely

Neither paper writes down a map from `G_folded` to an instance of
KMS Definition 1.3. KMS footnote 2 asserts the passage in the other direction
("the constraints are easily reinterpreted as being 2-to-1 constraints"), and
the bus lemma of `e2-w2-audit-ugc1` on `two-to-two-games-theorem` (2026-09-18)
shows that the *generic* per-constraint 2-to-2 -> 2-to-1 bipartization is not
gap preserving, so footnote 2 cannot be read as a generic transformation
either.

The claim `kms-2to2-instances-are-padded-dkkms-selector-lecs` supplies the one
map in the missing direction, the free-bit padding of `Sigma_B`, checks that it
lands in Definition 1.3 with invertible `T, T'` and `b != b'`, and checks that
hypotheses (E), (M) and (B) transport with the DKKMS parameters unchanged.

## 5. What the parameters are, from the paper text

Quoted in `dkkms-selector-membership-proof` and re-used unchanged here:

* **(E)**, uniform directions: `tau = 2^(l-1-2k)`, from the edge law of
  Section 4.2 step 2 ("Choose a random `L' in Gr(X_V,l-1)` and a random
  `L in Gr(X_U,l)` such that `L' subseteq L`") together with the vertex
  condition `L cap H_U = {0}`.
* **(M)**, marginal ratio: `K = 1`, from step 1 ("Choose a `k`-tuple `U` ...
  uniformly at random") and the fact that the validity probability does not
  depend on `U`.
* **Folding convention**: Lemma 4.1 and Definition 4.2, quoted in
  `dkkms-selector-membership-proof` as (Q3) and (Q4). A class label is
  `sigma : R -> F_2` on a representative `l`-space `R` with `R cap H_U = {0}`,
  and unfolds at `(U,L) in C` to `A(U,L) = sigma~_U|_L`, the restriction of the
  `(H_U,h_U)`-extension.

Neither `tau` nor `K` is changed by the padding, because neither depends on the
alphabets: both are properties of the edge law `mu` and the annotation
`(w_e, a_e, x_e)` alone.
