# Idea lane nh-nonsofic-transfer (2026-09-13)

Target: `non-hyperlinear-group`. Lens: carry the existing non-sofic existence mechanism over to unitary approximations. This is an ideas file only. It claims no theorem and edits no node.

## The mechanism, from the source

`openai-leavitt-unit-nonsofic` establishes the first nonsofic group, `L_(F_2)(1,2)^x`. The chapter source pinned at `c1168433:official/counterexample.tex` (lines 142–174 and 213–230, read for this lane) runs in four steps.

1. **Kun's expander decomposition** (cited there as Kun19, Theorem 1). A sofic approximation of a property (T) group, after changing `o(N)` edges, is a disjoint union of uniform expanders. There may be many components.
2. **Expander matching** (the chapter's Proposition 2.3). The compressors `t_i Gamma t_i^(-1) <= Gamma` inject-match components. Since `t_1 J t_1^(-1) <= Gamma`, the J-generators preserve Gamma-components at almost every vertex. One component is selected and repaired into a single expander.
3. **Kun–Thom expander-centralizer theorem** (cited there as KT19, Theorem 1.1). Take a sofic approximation of `K x J` in which the K-graph is one expander on the whole set. Then `J` is LEF.
4. **The witness.** `J ≅ V`, which is finitely presented, infinite and simple, so not LEF. Hence G is not sofic.

**Where it is permutation-specific.**
- Components are sets. The unitary analogue is the central decomposition of an approximate commutant, and it carries multiplicity.
- In step 3, almost-automorphisms of an expander round to an exact finite group. For unitaries, the commutant of a gapped block is a matrix algebra over its multiplicity space.
- The repository already records exactly this failure in `research/artifacts/unitary-expander-nonhyperlinearity-audit-2026-09-04.md`. There, an exactly invariant swap stays at squared HS distance `1-1/d^2` from the old factor.

## Approaches

### A1. An exact commutant-dimension skeleton, then make it robust
- **Idea.** Let `pi` be any finite-dimensional unitary representation of G.
  - Since `t_1 Gamma t_1^(-1) <= Gamma`, we get `pi(Gamma)' <= pi(t_1 Gamma t_1^(-1))' = pi(t_1) pi(Gamma)' pi(t_1)^*`.
  - The two sides have the same dimension, so they are equal.
  - Since `pi(J) <= pi(Gamma)'`, this gives `pi(t_1 J t_1^(-1)) <= pi(Gamma)'`.
  - So every word `w = [t_1 j t_1^(-1), gamma]` lies in the kernel of every finite-dimensional representation. No (T) is used.
  - A robust version would give nonhyperlinearity directly from one nontrivial `w`, without needing J to be non-LEF. It needs the dimension count to survive for approximate representations: a gap for the conjugation Laplacian of `Gamma` and of `t_1 Gamma t_1^(-1)`, up to `o(n^2)` HS-dimension.
- **Would prove.** Nonhyperlinearity of the Leavitt configuration, under an HS-gap hypothesis weaker than flexible stability.
- **Kill test run.** A repo grep for the exact regime and the robust regime.
- **Result.**
  - The exact regime is `fd-invisibility-of-compression` (identity `rho(Lambda)=rho(E)` across FD), as cited inside `approximate-collapse-for-kt-compressor`.
  - The robust regime is the OPEN "(AC) wall" `approximate-collapse-for-kt-compressor`.
  - The limit-algebra form is impossible: in the bilateral shift crossed product `(⊗_(k in Z) M_2) ⋊ Z`, the implementing unitary conjugates `⊗_(k>=0) M_2` onto `⊗_(k>=1) M_2`, a proper subalgebra. So equal "dimension" does not force invariance in a II_1 factor, and any proof must count at finite level.
- **Verdict.** Killed as a new route; it duplicates the AC wall. The no-(T) exact lemma is a clean way to state the exact face.

### A2. A halvable corner in characteristic zero feeding a rank model
- **Idea.**
  - `halvable-corner-makes-elementary-groups-nonsofic` gets nonsoficity from `rk(e) = 2 rk(e)`.
  - A trace kills a halvable idempotent the same way: `tau(e) = sum tau(t_i s_i) = 2 tau(e)`.
  - Run this over `L_C(1,2)` with complex rank or trace models: every hyperlinear model of `EL_n(L_C(1,2))` should induce a unital trace-like model of the ring, which cannot exist.
- **Would prove.** `EL_n(L_Z(1,2))` is nonhyperlinear.
- **Kill test run.** Read `leavitt-algebra-has-no-unital-rank-model` and `non-linear-sofic-group`.
- **Result.**
  - The first node says explicitly that models of the unit group need not be multiplicative on R: the isometries are never inverted inside `EL_n(R)`. So ring-level rank or trace obstructions don't reach group-level approximations.
  - The characteristic-two Kaplansky route in `non-linear-sofic-group` is still open.
- **Verdict.** Killed. A group approximation induces no trace on R.

### A3. A unitary Kun–Thom Theorem C, via the coset wreath
- **Idea.**
  - `binary-free-and-ordinary-coset-wreaths-share-hyperlinearity` makes hyperlinearity of `(C_2) wr_(G/Gamma) G` equivalent to scalar relative embeddability of `L(Gamma) <= L(G)`.
  - Kun–Thom Theorem C (sofic actions of an infranormal Kazhdan pair have a G-invariant Gamma-fixed algebra) is operator-algebraic in form.
  - Prove its analogue for relatively embeddable inclusions; non-normality of a Theorem E pair then forbids it.
- **Would prove.** Nonhyperlinearity of the Kun–Thom wreath.
- **Kill test run.** A repo grep, and the II_1 shift example from A1.
- **Result.** The weakest sufficient statement is already recorded as the OPEN `kt-wreath-relative-canonical-actor-exactification`. The shift example shows that a relative-commutant version without finite-level counting is false in general.
- **Verdict.** Killed as a new route; it duplicates the existing endpoint.

### A4. Bounded-block monomial approximations: a real intermediate class (SURVIVES)
- **Idea.** Replace `Sym(n)` by `U(r) wr Sym(n)`, block-monomial unitaries with a **fixed** block size r and continuous labels, in normalized HS. Candidate theorem: the OpenAI configuration groups, in particular `L_(F_2)(1,2)^x`, are not `U(r) wr Sym`-approximable for any fixed r. Sketch:
  - **Permutation parts.** HS-closeness of block-monomial matrices forces their permutation parts to agree at most points. So the permutation parts are a sofic approximation of `G/N'`, where N' is their Hamming-trivial kernel. Steps 1–3 then apply to `(Gamma/(Gamma ∩ N')) x (J/(J ∩ N'))`.
  - **Case `V ∩ N' = 1`.** J is LEF, a contradiction.
  - **Case `V ⊆ N'`.** On the Loeb space `X = prod_omega I_n`, the labels give measurable maps `u: J x X -> U(r)` satisfying `u_(jk)(x) = u_j(x) u_k(x)` for almost every x. So they are genuine homomorphisms `V -> U(r)` almost everywhere.
  - **Finishing that case.** V is finitely generated, infinite and simple, and f.g. linear groups are residually finite, so each such homomorphism is trivial. Hence `rho(v) ≈ 1` and `tau(rho(v)) -> 1`, contradicting trace-faithfulness.
  - **Why V is dichotomous.** V is simple, so `V ∩ N'` is 1 or V.
- **Would prove.** The first group that is not approximable by bounded-block monomial unitaries.
  - This is strictly more than nonsoficity: continuous phases cancel traces that permutations cannot.
  - It lands exactly on the multiplicity wall of the unitary audit: the argument breaks only as `r -> infinity`.
- **Kill test run.**
  - Read `uniformly-discrete-block-monomial-images-are-sofic`. That fence needs block labels uniformly HS-discrete (UDB1), so continuous `U(r)` labels are outside it.
  - A web search for approximation by `U(1) wr S_n` in the HS metric found no equivalence with soficity or hyperlinearity. The search was not exhaustive.
- **Result.** Nothing on main kills it. The unchecked steps are:
  - (a) that the permutation parts really satisfy the Hamming relator tests needed for Kun's decomposition after discarding the o(1) set where labels are far from 1;
  - (b) the measurable-cocycle bookkeeping on the Loeb space;
  - (c) that the configuration's distinctness tests pass to `G/N'`.
- **Verdict.** Survives, as a candidate intermediate theorem with a concrete proof sketch. It isolates the gap to nonhyperlinearity as block-size growth.

### A5. An HS version of Kun's decomposition (the localization face)
- **Idea.** Prove the unitary analogue of step 1: after an `o(1)`-HS correction, an approximate representation of a Kazhdan group is a direct sum of blocks with a uniform gap on the non-scalar part of their conjugation action. Then steps 2–3 run with commutant algebras in place of components.
- **Would prove.** The rigidity route to a non-hyperlinear group, through the Leavitt or Kun–Thom configurations.
- **Kill test run.** A repo grep.
- **Result.** It is the OPEN localization face (L), `actor-commutant-has-liftable-masa-in-every-model`. Its own text names Kun–Thom Lemma 2.3 as the Hamming analogue and points to `research/artifacts/unified-compression-rigidity-2026-09-12.md` §3.
- **Verdict.** Killed as a new route; it duplicates an existing face.

## Summary

The transfer has been mapped in detail on main: the AC wall, face (L), vertex rounding (H1) and the exactification endpoint. Three of these approaches are duplicates of it, and one is killed outright.

The one new, testable idea is **A4**. It is a non-approximability theorem for bounded-block monomial unitaries, proved by combining the permutation mechanism with pointwise Loeb rounding of fixed-size unitary labels. It sits strictly between nonsoficity and nonhyperlinearity, and its failure point is exactly the multiplicity wall. That makes it the natural next deep-lane candidate from this lens.
