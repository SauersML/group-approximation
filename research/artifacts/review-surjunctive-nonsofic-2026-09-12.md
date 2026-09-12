# Independent review: a surjunctive nonsofic group

Reviewer lane `review-surjunctive`, 2026-09-12. Adversarial review requested by
`gottschalk-positive` for the root `surjunctive-nonsofic-group-exists`.

## Verdict: PASS

The proofs hold as written. No gap, missing hypothesis or counterexample was
found. Two trust surfaces remain; they are listed under "Not verified" below.

## Scope reviewed

* `research/artifacts/rf-lamp-wreath-surjunctivity-2026-09-11.md` (Theorem 1,
  Corollary 2).
* `research/artifacts/finitary-split-extension-surjunctivity-2026-09-11.md`
  (Theorem 0, Lemma 5.1, Corollaries 6 and 7).
* `research/artifacts/surjunctivity-graph-folds-2026-09-11.md`, the peer node
  `graph-folds-over-surjunctive-groups-are-surjunctive`.
* The claim and route nodes wired into the root, and the literature inputs.

## 1. Theorem 1 (residually finite lamps over a surjunctive base)

Checked line by line.

* **Lemma 1.1 (transplant).** The identity `tau(pi^* y) = pi^*(tau_Omega y)`
  holds with the left-shift convention `tau(x)(l) = mu((x(l m))_m)`.
  Injectivity transfers because `pi` is onto.
* **Lemma 1.2 (density).** Pulled-back solutions agree with any target on a
  separated finite set; the image is closed by compactness.
* **Lemma 2.1 (separation).** `w' w^-1 = (n' n^-1, 1)` when the
  `G`-coordinates agree, and lies outside `N` otherwise. A finite-index
  normal `A_0` avoiding the finitely many nontrivial values exists because
  `A` is residually finite.
* **Coordinates and (2.1).** `H(n,g) = H(n',g')` iff `g = g'` and `n, n'`
  agree mod `A_0` on `S`; the right action multiplies fibre coordinates on
  the right by `A_0 n_1(g^-1 s)`.
* **Lemma 2.2.** `{g : g u = s} = G_s g_u`, so `Z_s` is a finite union of
  right `G_s`-cosets. For `k in G_U`, `(kg)^-1 s = g^-1 s` on `U`, so
  `tau_U` commutes with left `G_U`-translation.
* **Lemma 2.3 (slices).** When `nu_m(g)` is trivial on `U\V`, the product
  `a . nu_m(g)|_U` keeps the `U\V` coordinates fixed, and `tau_U` reads
  exactly as `tau_V` on the slice.
* **Lemma 3.1 (coset region).** `RP \ R` is a finite union of right
  `K`-cosets; the output at `k h_i` reads `y` at `k eta f` with `eta`
  independent of `k`. So `Psi` is a genuine automaton over `K`. Injectivity
  of `Psi` follows from injectivity of `rho` by a common extension off
  `R ⊔ E`; ontoness and the finite-memory form of `rho^-1` follow as stated.

### Proposition 4.1 (peeling), the step most likely to break

* **(c).** Slicewise extensions of maps commuting with `G_(U')` commute with
  `G_U`, which is contained in `G_(U')`. So `rho_U` is an injective
  finite-memory map commuting with left `G_U`-translation.
* **(b), choice of `V`.** `g not in Q_U` gives some `s in U` with
  `g F_U` missing `Z_s`, so `V != U`.
* **(b) step 1.** For `U'` not inside `V`, a point `h in gP` in `Q_(U')`
  would give `h F_(U')` meeting `Z_s` for some `s in U'\V`, but
  `gP F_(U')` lies in `g F_U`. The inverse of a bijection that fixes a
  coordinate for every input also fixes it.
* **(b) steps 2-3.** Lemma 2.3 applies at every window point, because all
  windows lie inside `gP` (each `P_i` contains `1`). Nested slicing is
  associative.
* **(b), the induction on stages.** Since the order refines cardinality,
  every proper subset of `V` precedes `V` and no later subset lies in `V`.
  On the shrinking windows the partial composite equals the slicewise
  extension of the `V`-setting composite, which is `rho_V` at stage
  `j_V - 1`. Stage `j_V` returns `y`, and every later stage is the identity
  at `g`.
* **Bijectivity.** An intersection of right cosets of the `G_s`, `s in U`, is
  empty or a right coset of `G_U`, so `Q_U` is a finite union of right
  `G_U`-cosets. Commuting with `G_U` gives left-invariant rules. Lemma 3.1
  applies with `K = G_U` and the finite alphabet `B^(Abar^U)`.
* **Degenerate cases.** `Q_U = empty` gives `rho_U = id`; `G_U` of finite
  index is allowed; stabilizers may be infinite and the action need not be
  faithful or transitive. None of these affects the argument.

## 2. Theorem 0 and the doubles

* **Theorem 0.** The only points where the proof is not literally the
  wreath proof were checked:
  * `H_U = ker(q iota_(U,S) p_U)` gives `H_U\W ~= Q_U x G`, with (T) the
    correct transplant;
  * (A2) applied to the pair `(V, U)`, together with compatibility of the
    `iota`, gives `c^U_m(g) = c^V_m(g)` off the strata of `U\V`;
  * (A3) at `U` gives left `G_U`-equivariance;
  * slices over left cosets `c Q_V` do not depend on representatives,
    because every map in the induction commutes with left `Q_V`-translation.
* **Instance (I1).** (A1)-(A3) hold for `p_S` = restriction.
* **Lemma 5.1.** Checked:
  * `alpha` is an action;
  * `Phi` agrees on the two copies of `Gamma`;
  * `Psi` respects the conjugation relation;
  * `Psi Phi(ghat) = ghat` and `Phi Psi(e_(g x_0)) = e_(g x_0)`.

  Independently, the kernel of the fold map meets every vertex stabilizer
  trivially, so it acts freely on the Bass--Serre tree. The quotient graph
  has two vertices and `|G/Gamma|` edges, so the kernel is free of rank
  `|G/Gamma| - 1`, consistent with the basis `{e_x : x != x_0}`.
* **Instance (I2).** Letters of `alpha_g(w)` lie in `g(letters(w) ∪ {x_0})`,
  which gives (A2). A pointwise stabilizer of `S` preserves `X \ S`, which
  gives (A3).

## 3. The graph-folds extension (peer node)

* **Section 3 lemma.**
  * The loop formula `[g.ell] = product b_(g e_j)^eps_j` needs only that `G`
    fixes every vertex, so `g.ell` is again a based loop. Tree-path
    corrections are absorbed because `b_e = 1` for tree edges.
  * (A2) follows by deleting symbols outside `S`.
  * For (A3), a pointwise stabilizer of `S` sends edges outside `S` to edges
    outside `S`.
* **Section 4 enlargement.**
  * `f_v` is injective, so `f_v(a)` lies in `f_v(j_e(A_e))` iff `a` lies in
    `j_e(A_e)`. Reduced words stay reduced, and `J` is injective.
  * The retraction `r` respects the edge relations by (4.1).
* **Section 5.**
  * `ker r` meets every conjugate of every `G_v` trivially, so it acts freely
    on the Bass--Serre tree.
  * `N\W/G_v ~= r(W)/r(G_v) = G/G` is a single vertex per type, so `G` fixes
    every vertex of `Y`.
  * The based covering identification intertwines the actions.

## 4. Literature inputs, read from the sources

* **Kun--Thom, arXiv:2608.06222v3** (PDF, pages 1-4, read 2026-09-12).
  * Theorem A: "Let Gamma be an infranormal but not normal subgroup of G, and
    suppose that both Gamma and G have Kazhdan's property (T). Then
    (Z/2Z) wr_(G/Gamma) G and the group double G *_Gamma G are not sofic."
  * Theorem E: for a prime power q and r, d >= 3, Gamma = EL_r(F_q[x_1..x_d])
    and G = EL_r(F_q[x^(+-1)]) semidirect SL_d(Z) are residually finite
    Kazhdan groups, and Gamma is infranormal but not normal.
  * This matches `kun-thom-nonsofic-wreath` and
    `kt-pair-group-double-is-nonsofic`, and the wreath there is the
    permutational one of Theorem 1 with `A = Z/2Z`, `X = G/Gamma`.
* **Bowen--Chapman, arXiv:2511.06586v1** (abstract page, no v2 exists).
  * Problem 1.1: "are all surjunctive groups sofic?"
  * The abstract adds that "answering this problem in the negative in the
    category of groups is still out of reach" while no nonsofic group was
    known.
  * A surjunctive nonsofic group is a negative answer, as the root states.
* **Arzhantseva--Gal, Ann. Math. Blaise Pascal 27 (2020) 125-130**
  (PDF, pages 1-3).
  * Theorem 1 and its abstract: a split extension with a finitely generated
    residually finite kernel and a surjunctive quotient is surjunctive. They
    note this was unknown even for `G x Z`.
  * Theorem 1 here needs no finite generation of the kernel, and
    `direct_sum_(G/Gamma) Z/2Z` is not finitely generated. So Arzhantseva--Gal
    does not already cover the witness; the new theorem goes beyond it.
* **Standard facts (F1)-(F4)** are textbook
  (Ceccherini-Silberstein--Coornaert, *Cellular Automata and Groups*):
  Curtis--Hedlund--Lyndon and inverses of bijective automata; subgroup
  heredity of surjunctivity; residually finite groups are surjunctive.
* **Finite generation.** `EL_r` over a finitely generated commutative ring,
  `r >= 3`, is generated by finitely many elementary matrices. With
  `SL_d(Z)` and one lamp, and the transitive action on `G/Gamma`, this
  generates the wreath.

## 5. Adversarial tests

* **Known cases.**
  * Trivial `G`: `direct_sum_X A` is residually finite, hence surjunctive.
  * Trivial `A`: `W = G`.
  * `G = Z`, `X = Z`, `A = Z/2Z`: the lamplighter group is amenable, hence
    surjunctive.

  All three agree with the theorem.
* **Consistency with the linear lane.** Surjunctivity implies stable finiteness
  of `F_p[W]`, which agrees with the established
  `rf-lamps-preserve-stable-finiteness-for-arbitrary-actions`. Nothing in
  Cairn forces a nonsofic group to be non-surjunctive: sofic implies
  surjunctive, and there is no converse.
* **Hunting for hidden hypotheses.**
  * Infinite point stabilizers, non-faithful or intransitive actions, and
    nonabelian `A/A_0` were all traced through. The proof uses only that each
    `G_U` is a subgroup of `G`, and that products in `Abar^U` are
    coordinatewise.
  * Finiteness is used exactly where it is available: the memory, the
    supports, `S`, `Abar`, and the union of strata cosets.

## 6. Not verified

* **The proof of Kun--Thom Theorem A.** Nonsoficity of both witnesses rests
  on an unrefereed preprint (v3). Only its statement was checked.
* **Exhaustive novelty.** The web-search budget was exhausted and arXiv search
  endpoints were blocked during the review. Only the three sources above and
  Bowen--Chapman's current version were read. I found no earlier statement of
  a surjunctive nonsofic group or of Theorem 1, but this is a bounded check.
* **No formal verification.** Nothing here is in Lean.

## 7. Minor notes, no action needed for correctness

* The "What this does not settle" remark in the wreath artifact still lists
  surjunctivity of the Kun--Thom doubles, which the finitary artifact settled
  the same day. This is stale text in the author's artifact, not an error in
  any claim.
* The finitary artifact transfers the peeling "verbatim". The only
  non-literal points are the left-coset slicing and representative
  independence. They are correct (Section 2 above), and the graph-folds
  artifact spells them out.
