# solve-weakly-sofic (2026-09-13): stability form of non-weak-soficity

Lane `solve-weakly-sofic`. Target: a group that is not weakly sofic (Glebsky--Rivera Conjecture 4.5,
`non-weakly-sofic-group-exists`), or not linear sofic (`non-linear-sofic-group`).

**Verdict: partial.** No witness. Landed:
- the stability form of both roots for finitely presented simple candidates;
- a new sufficient condition for linear soficity;
- the imports behind them.

Nothing is independently reviewed, and no novelty is claimed.

## 0. State of main when the lane started (tip 2379c90d5)

- **The two roots are equivalent.** `non-weakly-sofic-iff-non-finite-field-linear-sofic-group` (unreviewed).
- **Weak soficity equals finite-field linear soficity for finitely presented simple groups.**
  `fp-simple-weak-soficity-is-finite-field-linear-soficity` (review PASS).
- **Candidate `R^x`.** The gate is `leavitt-el3-rank-models-over-finite-fields-are-trivial`, still open. Its
  Attempts list what a proof must use: the nonsofic compression subgroup, and neither finite nor sofic subgroups.
- **The directive's step 2 was already settled.** `weak-soficity-survives-every-corpus-obstruction` realizes the non-MF
  mechanism (operator-norm microstate failure) inside the sofic group `E`, so it obstructs neither weak nor linear
  soficity. The failure point is metric:
  - the non-MF inequalities are operator-norm estimates;
  - normalized rank ignores operator norm, and a sofic approximation is already a rank model (Arzhantseva--Paunescu
    Proposition 4.5).

  No new node was needed.
- **Kun--Thom transcription is dead in every rank row.** See `non-linear-sofic-group`, Attempts, and
  `kazhdan-rank-rounding-fails-over-every-field`.

## 1. Sources pinned (TeX fetched on MSI, `~/ws-weakly-sofic/{bbg,ap}`)

**Bauer--Blachar--Greenfeld, arXiv:2401.04676v2** (`main_arxiv2.tex`). The theorem counter is shared within sections.
- **Definition 1.1** (l.134) and **Definition 6.1** (l.625): algebra and group rank-stability, flexible in the size
  `n'`. Quoted on `fp-group-algebra-rank-stability-citation`.
- **Theorem 6.3** (`thm:group-alg`, l.650): group rank-stability over `F` iff rank-stability of `F[G]`.
- **Theorem 8.2** (`thm:unstable`, l.1363): the instability criterion. Quoted on
  `algebra-rank-instability-criterion-citation`.
- **Proposition 2.2** (`prop:sofic`, l.210--212), verbatim:
  > Let $\Alg$ be a finitely presented, rank-stable algebra. Suppose that~$\Alg$ is linear sofic. Then $\Alg$ is
  > residually finite-dimensional.
- **l.144--145**, verbatim:
  > \Dref{def:rank-stab} is given in \cite{ElekGrabowski21} in the group-theoretic context, where the authors prove that
  > $\mathbb{Z}^k$ is rank-stable when all matrices considered are unitary or self-adjoint. The question of whether
  > $\mathbb{Z}^k$ is rank-stable without any spectral restrictions on the involved matrices remains open
  > \cite[Remark~2]{ElekGrabowski21}.
- **Example 2.4** (`ex:vac-stab`): `F<x,y,z>/<xyz - 1, xzy>` has no approximate representations, so it is vacuously
  rank-stable.

**Arzhantseva--Paunescu, arXiv:1212.6780v1** (`Lsofic_arxiv.tex`).
- **Definition 4.1** (`def:lsofic`), verbatim:
  > A countable group $G$ is \emph{linear sofic} if there exist an injective morphism
  > $\Theta:G\to\Pi_{k\to\omega} GL_{n_k}(\cz)/d_\omega$.
- **Definition** `universallinearsofic` (l.282): the group ultraproduct is the quotient of `prod GL_(n_k)(F)` by the
  sequences with `lim_omega d_rk(a_k, Id) = 0`. So representatives are invertible.
- **Proposition** `16 algebraic definition` (l.790; numbered 5.7 by the counter, unrechecked): linear soficity iff for
  every finite `E` and `eps` some `phi : E -> GL_n(C)` is `eps`-multiplicative with `rho(1 - phi(g)) > 1/4 - eps`.
- **Question** `q:oneF` (l.1216), verbatim:
  > Let $G$ be a linear sofic group and $F$ a finite field. Does there exist an injective group morphism
  > $\Phi:G\to\Pi_{k\to\omega} GL_{n_k}(F)/d_\omega$?

## 2. The equivalence (landed)

`fp-simple-group-not-linear-sofic-iff-rank-stable`: let `G` be infinite, finitely presented and simple.
- **Fixed field.** `G` is not `F`-linear sofic iff `G` is rank-stable over `F`, iff `F[G]` is rank-stable.
- **Finite fields.** `G` is not linear sofic over finite fields iff it is uniformly rank-stable over finite fields, iff
  `G` is not weakly sofic.

The key point: exact solutions of the relators in `GL_(n')(F)` are identities, by Malcev and simplicity. Stability
therefore says every approximate solution is near the identity, and a nontrivial rank-ultraproduct model of a simple
group is injective. The algebra analogue for residually finite-dimensional algebras is Proposition 2.2 above.

Stability form of the Glebsky--Rivera root, as an OPEN node: `fp-simple-group-uniformly-rank-stable-over-finite-fields-exists`,
wired by `non-finite-field-linear-sofic-via-uniform-rank-stability`.

## 3. Stability tools against the candidates

- **Permanence.**
  - Bauer--Blachar--Greenfeld: finite-dimensional algebras (Theorem 5.1), free products (Proposition 7.1), direct
    products and matrix rings.
  - At the group level these reach free and direct products of finite groups. Those are residually finite, hence never
    infinite simple, and no amalgam or HNN theorem exists (`atlas-rank-stability-literature-fence`).
  - Rank-stability plus linear soficity forces residually finite-dimensional group algebras (Proposition 2.2). A
    stability proof for a non-residually-finite group therefore has to be new, not a permanence argument.
- **Obstructions.**
  - Bachner's free-quotient instability (`free-quotient-obstructs-flexible-uniform-rank-stability`) is silent for
    simple groups.
  - Abels' group is not rank-stable (Elek--Grabowski, as quoted on l.1347), but it is residually finite.
- **Spectral restrictions.** Even `Z^k` is not known to be rank-stable without them. Stability proofs in the rank metric
  are rare.

## 4. The instability criterion as a positive tool (landed)

`fp-simple-group-algebra-amenable-quotient-gives-linear-soficity`: take a nonzero two-sided ideal `I` of `F[G]`,
finitely generated as a left ideal, with `F[G]/I` amenable and without finite-dimensional representations. Then `G` is
`F`-linear sofic.

Attempts on the candidates:
- **The augmentation ideal.** It fails: the quotient is `F`. Any other proper nonzero `I` embeds `G` in the units of
  `F[G]/I`.
- **The Leavitt quotient of `F_2[R^x]`.**
  - The algebra map `F_2[R^x] -> L = L_(F_2)(1,2)` lands in a subalgebra containing all units.
  - Any subalgebra `B` containing `s_0, s_1, t_0, t_1` is not amenable. If `V` were almost invariant, then
    `s_0 V ∩ s_1 V = 0` because `t_1 s_0 = 0` and `t_1 s_1 = 1`, and `dim s_i V = dim V`. So `dim(SV + V) >= 2 dim V`.
  - Whether the unit span contains `s_0` was not checked. So the natural quotient is probably dead, but unproved here.
  - The same question for `V <= R^x` is not checked.
- **Permutation modules.** Følner subsets of Schreier graphs give monomial models, which are Hamming models
  (`monomial-rank-models-are-hamming-models`). They are dead for `R^x` (nonsofic), and for `V` they would already prove
  soficity.
- **One-sided criterion (sketch, not landed).** An `F[G]`-module with Følner subspaces on which some generator has
  displacement bounded below gives a nontrivial rank-ultraproduct homomorphism by truncation, hence linear soficity for
  simple `G`. Theorem 8.2 is the two-sided, model-free version.

## 5. Exact gap

- **Glebsky--Rivera.** One infinite finitely presented simple group (`R^x`, `V`, or another) whose approximate
  representations over all finite fields, with relator defect below `delta`, keep every generator within rank `eps`
  of the identity. The published stability theory has no mechanism for this outside residually finite groups.
- **The opposite direction for `V` over `F_2`.** An amenable, finitely generated quotient ideal of `F_2[V]` as in
  Section 4, or a direct model.
