# STW Problem LXXIV (swarm session, 2026-09-16)

Target: `stw99-problem-lxxiv-infinite-projections-purely-infinite` (STW
Problem LXXIV = Rordam, Acta Math. 2003, Question 7.7).  Hole worked:
`stw74-hypothesis-forces-property-sp` (locked with a 180m TTL for this
session, then unlocked).

## Setup

By the established `stw74-property-sp-is-the-exact-missing-condition`, the
problem is whether every unital simple C\*-algebra whose nonzero projections
are infinite (an "LXXIV algebra") has property (SP).  The graph already has:
all projections in `A tensor K` properly infinite; stationary matrix
thresholds on spectral towers; gapless compressions with a uniform norm floor
over `CP^(m-1)`; Morita normal form; Cu-theoretic reformulations (finite unit
roots, QQ, UAU, weak cancellation); regularity classes that close the hinge
(Z-stable, zero-dimensional Cartan); subhomogeneous threshold models; and an
abstract Cu countermodel.  No claim reduced the matrix level to a fixed
value, and no claim justified the repeated restriction to "separable
counterexamples".

## What was proved (complete proofs in `research/artifacts/stw74-two-level-descent-2026-09-16.md`)

1. **`stw74-lxxiv-hinge-is-two-level-descent`.**  For an LXXIV algebra, (SP)
   is equivalent to: *for every hereditary `H`, if `M_2(H)` has a nonzero
   projection then `H` has one*; equivalently, for one (or every) pair of
   isometries with orthogonal ranges, `Her(t_1at_1*+t_2at_2*)` having a
   projection forces `Her(a)` to have one.  Proof: fullness normal form
   `sum y_i* a^2 y_i=1` gives a least level `m`; the corner isomorphism
   `M_n(A) ~= PAP` from `n=m-1` orthonormal isometries turns
   `M_(m-1)(Her(a))` into `Her(b)`, so `Her(b)` is projectionless while
   `M_2(Her(b)) ~= M_(2m-2)(Her(a)) superset M_m(Her(a))` has a projection.
   Route requires only `stw74-simple-infinite-projections-are-properly-infinite`.
2. **`stw74-two-level-failure-has-full-spectrum-sphere`.**  If `H` is
   projectionless and `M_2(H)` has a projection, there are `x,y` with
   `x*x+y*y=1` and `xx*,xy*,yx*,yy* in H`; every scalar mix
   `z_xi=conj(xi_1)x+conj(xi_2)y` has `sigma(z_xi z_xi*)=sigma(z_xi*z_xi)=[0,1]`,
   and `Her(z_xi* z_xi)` is projectionless.  Key tools: Lemma K
   (`zz* in H`, `z*z` invertible => `z(z*z)^(-1)z* in H` is a projection) and
   Lemma R (`zz* in H` => `zXz* in H`).  Corollary (unit-splitting
   dichotomy): an LXXIV algebra has (SP) iff for every positive contraction
   `e`, `Her(e)` or `Her(1-e)` contains a nonzero projection.
3. **`stw74-counterexamples-have-separable-subcounterexamples`.**  Any
   countable subset of an LXXIV algebra lies in a separable unital
   C\*-subalgebra that is simple, has all nonzero projections infinite, and
   inherits the CPAP.  Construction: countable closure under fullness
   witnesses for `(c-1/4)_+`, infiniteness witnesses for a dense set of
   projections (perturbation by the unitary `u=z|z|^(-1)`,
   `z=qp+(1-q)(1-p)`), and CPAP factorizations.  So counterexamples contain
   separable counterexamples (nuclear if the original is nuclear).
4. **New hole `stw74-separable-two-level-projection-descent`** with the two
   routes `stw74-separable-two-level-descent-forces-sp` (hole + 1 + 3 =>
   `stw74-hypothesis-forces-property-sp`) and
   `stw74-property-sp-gives-separable-two-level-descent` (converse).  Hence
   Problem LXXIV is equivalent to separable level-two descent; the nuclear
   version follows from the same statement for separable CPAP algebras
   (recorded in the artifact and the hole's Attempts, not as a node).

`check.sh` on the ten research paths: exit 0; the three claims above compile
as established (their inputs are established), the two new routes each miss
only the other hole.  No `requires: []` route was written.

## Approaches tried and where each died

* **Direct level-two descent from the column `v=(x,y)^T`.**  One needs `z`
  with `zz* in H` and `z*z` invertible.  Scalar mixes all fail in a
  counterexample (item 2).  Operator mixes `c_1x+c_2y` leave `H` unless the
  `c_i` compress `H` into itself; no source of such `c_i` beyond scalars and
  elements of `H` itself was found.
* **Scalar mixing as a general principle.**  Dead even algebraically:
  `x=e_11`, `y=e_12` in `M_2(C)` satisfy the column data, `x*y` is nilpotent
  of norm 1 and every scalar mix has rank one.
* **Gram-matrix reformulation.**  Asking for a left-invertible compression of
  `[[x*x,x*y],[y*x,y*y]]` inside `H` restates the hole; circular.
* **Unit splitting.**  Excluding `e` with `Her(e)`, `Her(1-e)` both
  projectionless would need a way to create projections from `e(1-e)` (with
  spectrum `[0,1/4]`); no comparison principle is available without Z-type
  regularity, which counterexamples lack.
* **Relative (SP) via inclusions / conditional expectations.**  Already in
  Gow--Hernandez Palomares (arXiv:2608.30057v1).  Their TeX source defines
  `A subset B` to be an SP-inclusion when `closure(aBa)` has a nonzero
  projection for every nonzero `a in A_+`.  Their Theorem 4.4 (Section 4)
  says: if there is a faithful conditional expectation `E:B->A` with the
  pinching property, then `A subset B` is an SP-inclusion iff `B` has
  (SP).  This relates (SP) of the inclusion to (SP) of the larger algebra.
  It does not create projections in an LXXIV algebra, so I dropped this
  approach as not new.
* **Tensor-product route** (use `A tensor O_infinity` or `A tensor O_2`,
  where projections are abundant, and pull back): stalled because a projection
  of `Her(a) tensor O_infinity` need not come from `Her(a)`, and descending
  from `O_infinity`-coefficients is the same level-`m` problem in disguise.
  An `O_2`-corner formulation would need Cuntz's K-theory computation; not
  pursued (unverified here, not used).
* **Type I / non-simple models.**  Subhomogeneous algebras have no properly
  infinite projections, so they cannot host the hypothesis; the graph's
  `D_(1,2)` (`stw74-every-matrix-descent-threshold-occurs-subhomogeneously`)
  shows level-two failure does occur intrinsically, so any proof must use the
  ambient simplicity plus infiniteness.
* **Cu-semigroup remark.**  The hypothesis of level-two descent for
  `H=Her(a)` forces `[1]<=2[a]` in `Cu(A)` (proper infiniteness plus
  Lemma 4 in `M_2(A)`), while the conclusion is a projection in
  `Her(a)`; the graph's `stw74-cu-axioms-do-not-extract-projective-roots`
  already records that Cu-axioms alone do not extract projective roots, so
  no purely Cu-theoretic proof of level-two descent was attempted.
* **Selfless algebras.**  By the graph's `gould-selfless-dichotomy-and-purity`
  (Gould, arXiv:2606.09654v2), a selfless LXXIV algebra cannot have stable
  rank one (its unit is infinite), so it is purely infinite; another class
  closing the hinge, not a solution.

## Weakest steps (for the referee)

* Theorem B(c): the approximate-unit estimate `w*e w>=1/(2n)` and the use of
  Lemma R for `z(ww*)z* in H`.
* Theorem C: CPAP inheritance (restricting `phi`, landing `psi` in `C` by
  adding `psi(e_rs)`), and the perturbation constants `1/10, 1/5, 2/5`.
* Theorem B(a): transferring proper infiniteness of `p in M_2(H)` from
  `A tensor K` into `M_2(A)` (witnesses lie in `p(A tensor K)p=pM_2(A)p`).

## Literature gate (checked 2026-09-16)

* Schafhauser--Tikuisis--White, *Nuclear C\*-algebras: 99 problems*,
  arXiv:2506.10902v2: Problem LXXIV listed as open (TeX source read in the
  earlier part of this session).
* Gow--Hernandez Palomares, *Property (SP) and Inclusions of C\*-algebras*,
  arXiv:2608.30057v1 (submitted 2026-08-30): SP-inclusions; Theorem 4.4
  (faithful pinching conditional expectation `E:B->A`: `A subset B` is an
  SP-inclusion iff `B` has (SP)), verified from the TeX source; does not
  address LXXIV.
* A. Sutradhar, *The pure infiniteness transfer problem*, arXiv:2608.30906v2
  (v1 2026-08-31, v2 2026-09-01): Problem 8.4 of arXiv:0806.4156 under real
  rank zero / closure hypotheses; not LXXIV.
* M. Gould, *The Selfless Dichotomy*, arXiv:2606.09654v2 (v1 2026-06-08):
  selfless algebras have stable rank one or are purely infinite (already in
  the graph).
* F. Flores, J. Gondek, arXiv:2608.30127v1 (2026-08-31), D. Pask,
  arXiv:2607.27691v1 (2026-07-30), Geffen--Hua--Kranz arXiv:2608.13000v1
  (2026-08-13): pure infiniteness for specific groupoid/graph/group classes;
  not LXXIV.
* arXiv:2508.06844v3 and arXiv:2405.10191v2: checked earlier in the session,
  not relevant to LXXIV.
* arXiv API queries (2026-09-16, HTTPS export.arxiv.org):
  `abs:"purely infinite" AND "projections"`, `abs:"property (SP)"`,
  `abs:"projectionless" AND "infinite"`, `abs:"hereditary" AND
  "purely infinite"`, and the newest-first union of `"property (SP)"` and
  `"purely infinite"`: nothing newer than 2026-08-31 and no solution of
  LXXIV found.
* Kirchberg--Rordam (traceless ultrapower characterizations) and the
  Choi--Effros/Kirchberg equivalence of nuclearity with CPAP are mentioned
  only as background and are **unverified** here (no theorem numbers used);
  Theorem C is stated with the CPAP so no import is needed.

## Files

* `research/artifacts/stw74-two-level-descent-2026-09-16.md`
* `research/stw74-lxxiv-hinge-is-two-level-descent.md`,
  `research/stw74-two-level-descent-equivalence-proof.md`
* `research/stw74-two-level-failure-has-full-spectrum-sphere.md`,
  `research/stw74-full-spectrum-sphere-proof.md`
* `research/stw74-counterexamples-have-separable-subcounterexamples.md`,
  `research/stw74-separable-subcounterexample-proof.md`
* `research/stw74-separable-two-level-projection-descent.md` (hole),
  `research/stw74-separable-two-level-descent-forces-sp.md`,
  `research/stw74-property-sp-gives-separable-two-level-descent.md`

## Referee (2026-09-16)

**Checked.**

* Read all ten research files, the artifact and this note, plus the graph
  inputs they use: `stw74-simple-infinite-projections-are-properly-infinite`,
  `stw74-all-stabilized-projections-are-properly-infinite` and
  `stw74-property-sp-is-the-exact-missing-condition` (all ESTABLISHED per
  `cairn why`), `stw74-hypothesis-forces-property-sp`, `stw74-via-property-sp`,
  `stw74-counterexamples-have-stationary-matrix-thresholds`,
  `stw74-every-matrix-descent-threshold-occurs-subhomogeneously`,
  `stw74-projectionless-corner-forces-gapless-compressions` and
  `stw74-z-stability-and-finite-nuclear-dimension-close-hinge`.
  `git status` shows no unlisted solver files.
* Re-derived every step of the artifact by hand.
  * Lemma 1: from the ideal `J_0`, `1=C(a tensor 1)Dcol`, then
    `C*C<=||C||^2` and the rescaling by `g_1^(-1/2)`.
  * Lemma 2: the products `t_i*t_j`, using `q s_2=s_2`.
  * Lemma 3: multiplicativity, injectivity via `t_k*Phi(C)t_l`, surjectivity
    onto `PAP`, and `Phi(M_n(Her(a)))=Her(b)`, because `bPAPb=bAb` and `Phi`
    is isometric.
  * Lemma 4: `w*w=sum y_i*qy_i=1`.
  * Lemma K: `q=hX^2h` with `hX=Xh=q`.
  * Lemma R: `t n^(-2)(1/n+t)^(-2)<=1/(4n)` by AM-GM.
  * Theorem A, (3')=>(1): `w_1*bw_1=a`; `Her(b)~=M_(m-1)(Her(a))` is
    projectionless; and `M_2(Her(b))~=M_(2m-2)(Her(a))` contains a projection
    because `2m-2>=m`.
  * Theorem B(a): a witness `s` with `s*s=p` and `ss*=e<=p` satisfies
    `s=esp`, so it lies in `p(A tensor K)p=pM_2(A)p`; also `M_2(A)` is simple
    and `vv*=p(ue_11u*)p` lies in `M_2(H)`.
  * Theorem B(b): Lemma K gives non-invertibility of `e_xi` and of
    `e_eta=1-e_xi`; a spectral gap gives a nonzero spectral projection of
    `b_xi` inside `H`.
  * Theorem B(c): `rw=w`; the approximate-unit estimate
    `||(1-g_n)e||<=1/(4n)`, extended to the closure; `w*g_nw>=1/2` gives
    `w*ew>=1/(2n)`; then Lemma R for `z ww* z*`.
  * Corollary B'.
  * Theorem C, simplicity constants:
    `||a-d*d||<(1/40)(2+1/40)<1/15`, `||a-c'||<2/15`, `2/15+1/10=7/30<1/4`.
  * Theorem C, infiniteness: `sigma(h)` lies within `1/10` of `{0,1}`;
    `z-1=(2q-1)(p-q)`; `z*z` commutes with `p`; `upu*=zpz^(-1)=q`.
  * Theorem C, CPAP: `psi` lands in `C`, positivity is permanent under the
    inclusion, and the `epsilon/3` argument.
  * Both Section 5 routes.
* Found no mathematical error, hidden hypothesis or quantifier mismatch.
  Unitality and simplicity are used where stated. Separability is only
  produced (Theorem C), never assumed.
* No route has `requires: []`. The three new claims are established through
  routes whose inputs are already established. The two cycle routes each
  miss only the other hole, so the new hole
  `stw74-separable-two-level-projection-descent` is honestly OPEN and has an
  `## Attempts` section.
* Duplicates: `cairn search --similar` on the four new claims found no
  existing claim with the same content. The `distinct_from` entries are
  accurate.
* Id lengths: longest claim id is 55, longest route id is 51.
* Literature spot-checks, fetched 2026-09-16:
  * arXiv:2608.30057 (Gow--Hernandez Palomares, submitted 2026-08-30).
    Definition 2.4 (SP-inclusion) and Theorem 4.4 (faithful conditional
    expectation `E:B->A` with the pinching property: `A subset B` is an
    SP-inclusion iff `B` has (SP)) match the note and the hole's Attempts.
  * arXiv:2506.10902 (STW, v2 2026-05-08) exists as cited.
  * An arXiv API newest-first query for `abs:"purely infinite" AND
    abs:"projection"` returns nothing after 2026-08-31 and no resolution of
    LXXIV.

**Changed.**

* Hole Attempts item 7: replaced "traceless and not Z-stable by the existing
  regularity claims". Tracelessness now has its one-line reason, and non-Z-
  stability cites `stw74-z-stability-and-finite-nuclear-dimension-close-hinge`.
* Artifact, remark after Theorem C: added a sentence saying that the
  countable-closure construction and Lemmas 1--4, K and R are standard
  elementary techniques, proved in full, and that no literature novelty is
  claimed for them.

**Verdict.** Landed with minor fixes. The work is a sound reduction, with
three established structural claims and one new open hole that is
equivalent to `stw74-hypothesis-forces-property-sp`. Problem LXXIV remains
open.
