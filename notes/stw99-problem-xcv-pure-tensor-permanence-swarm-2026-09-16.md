# STW Problem XCV (minimal tensor products of pure algebras) -- swarm attack 2026-09-16

Agent: `swarm-stw99-problem-xcv-pure-tensor-`.  Lock taken on
`stw99-problem-xcv-pure-tensor-permanence`; released at the end.  Nothing was committed.

## Setup

Root claim: if `A` and `B` are pure C\*-algebras, then `A (x)_min B` is pure (Schafhauser--Tikuisis--White,
arXiv:2506.10902v2, Problem XCV, general part).  Pure means that `Cu` is almost unperforated and almost divisible.
Known cases before this session (from the repo artifacts `fz-stw-xcv-review-2026-09-13` and
`stw95-pure-tensor-frontier-2026-08-30`, and Seth--Vilalta arXiv:2602.14809v2):

- `B = C(X)` with `X` compact metric, when `A` is simple (SV Cor. 5.9) or no quotient of `A` has a nonzero compact
  properly infinite Cuntz class (SV Thm 5.11, via Prop. 5.10 and Thm 5.6 for finite-dimensional `X`).  The second
  case includes residually stably finite `A`;
- `B` unital separable ASH, with `A` simple pure (SV Thm 6.7) or pure and residually stably finite (SV Rem. 6.8);
- products where one of the factors absorbs `Z`, and products of finite nuclear dimension that have the Global
  Glimm Property (APTV arXiv:2406.11052v3, Thm 6.5: Global Glimm Property plus finite nuclear dimension gives
  purity).

This lane attacks the case "`A` pure, `B` separable of finite nuclear dimension".  `B` is not required to be
pure, for example `B = C([0,1])`.  The pure factors of finite nuclear dimension form a case of XCV itself.
Proofs are in `research/artifacts/nucdim-factor-comparison-divisibility-2026-09-16.md`.

## Status gate (2026-09-16)

- STW arXiv:2506.10902v2 lists XCV as open.
- SV arXiv:2602.14809v2 (Feb 2026), TeX source read.  The introduction recalls the question whether `B (x) A` is
  pure whenever `A` is pure.  The paper proves the `C(X)` and ASH cases above and does not treat general `B`.
- APTV arXiv:2406.11052v3, TeX source read for Theorem 5.7 (`(m,n)`-pure implies pure), Lemmas 6.2, 6.3 and
  Theorem 6.5.
- arXiv search, 2026-09-16, abstracts fetched through export.arxiv.org:
  - Fu, arXiv:2605.21655 (2026-05-20), *Divisibility and Real Rank Zero*: simple exact, tracial divisibility
    equivalences.  Not about tensor products of non-simple pure algebras.
  - Lee, arXiv:2603.07491 (2026-03-08), *On permanence of regularity properties II*: permanence of tracial
    `m`-comparison and `m`-almost divisibility along tracially sequentially-split maps, simple unital.  Does not
    address XCV.
  - Ng--Thiel--Vilalta, arXiv:2507.16261 (2025-07-22), *The Global Glimm Property for C\*-algebras of topological
    dimension zero*: nowhere scattered plus topological dimension zero gives the Global Glimm Property.  See the
    remark below; only the abstract was read.
  - arXiv:2607.27691 (2026-07-30), *Nuclear dimension, pure infiniteness and real rank for higher rank graph
    C\*-algebras*: title only, not relevant.
- No source found that settles XCV or the finite-nuclear-dimension case.

## What was proved (graph nodes, all with the artifact attached)

Constants: `M = 2(m+1)`, `M_1 = 2M^3 = 16(m+1)^3`, `L = 32(m+1)^3`.

1. **Theorem A** (`nucdim-factor-transfers-m-comparison`, direct route).  If `Cu(A)` is almost unperforated and
   `B` is separable with `dim_nuc B <= m`, then `Cu(A (x) B)` has `m`-comparison.
   - Proof: WZ almost order zero approximations (WZ Adv. Math. 224 (2010), Prop. 3.2, audited), passed to the
     sequence algebra by Lemma P.
   - Each colour is transported by an order zero map `id (x) phi^(i)` (WZ Munster J. Math. 2 (2009),
     Thm 2.3 and Cors 3.2, 3.3, 3.5).
   - Almost unperforation in `A (x) F_i` is used colour by colour, followed by diagonal reflection back into
     `A (x) B`.
2. **Theorem B and Corollary B'** (`nucdim-factor-transfers-bounded-divisibility`, direct route).  If `Cu(A)` is
   almost divisible, then for every `N >= 1` and `x' << x` in `Cu(A (x) B)` there is `y` with
   `x' << N y << 2(m+1) x`.  This is bounded divisibility with `M = 2(m+1)`.  Each colour is divided separately
   and the pieces are summed, which costs the factor `m+1`.
3. **Imported dimension reduction** (`sv26-bounded-divisibility-dimension-reduction`, citation route).  Assume
   `m`-comparison and bounded divisibility with constant `M`.  Then:
   - SV Lemma 5.4 holds; its proof was re-checked;
   - a two-piece splitting implies purity (SV Thm 5.6 (ii)=>(iii)).  The Claim induction and the
     `n`-almost-divisibility chain were re-derived.  The only load-bearing import is APTV Thm 5.7;
   - purity implies the Global Glimm Property (Thiel--Vilalta arXiv:2204.13059, Thm 3.6).
4. **Imported converse** (`sv26-global-glimm-gives-two-color-splitting`, citation route).  Under the same
   hypotheses, the Global Glimm Property gives a splitting with `L = 2(m+1)(M_1+2)`.  SV only sketch this as
   modifications of APTV Lemma 6.2, and the route body says so.
5. **Theorem D** (`pure-tensor-nucdim-no-pi-quotient-is-pure`, route requiring 1, 2, 3).  Let `A` be pure,
   `B` separable with `dim_nuc B <= m`, and suppose no quotient `C/J` of `C = A (x) B` has a nonzero compact
   properly infinite element in `Cu(C/J)`.  Then `C` is pure.
   - This adapts SV Prop. 5.10.  Evaluation at points is replaced by the quotient of `C (x) K` by the ideal
     generated by the second piece.
   - New details that were checked:
     - orthogonality of the two pieces through a row matrix;
     - the description `I = J (x) K` of closed ideals of `C (x) K`;
     - the tracial step through Robert's Lemma 1, including traces taking the value `infinity` on the element.
6. **Corollary E'** (`pure-tensor-nucdim-factor-pure-iff-global-glimm`, route requiring 1--4).  For `A` pure and
   `B` separable of finite nuclear dimension, `A (x) B` is pure iff it has the Global Glimm Property iff it
   admits a two-piece splitting.
7. Open holes created:
   - `pure-tensor-nucdim-factor-is-pure` (claim E).  Route `pure-tensor-nucdim-factor-purity-via-glimm` reduces
     it to claim F;
   - `pure-tensor-nucdim-factor-has-global-glimm` (claim F).

No route to the root was written.  Claims D and E are positive classes, not decompositions of XCV.

## Approaches and where each dies

- **Global Glimm colour by colour.**  Square-zero elements exist in each `A (x) F_i`, but an almost full
  square-zero element of `A (x) B` would have to be assembled across colours.  The images of different colours
  overlap and no bound on the overlap was found.  The same overlap is why Theorem B loses the factor `m+1`.  With
  that factor the splitting of SV Thm 5.6 (ii) does not follow.
- **Thiel--Vilalta Glimm criteria** (arXiv:2204.13059).  They need ideal-lattice or property (V) type
  hypotheses.  The ideal lattice of `A (x)_min B` is not controlled without exactness assumptions.
- **APTV Theorem 6.5.**  It needs finite nuclear dimension of `A (x) B` itself, which fails for general pure `A`.
- **Reducing the Theorem D hypothesis to `A` and `B`.**  Quotients of `A (x)_min B` need not be tensor products of
  quotients unless exactness conditions hold.  So "no quotient of `A` has a compact properly infinite class" was
  not transferred to `A (x) B`.  SV avoid this for `B = C(X)` by evaluating at points.  For general `B` there are
  no points to evaluate at, and the ideal generated by the second piece is used instead.
- **Brute-force lemma.**  Applying the Cuntz lemma for order zero maps to `id (x) phi^(i) psi^(i)` without the
  functional-calculus cut is false in general.  See the remark after Corollary B' in the artifact.

## Side observations (notes only, not in the graph)

- **`stw99-lxxv-fnd-implies-pure` overstates its result.**  Its body says every separable C\*-algebra of finite
  nuclear dimension is `(m,m')`-pure and hence pure.  `C([0,1])` has nuclear dimension 1 but is not almost
  divisible: in `Cu(C([0,1]))`, `2y <= [1]` forces `y = 0`.  The APTV statement (arXiv:2406.11052v3, Thm 6.5)
  needs the Global Glimm Property.  APTV note that the non-simple Toms--Winter question contains the Global Glimm
  Problem for finite nuclear dimension, so nowhere scatteredness alone is not known to suffice.  The committed
  node was not edited.
- **Nowhere scatteredness.**  Bounded divisibility (Corollary B') passes to quotients, because `Cu(C/J)` is a
  quotient of `Cu(C)` and `x' << x` pairs lift through `(f-eps)_+`.  It then excludes elementary ideals of
  quotients.
  - In `Cu(K) = N-bar`, the equation `x' << N y <= 2(m+1)x` with `x = x' = 1` and `N > 2(m+1)` has no solution.
  - With Thiel--Vilalta's characterization of nowhere scattered algebras (*Nowhere scattered C\*-algebras*,
    arXiv:2112.09877, J. Noncommut. Geom. 18 (2024); theorem number not re-verified), `A (x) B` is nowhere
    scattered.  This matches the SV remark after Theorem 5.6.
  - So a positive answer to the Global Glimm Problem (`stw99-problem-lxxiii-global-glimm`) would give claim E.
- **Topological dimension zero (unverified).**  Suppose `A (x) B` has topological dimension zero.  The Ng--Thiel--Vilalta
  abstract (arXiv:2507.16261) together with the previous remark would give the Global Glimm Property, and hence
  purity by Corollary E'.  Only the abstract was read, so this was not put into the graph.
- **Residual stable finiteness.**  If every quotient of `A (x) B` is stably finite, then no quotient has a nonzero
  compact properly infinite class, so Theorem D applies and `A (x) B` is pure.  SV state this implication in the
  paragraph before their Prop. 5.10.  Behind it is the fact that compact Cuntz classes of stably finite algebras
  come from projections (Brown--Ciuperca; not re-checked here).  SV also note that, for algebras of finite nuclear
  dimension, the condition is equivalent to having no simple purely infinite quotients (Robert--Tikuisis, Lemma 3.3).
  `A (x) B` need not have finite nuclear dimension, so that equivalence does not apply here.

## What remains open

- `pure-tensor-nucdim-factor-has-global-glimm` (equivalently `pure-tensor-nucdim-factor-is-pure`).  The first
  case of interest is a pure `A` that is not `Z`-stable and is not a direct sum of pieces covered by Theorem D, and
  that has a quotient with a nonzero compact properly infinite Cuntz class, with `B = C([0,1]^2)` or a
  non-commutative `B`.  Two simpler cases give nothing new:
  - direct sums split into summands;
  - for `Z`-stable `A` the product is `Z`-stable, hence pure by standard results.
- The root XCV for pure factors of infinite nuclear dimension is untouched by this lane.

## Referee attack points

1. APTV arXiv:2406.11052v3 Theorem 5.7 (`(m,n)`-pure implies pure).  This is the only external step of SV 5.6
   (ii)=>(iii) not re-derived.
2. SV Lemma 5.4: the proof was re-checked, but it is a preprint.
3. Lemma P and the audit of WZ Prop. 3.2 (sequence-algebra lifting of almost order zero approximations).
4. For Corollary E' only: the sketched SV Theorem 5.6 (i)=>(ii).

## Literature (dated)

- Schafhauser--Tikuisis--White, arXiv:2506.10902v2 (open-problem list; v1 June 2025, v2 read).
- Seth--Vilalta, arXiv:2602.14809v2 (v1 Feb 2026, v2 read): Lemma 5.4, Theorem 5.6, Remark 5.7, Theorem 5.8,
  Cor. 5.9, Prop. 5.10, Theorem 5.11, Theorem 6.7, Remark 6.8 (numbering counted from the TeX source).
- Antoine--Perera--Thiel--Vilalta, arXiv:2406.11052v3 (Dec 2024): Theorem 5.7, Lemmas 6.2 and 6.3, Theorem 6.5.
- Thiel--Vilalta, *The Global Glimm Property*, arXiv:2204.13059, Trans. Amer. Math. Soc. 376 (2023): Theorem 3.6
  (Global Glimm Property iff `(2,omega)`-divisible).
- Thiel--Vilalta, *Nowhere scattered C\*-algebras*, arXiv:2112.09877 (2021-12-18), J. Noncommut. Geom. 18 (2024).
- Robert, arXiv:1002.2180, Munster J. Math. 4 (2011): Lemma 1 and Theorem 1.
- Winter--Zacharias, arXiv:0903.4914, Adv. Math. 224 (2010): Prop. 3.2.
- Winter--Zacharias, arXiv:0903.3290, Munster J. Math. 2 (2009): Thm 2.3, Cors 3.2, 3.3, 3.5.
- Robert--Tikuisis, arXiv:1308.2941 (Trans. AMS 369, 2017).
- Kirchberg--Rordam, Amer. J. Math. 122 (2000) and Adv. Math. 167 (2002), Lemma 2.2.
- Coward--Elliott--Ivanescu, J. reine angew. Math. 623 (2008).
- Phillips, *Large subalgebras*, arXiv:1408.5546 (2014): Lemma 1.5 and Cor. 1.6, the Cuntz inequalities quoted in
  SV Lemma 2.3(iii),(iv).
- 2024--2026 arXiv hits listed in the status gate: 2605.21655, 2603.07491, 2507.16261 (abstracts read) and
  2607.27691 (title only).
