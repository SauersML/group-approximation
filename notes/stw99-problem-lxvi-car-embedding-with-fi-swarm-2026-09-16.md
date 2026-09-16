# STW Problem LXVI (CAR embedding with a finite projection) -- swarm notes, 2026-09-16

Agent: `swarm-stw99-problem-lxvi-car-embeddi`.
Target root: `stw99-problem-lxvi-car-embedding-with-finite-projection`.
Hole locked and worked: `stw99-lxvi-mixed-algebra-with-dyadic-finite-projection`
(open construction claim: simple `B` with an infinite projection and a finite
projection `p` carrying a coherent dyadic chain in `V(B)`).

## 1. Setup

Exact wording (read from the TeX source of arXiv:2506.10902v2, Schafhauser--
Tikuisis--White, "99 problems", Problem LXVI, label `M2InftyInfinite`):
"Does there exist a unital embedding of $M_{2^\infty}$ into a simple infinite
C$^*$-algebra $B$ such that the image contains finite projections?"  The
follow-up text says Rordam arranged `1_B` as a sum of two equivalent finite
projections, that modifications give for each `n` a unital `M_n -> B` whose
only infinite image projection is `1_B`, "but it seems challenging to combine
these", and proposes a Jiang--Su analogue expected to have the same answer.

Graph facts used (all already in the graph): the maximal-finite-corner
criterion (a finite `p` with coherent dyadic chain in a simple algebra with an
infinite projection gives an LXVI seed), no witness is Z-stable, finite seeds
have no quasitrace, injective limits cannot create instability, ultraproducts
and reduced products of finite stages are not simple, and the Rordam-type
no-gos (identical pairing destroys Hall; uniformly doubled steps and one
cofinal rank-amplifying branch force proper infiniteness; weighted Hall
criterion for Hopf-power blocks; triangular Hopf bundles give coherent
dyadic Euler roots K-theoretically).

## 2. Literature gate (checked 2026-09-16)

* arXiv:2506.10902v2 (Schafhauser--Tikuisis--White, 99 problems, revised
  2026-05-08): LXVI listed as open.  Fetched (e-print TeX source).
* arXiv API searches (export.arxiv.org, 2026-09-16) for combinations of
  "infinite projection", "finite projection", CAR / UHF with infinite,
  "stably finite" with simple, "properly infinite" with simple, "finite and
  infinite", "not purely infinite", Schafhauser--Tikuisis, Jiang-Su with
  "unital embedding": no paper claiming a resolution of LXVI found.
* Abstracts fetched and judged not to resolve LXVI: arXiv:2608.30906
  (Sutradhar, 2026-08-31), arXiv:2602.20591 (Ng--Wang, 2026-02-24),
  arXiv:2606.09654 (Gould, selfless dichotomy, 2026-06-08, v2 2026-07-22),
  arXiv:2508.13834 (Marcoux--Sarkowicz--Zhang, 2025-08-19).
* arXiv:2405.10191 (Suzuki) seen only in a listing; relevance unverified.
* Rordam, "A simple C*-algebra with a finite and an infinite projection",
  Acta Math. 191 (2003), arXiv:math/0204339: used only as recorded in existing
  graph nodes (Prop 3.2, Lemma 4.3, Prop 4.5(i) numbering as recorded there;
  not re-verified this session).
* The general web-search budget was exhausted this session, so the gate
  relied on the arXiv API plus direct abstract fetches; journal-only
  publications not on arXiv may have been missed.

Conclusion: LXVI appears open as of 2026-09-16.  This is not a status update.

## 3. What was proven (new graph nodes, check.sh exit 0)

1. `rordam-line-bundle-sums-are-k-theoretically-rigid`, direct route
   `rordam-line-bundle-sums-are-k-theoretically-rigid-proof` (`requires: []`).
   Over `Z_F=(S^2)^F` (F finite or countable), with `b_i=[zeta_i]-1`,
   `K^0(Z_F)=Z[b_i]/(b_i^2)` has basis `b_S` and
   `[directSum_J zeta_J^(m(J))] = sum_S N_m(S) b_S`,
   `N_m(S)=sum_(J contains S) m(J)`.  Boolean Mobius inversion recovers `m`.
   Hence finite Rordam sums are equivalent iff stably equivalent iff equal
   multisets, and `d` divides the class iff `d` divides every multiplicity.
   Inputs: `K^0(S^2)`, the fundamental product theorem, Swan, continuity
   through the dense union of finite-stage pullbacks (injective because the
   coordinate projections have sections).
2. `blockwise-rordam-halving-forces-proper-infiniteness`, route
   `blockwise-rordam-halving-forces-proper-infiniteness-proof`
   (`requires: [rordam-line-bundle-sums-are-k-theoretically-rigid]`).
   For `Q=sum_j s_j p_(K_j) s_j^*` in `M(C(Z) tensor K)`: if a partition into
   finite blocks has every block class in `2^n K_0` (H1), and infinitely many
   distinct occurring sets satisfy `|K \ C|<=s<2^n` for one finite `C` (H2),
   then `1` is equivalent to a subprojection of `Q`, so `Q` is full and
   properly infinite and `g <~ Q`.  Transported singleton seeds give (H2) with
   `s=1`, so any blockwise `K_0`-halving of a step output containing them is
   fatal.  This generalizes `dyadic-rordam-identical-pairing-destroys-sdr`
   (which assumed identical branch copies and concluded only failure of Hall)
   and removes the "duplicated branch list" hypothesis from
   `uniformly-doubled-rordam-steps-force-proper-infiniteness`.

Sanity script: `experiments/stw99-lxvi-line-bundle-rigidity-2026-09-16/mobius_check.py`
(400 random multisets over 5 coordinates: honest multiplication in
`Z[b_i]/(b_i^2)`, coefficient formula, Mobius recovery, gcd of coefficients
equals gcd of multiplicities; plus the threshold `2^n N > |C|+sN`).  It is a
consistency check only; the proofs do not depend on it.

Weakest steps (for a referee): in node 2, the strict convergence of
`V=sum_k w_k` and the use of obstruction theory for a nowhere-zero section
when real base dimension is at most `2r-2`; in node 1, only textbook inputs.

## 4. Approaches tried and exactly where each dies

**(a) Blockwise dyadic halving inside Rordam sums.**  Dies by the two nodes
above: K-theory forces literal multiplicity `2^n`, and repeated summands over
a bounded relative support exceed the base dimension, giving `1 <~ Q`.

**(b) Shifted (non-blockwise) halving in the multiplier algebra.**  Not
covered by anything proved here; this is the remaining escape hatch in the
line-bundle calculus.  K-theory cannot help there (the multiplier algebra of
a stable algebra has trivial `K_0`; standard, not used in any proof).  What
can be said (sketches, not graph nodes):
* If `g` is not `<~ P`, every subprojection of `P` whose range is pulled back
  from coordinates `F` has rank at most `|F|` (general position), so every
  embedding problem that a shifted halving must solve lies in the unstable
  range where Euler classes and higher obstructions decide, never `K_0`.
* Line absorption for `J subset J'`: `L_J` embeds in `2^m L_(J')` iff the
  Hom bundle `2^m L_(J' \ J)` has a nowhere-zero section.  It has one when
  `2^m > |J' \ J|`; when `2^m <= |J' \ J|` its top Chern class
  `(sum_(i in J'\J) x_i)^(2^m)` is a positive multiple of a sum of basis
  monomials, hence nonzero, so no section.  Rordam's certificate for the
  single block `2^m L_(J')` needs `2^m <= |J'|`.  So individual absorptions
  compatible with the certificate exist exactly when
  `|J' \ J| < 2^m <= |J'|`; combining infinitely many of them coherently is
  where the analysis stops (not attempted rigorously).
* Euler class of a sum of line bundles `L_(v_c)` with linear forms `v_c` in
  the `x_i`: `e = sum_(|S|=r) perm(V[S]) x_S` (permanent of the coefficient
  submatrix), which reproduces the (weighted) Hall criteria when the `v_c`
  are 0/1 vectors.  Disjoint-support absorption (`L_(J_0)` into
  `directSum_i L_(J_i)^(m_i)` with the `J_i` disjoint from `J_0`) has top class
  `prod_i (x_(J_i)-x_(J_0))^(m_i)`, which I believe is nonzero when every
  `m_i <= |J_i|`, obstructing such absorptions in the top-rank case; this was
  only checked by hand in small cases and is not claimed.

**(c) Designs whose halved summands have unbounded relative support.**  (H2)
fails if, for every finite `C` and `s<2^n`, only finitely many occurring sets
satisfy `|K \ C| <= s`.  Node 2 says nothing there.  The triangular Hopf
feasibility node (`2^(K-m) L_K` with large `L_K` supports) lives in this
regime at the level of finite stages, but its natural diagonal implementation
is already killed by `one-cofinal-rank-amplifying-branch-forces-proper-infiniteness`
once the simplicity engine supplies a bounded-support family.  Where a
simplicity engine that never feeds bounded-support summands into the halved
class could come from is exactly the open design question; I found no
candidate.

**(d) CAR version versus Jiang--Su version (sketch, off-axis, not a node).**
A positive answer for CAR gives one for the Z-analogue in the STW follow-up:
if `p` is a finite projection in the CAR image, pick a soft `a` in a unital
copy of Z inside CAR with `d_tau(a)=tau(p)`.  Inside CAR, `a <~ p` and
`p <~ a directSum r` for every small nonzero projection `r`.  If `a` were
Cuntz-infinite (`a directSum b <~ a`, `b` nonzero), fullness in CAR gives
`r <~ b^(directSum k)`, then `p directSum b <~ p`, and a hereditary-subalgebra
and polar-decomposition argument makes `p` infinite, a contradiction.  I did
not write the Cuntz-comparison details to referee standard.

**(e) Stability indices (sketch).**  With `mu(q)` the least `k` with
`k[q]` infinite, the dyadic halves `p_n` of an LXVI seed satisfy
`mu(p_(n+1))` in `{2mu(p_n)-1, 2mu(p_n)}`, so `(mu(p_n)-1)/2^n` increases and
`mu(p_n)/2^n` decreases to a common threshold; finiteness of a CAR-image
projection then depends only on its trace and is a down-set.  This refines
`stw99-lxvi-car-corner-forces-unbounded-stability-indices` but adds no
obstruction.

**(f) Other architectures (where each stops).**
* Stagewise reformulation (stages `C_n`, maps into `M_2(C_(n+1))`, finite
  `M_(2^n)(C_n)`, simple injective limit) is a restatement, not progress.
* Zero-dimensional, ample-groupoid, and real-rank-zero constructions: no
  non-tracial finiteness certificate is known; Rordam's certificate is the
  Euler class of bundles over `(S^2)^N`.
* Finite-dimensional base with multiplier projections of infinite rank:
  such projections are trivial after stabilization in the usual
  Dixmier--Douady/Kuiper sense, so there is no room for a certificate
  (heuristic, not proved here).
* Tensor products with an infinite-unit factor, non-tracial free products
  (purely infinite by Dykema--Rordam, as recalled, not re-fetched), and
  separated-graph algebras (realization of the truncated dyadic monoid is
  unresolved; that monoid is not a refinement monoid, e.g. `1/2+1/2=1+1`
  admits no refinement) give no candidate.

## 5. What remains open

`stw99-lxvi-mixed-algebra-with-dyadic-finite-projection` stays open.  After
this session, any Rordam line-bundle design must implement the dyadic
halvings of the candidate finite projection by equivalences in the multiplier
algebra that do not respect any partition into finite Rordam blocks
satisfying (H2), or keep the halved summands free of infinite
bounded-relative-support families.  No construction of either kind is known
to me, and I found no obstruction to shifted equivalences.

## Referee (2026-09-16)

Checked:

* **`rordam-line-bundle-sums-are-k-theoretically-rigid-proof` (direct).**
  I checked every step. The inputs are textbook: `K(S^2)=Z[H]/(H-1)^2`, the
  product theorem `K(X) tensor K(S^2) = K(X x S^2)` for compact Hausdorff
  `X`, and Swan. With them, `K^0((S^2)^n)=Z[b_i]/(b_i^2)` is free on the
  `b_S`. The expansion `[zeta_J]=sum_(S subset J) b_S` is correct. The
  Boolean Mobius inversion `sum_(S contains T)(-1)^|S\T| N_m(S)=m(T)` is
  correct, and since it has integer coefficients, divisibility of all
  `N_m(S)` passes to all `m(T)`. Uniqueness of the root comes from
  torsion-freeness. The countable case is standard continuity of `K_0`
  along the union of the pulled-back finite-stage algebras. The maps
  `pi_n^*` are injective because the coordinate projections have sections,
  and the functional-calculus approximation stays inside the pulled-back
  C*-subalgebra. I found no gap. I reran `mobius_check.py`, which passed.
* **`blockwise-rordam-halving-forces-proper-infiniteness-proof`.**
  - Step 1 is exactly item 3 of the rigidity claim, applied to the finite
    block classes.
  - The group count needs `|U| <= |C|+sM < RM=r`, so the real base
    dimension is at most `2r-2`. The primary-obstruction statement (fibre
    `S^(2r-1)`, so sections extend over cells of dimension at most `2r-1`)
    applies to the finite CW complex `(S^2)^U`.
  - Step 4: `w_k^* w_l = delta_kl (1 tensor e_kk)` holds because the
    `xi_(G(k))` are pointwise orthogonal (the `J_G` are disjoint and the
    `s_j` have orthogonal ranges), and `w_k w_l^* = 0` for `k != l`. Both
    one-sided tail estimates are right. The key point is that only finitely
    many of the disjoint finite sets `J_G` meet an initial segment. The
    partial sums are contractions, so the strict limit exists.
  - Step 5 and the transported-seed induction (Step 6) are correct. The
    solver's weakest-step candidates hold up.
* **Hidden assumptions.** None beyond the stated setting: constant
  isometries in `1 tensor B(l^2)` and rank-one summands with pulled-back
  Hopf-tensor range bundles. The claim says plainly that it does not cover
  non-blockwise (shifted) halvings in `M(A)`, or designs without an
  infinite bounded-relative-support family. That scope statement is honest.
* **Duplicates.** `bin/cairn search --similar` found no duplicate. The
  nearest nodes are `uniformly-doubled-rordam-steps-force-proper-infiniteness`
  (same rank-versus-dimension mechanism, but with multiplicities given by a
  duplicated branch list), `dyadic-rordam-identical-pairing-destroys-sdr` and
  `one-cofinal-rank-amplifying-branch-forces-proper-infiniteness`. All are
  correctly separated by `distinct_from`. The new content is the K-theoretic
  hypothesis (H1) plus the rigidity input, and the rank-versus-dimension step
  is reused. The rigidity claim is a standard computation. It is recorded as
  a reusable lemma, and no novelty is claimed.
* **Literature.** On 2026-09-16 I confirmed from the arXiv abstract page
  that arXiv:2506.10902 is at v2 (2026-05-08). I did not re-fetch the TeX
  source, so the wording of Problem LXVI is taken from the solver. An arXiv
  API query (abstract terms "finite projection", "infinite", "simple",
  newest first) turned up only arXiv:2608.30906 (Sutradhar, pure
  infiniteness transfer), whose abstract does not address LXVI. The
  general web-search budget was exhausted, so journal-only sources may be
  missed. The status stays open.
* **Notes.** I checked two sketch claims in section 4:
  - In `M={r in Z[1/2]: 0<=r<=1}`, `1/2+1/2=1+1` has no refinement: the
    row sums force every `c_ij <= 1/2` with rows summing exactly to `1/2`,
    and then a column sum of `1` forces a zero column.
  - The stability-index recursion `mu(p_(n+1)) in {2mu(p_n)-1, 2mu(p_n)}`
    holds.
  All other items there remain sketches and are labelled as such.

Changes:
- Wording: the halving example in the rigidity claim now says "2^n copies
  of `e`", replacing `e directSum e` with exponent `2^n`.
- Item 2 of the rigidity route now justifies MvN equivalence via isomorphic
  range bundles.
- (H1) now names the index set of the `j`, which removes a clash with the
  coordinate set `N`.
- Blockwise proof: added explicit justifications for strict completeness,
  positivity of `VV^* <= Q`, and fullness.

Verdict: sound. Both nodes land with the minor fixes above. LXVI and the
worked hole `stw99-lxvi-mixed-algebra-with-dyadic-finite-projection` stay
open.
