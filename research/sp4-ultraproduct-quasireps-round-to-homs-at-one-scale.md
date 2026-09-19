---
rg: 2
id: sp4-ultraproduct-quasireps-round-to-homs-at-one-scale
kind: claim
title: At one fixed defect scale, every uniform quasi-representation of Sp4(Z) into the matrix ultraproduct is close on one relator's letters to a homomorphism into a tracial extension
distinct_from:
  sp4-quasirep-single-scale-winding-deficit: that bounds the trace-winding by a positive constant times the scale; this asks for rounding to exact homomorphisms, which forces the trace-winding to be exactly 0 (item 4 of sp4-ssd-is-a-matrix-ultraproduct-winding-bound), and it can fail for reasons that have nothing to do with windings.
  sp4-ssd-is-a-matrix-ultraproduct-winding-bound: that is the established reduction and criterion; this is the open stability input the criterion needs.
  blsw-real-lattice-frobenius-stability: that is pointwise Frobenius-norm stability of rank at least three lattices; this is uniform operator-norm rounding of Sp_4(Z) at one scale, inside one C*-ultraproduct, near the letters of one relator.
  mod-s2-stability-forces-honest-torelli-windings: that shows pointwise point-norm stability of Mod(S_2) would force honest windings; this is about uniform maps of Sp_4(Z) at fixed defect, where honest windings vanish.
---

**OPEN.** Notation of `sp4-ssd-is-a-matrix-ultraproduct-winding-bound`:
- `Q = prod_n M_(n!) / c_omega` with trace `tau`;
- a relator `r = prod_{i<=g} [a_i, b_i]` with `k != 0`;
- `a_g = 1/(6g-1)`.

**Claim (UQ).** There are `eps_0 in (0, a_g)` and `delta < 1/(4g)` with the following property. Let
`Pi : Gamma -> U(Q)` be unital with `||Pi(g)Pi(h) - Pi(gh)|| <= eps_0` for all `g, h in Gamma`. Then there are:
- a unital C*-algebra `M` with a tracial state `tau_M`;
- a unital *-homomorphism `theta : Q -> M` with `tau_M o theta = tau`;
- a homomorphism `Rho : Gamma -> U(M)`,

with `||theta(Pi(y)) - Rho(y)|| <= delta` for the `2g` letters `y in {a_i, b_i}`.

The model case is `M = Q`, `theta = id`, with closeness on all of `Gamma`. That is uniform `U(Q)`-stability of
`Sp_4(Z)` with estimate `delta` at the single scale `eps_0`. (UQ) asks for less: one scale, one relator's letters,
and any trace-preserving image.

**Why it matters.** By items 4 and 5 of the reduction node, (UQ) gives `w(eps_0) = 0`. Then:
- (SSD) of `sp4-quasirep-single-scale-winding-deficit` holds with every `c > 0` (route
  `sp4-single-scale-deficit-from-ultraproduct-rounding`);
- `Theta_inf = 0`, and `sp4-quasirep-winding-ratio-has-a-deficit` holds;
- with `deligne-finite-parameter-group-has-period-prime-to-three`, the flagship `deligne-triple-cover-exact-mf-radical`
  follows.

**How it can fail.**
1. *The all-MF branch.* If `P_op = R/Z`, then (UQ) fails at every scale and for every admissible `delta` (item 6 of
   the reduction node). A proof of (UQ) therefore proves `P_op != R/Z`.
2. *Non-winding obstructions.* (UQ) can fail while (SSD) holds. (SSD) needs only `|kappa^tau| < eps_0 nu/(2 pi)`,
   while (UQ) needs rounding. Burger–Ozawa–Thom's non-stability for free subgroups is recorded in GLMR, quoted below.
   It is a construction in `U(H)` for infinite-dimensional `H`. If a version of it, induced from a free subgroup of
   `Sp_4(Z)`, can be realized inside `U(Q)` at a fixed scale, then (UQ) is false for a reason unrelated to the
   Deligne class. Only the winding form (SSD_Q) would then survive. This is the first check to run.

**What the literature gives and does not give.** Glebsky–Lubotzky–Monod–Rangarajan, *Asymptotic cohomology and
uniform stability for lattices in semisimple groups* (arXiv:2301.00476v4), prove uniform stability, uniform in the
dimension, for lattices in groups with their Property-G(Q1,Q2). The targets are finite-dimensional unitary groups
with submultiplicative norms. On type `C_n` they say, verbatim (§6.3):

> "Note that our method will not work for the split simple real Lie groups of type Cn or G2. In the case of Cn, for
> any two two proper subdiagrams covering the vertices of the Satake diagram, at least one of them must either itself
> be of type Cm, which corresponds to the simple group Sp(2m,R) which does not have the 2½-property (as
> H2b(Sp2m(R),R)≠ 0), or of type A1, which corresponds to the simple group SL2(R)."

The PDF text extraction renders `H^2_b` as "H2b".

Also from GLMR:
- Theorem 1.0.11: "If Γ is a higher rank lattice then it is uniformly U(1)-stable." Abelian targets carry no
  commutator winding, so this is consistent with (UQ) and says nothing about it.
- Proposition 1.0.12: the preimage of a cocompact lattice in the universal cover of a Hermitian group "is not
  uniformly U(1)-stable". The quasimorphism is the `Z`-coordinate of the central extension. For `Sp_4(Z)` (not
  cocompact) the analogous object is the covering cocycle `b` of `E_infinity`. The scalar obstruction of item 1
  above is the matricial shadow of that quasimorphism.
- Introduction: "if a group contains a non-abelian free subgroup, then it is not strongly Ulam stable." Strong
  Ulam stability allows all `U(H)`. (UQ) is about the single target `Q`, so this does not decide it.

Even a C_2 extension of GLMR would not apply verbatim. A uniform quasi-representation into `U(Q)` lifts only to
finite-dimensional maps whose defect is small on growing windows, not on all of `Gamma` (remarks of the reduction
node). GLMR's defect-diminishing argument would have to be run with `U(Q)` as target.

**Heuristic, not proved: the Deligne content of (UQ) is central.** Let (UQ_0) be the weaker statement where
`theta(Pi)` need only be close to a map `Rho` that is a homomorphism modulo scalars, i.e. a projective representation
into `U(M)`. The heuristic is that (UQ) splits as (UQ_0) plus a statement about the scalar cocycle.
- Burger–Monod give `H^2_b(Gamma, R) = R [b]`, spanned by the Kähler class. So the scalar cocycle of `Rho` should be,
  up to a small coboundary, `e(t b)` for a small real `t`.
- Rephasing `Rho` by scalars does not change commutators. So only `t` matters for the trace-winding, and
  `kappa^tau = t k` as in the twisted algebras of the unlanded lemma sp4-winding-deficit-fails-in-twisted-tracial-algebras.
- If `M` can be chosen with finite-dimensional-type rigidity (so that `t` lies in `P_op`), then the rounded maps have
  `kappa^tau` in `k P_op`, near `0`.

If this were made rigorous, it would say: under (UQ_0), (SSD) holds iff `P_op` has no nonzero elements of size
`O(eps_0)`, i.e. iff `P_op != R/Z` (a closed subgroup other than `R/Z` is finite). Everything that is not about the
Deligne class would then sit in (UQ_0). Missing steps:
- the identification of the scalar cocycle needs the ordinary class, `H^2(Gamma, R)`, not only `H^2_b`, to be `R [b]`
  on the relevant range;
- the step that puts `t` in `P_op` needs a model of `M` by matrices.

Neither step is proved here.

## Attempts
- **2026-09-19, swarm-0917-w17-w17-deligne-pull: posed; direct attack deferred.** The obvious attack is to quote GLMR
  uniform stability. It dies twice: GLMR exclude type `C_n` because `H^2_b(Sp_4(R), R) != 0` (quoted above), and
  their theorems are for targets `U(d)` with defect small on all of `Gamma`, which the lifts of a map into `U(Q)` need
  not have. The next step is the non-winding check of "How it can fail", item 2: can a Burger–Ozawa–Thom-type
  construction, induced from a free subgroup of `Sp_4(Z)`, be realized inside `U(Q)` at a fixed scale? If yes, (UQ)
  is false and only (SSD_Q) survives.
- **2026-09-19, swarm-0917-w18-w18-deligne-follow (stability-approximation): the BOT check is run, and the literal
  construction dies.** See `sp4-uq-free-subgroup-induced-quasireps-round`, ESTABLISHED and unreviewed.
  - *Literal induction rounds.* Exact induction through finite `Gamma`-sets from a free (or torsion-free Haagerup)
    group `L`, with any uniform `eps`-quasi-representation of `L` as coefficient, is `eps`-close to an honest
    representation on **all** of `Gamma`. So it satisfies (UQ) with `M = Q` and `delta = eps`.
  - *Where it dies.* The invariant is the cocycle class in `prod Hom(Lambda_j, L)`. Property (T) of the
    finite-index `Lambda_j` makes it trivial.
  - *Other block-monomial models.* With defect small on all of `Gamma`, such a model is `2 eps`-close to
    `Ind_Lambda sigma`, so the free subgroup drops out.
  - *Free patterns are trace-null.* Local stabilizer patterns of an infinite-index noncentral `H` have `omega`-density
    tending to `0` (Stuck–Zimmer), and they die under the admissible `theta : Q -> ` tracial ultraproduct.
  - *Remark.* Letter-only rounding already makes quasimorphism-type BOT witnesses, which are detected on powers,
    irrelevant to (UQ).
  - *Still open.* Non-monomial maps, and windowed block-monomial models, i.e. almost-flat local systems on finite
    covers. Item 2 of "How it can fail" is not refuted, but its only named mechanism is gone.
