---
rg: 2
id: thompson-t-has-full-mf-radical
kind: claim
title: Thompson's group T has full MF radical, equivalently T is not MF
distinct_from:
  thompson-v-is-not-mf: that is the same exclusion for V, which contains T; this is strictly stronger, because T <= V makes Rad(T) = T imply Rad(V) = V, while an MF model of T says nothing about V.
  lifted-thompson-t-is-not-mf: that is the exclusion for the torsion-free central extension T-bar; this is its quotient. Item 3 of lifted-thompson-t-mf-radical-dichotomy gives that implies this, and lifted-thompson-t-not-mf-via-central-eigencorners shows the gap between the two is one corona-commutant statement about the central unitary.
  jz-question-5-for-thompson-t-implies-f-nonamenable: that concerns a question of Juschenko--Zheng about T; this is an operator-norm approximation statement.
---

**OPEN.**  Thompson's group `T` (piecewise-dyadic homeomorphisms of the circle)
does not embed in the unitary group of a norm matrix corona
`prod M_(k_n) / (+) M_(k_n)`.

`T` is simple (Cannon--Floyd--Parry, *Introductory notes on Richard
Thompson's groups*, Enseign. Math. 42 (1996), Thm 5.8).  So the following are
equivalent:
- `T` is not MF;
- `Rad_MF(T) != 1`;
- `Rad_MF(T) = T`.

## Position in the graph

- **Upward.**  It implies `thompson-v-is-not-mf`, because `T <= V` and `V` is
  simple (route `thompson-v-not-mf-via-thompson-t`).  Through
  `property-t-free-leavitt-via-thompson-v-not-mf` it therefore implies the
  binary-Leavitt endpoint `property-t-free-leavitt-full-mf-radical`.
- **Downward.**  It is implied by `lifted-thompson-t-is-not-mf` (item 3 of
  `lifted-thompson-t-mf-radical-dichotomy`).
- **Towards the seed.**  Together with
  `lifted-thompson-t-centre-has-commutant-eigencorners`, it implies
  `lifted-thompson-t-is-not-mf` (route
  `lifted-thompson-t-not-mf-via-central-eigencorners`), and hence both deep
  inputs of `property-t-free-manuscript-results`.

## What a refutation looks like

The claim is refuted by an MF model of `T`, that is, operator-norm
asymptotic unitary representations of `T`'s finite presentation that
separate points.  Two remarks limit the search.
- `T` has no nontrivial finite-dimensional unitary representation, since it
  is infinite simple and finitely generated, and so is not residually
  finite.  An MF model must have unbounded dimension and must be only
  asymptotically multiplicative.
- Finite subgroups of `T` are cyclic (`finite-subgroups-of-thompson-t-are-cyclic`),
  and the rotation subgroup `Q/Z cap Z[1/2]` is locally cyclic.  So local
  obstructions of the finite-subgroup kind that are used for `V` (for example
  through `S_4 *_(S_3)` gluings) are not available for `T`.

## Attempts

- **2026-09-19 (swarm-0917-w16-w16-ptm-last1, reframing): attack deferred;
  node created to carry an exact decomposition.**  This node was created to
  record that the flagship hole `lifted-thompson-t-is-not-mf` is equivalent to
  this claim plus `lifted-thompson-t-centre-has-commutant-eigencorners`.  No
  direct attack was made.  Two routes that one might copy from `V` do not
  carry over.
  - *Kazhdan transport.*  `T <= V` has the Haagerup property
    (`thompson-v-has-haagerup-property`), so it has no infinite Kazhdan
    subgroup to transport from.
  - *Finite-subgroup gluing.*  The `S_4 *_(S_3) S_3` presentation of `V`
    (`thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3`) and the op-norm
    defect-gap criterion for `V` posted on the live bus in wave 16 use
    non-cyclic finite subgroups.  `T` has only cyclic ones.

  The first falsifiable step for the next worker is to find the analogue for
  `T` of that defect-gap criterion.  A candidate is a presentation of `T` or
  of `C_T(r_1)` as a quotient of an amalgam of finite cyclic groups.  By item
  4 of `central-eigencorners-die-over-full-radical-quotients`, any single
  `C_T(r_k)` may be used instead of `T`.

- **2026-09-19 (swarm-0917-w16-w16-ptl-follow, follow-through): criterion
  found, target still open.**  The step requested above is done. The target
  was not proved.
  - *Presentation.* The Lochak--Schneps presentation of `T` is
    `Z/4 * Z/3 / <<r_1, r_2, (ba)^5>>`, imported verbatim from
    Funar--Kapoudjian Sec. 2.1 as `thompson-t-lochak-schneps-presentation`.
    Its relators were checked in exact PL arithmetic with
    `alpha = rot(1/4)` and `beta = C_cfp^(-1)`. `alpha, beta` generate `T`,
    with CFP `A = baa`, `B = bab`, `C = bb`.
  - *Criterion* (`thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`).
    `T` is not MF iff some `epsilon_0 > 0` makes every exact pair with
    `A^4 = B^3 = 1` and defect `< epsilon_0` trivial. Each generator is
    corrected by spectral rounding, and no amalgam alignment is needed.
    `delta_1 = 2 sin(pi/12)`. The sufficiency half (gap implies full radical)
    uses only the verified relators and generation.
  - *Sandwich* (`thompson-t-pentagon-winding-sandwich`).
    - `kappa([X, JXJ]) = 0` identically, since `J = a^2` conjugates `r_1` to
      its inverse.
    - `c_0 = r_P^12 (a^4)^(-15) (b^3)^(-20)` has Euler number `e = 1`.
    - With Dadarlat's Theorem 3.2 (`T` is Haagerup, so it has a
      gamma-element), this gives: this claim implies
      `thompson-t-pentagon-winding-rigidity` (PW), and PW implies that `T` is
      not quasidiagonal.
    - `Delta(4,3,5)` shows that PW needs `r_1` or `r_2`.
  - *What is left.* The target is the uniform gap. The first falsifiable
    step is PW. A refutation of PW is a sequence of low-defect pairs with
    `12 kappa_P != 0`, and it would prove that `T` is MF. A proof of PW
    must use `r_2`.

- **2026-09-20 (swarm-0917-w22-w22-ptl-break, belief breaker,
  census-computation): the target is still OPEN; there is a new structural
  constraint and a census.**
  - *Constraint* (`thompson-t-low-defect-pairs-are-spectrally-balanced`,
    ESTABLISHED).
    - Every low-defect sequence of `Z/4 * Z/3` pairs has tracial limit
      `a 1 + (1-a) delta_e` on `T`. This comes from the character simplex
      of `T`.
    - So its eigenvalue fractions converge to the "T-line", with
      `f_A(0) = (1+3a)/4` and every other fraction equal to `(1-a)/4`.
    - Nontrivial irreducible sequences have `a <= sqrt(5/17)`.
      Irreducible exact `Delta(4,3,5)` representations have
      `a <= sqrt(13/133)`.
    - Near-central and trivial-heavy families force `a = 1`, so they are
      dead as irreducible witnesses.
    - Tensor powers sharpen the criterion. `T` is MF iff some `D -> 0`
      sequence has trace tending to `delta_e`, which forces balanced
      spectra.
  - *Census* (`experiments/thompson-t-far-sector-census-2026-09-17/`,
    `census2.py`). A local search over exact irreducible `Delta(4,3,5)`
    representations in the far sector (`||[A^2,B]|| > 0.9`) found nothing
    with `D12 < 0.89` for `4 <= n <= 12` (`n = 9, 11` not run). The best
    value was `0.8946` at `n = 6`, and a critical value `0.9606` recurs at
    `n = 5, 6, 7, 10`. The restarts were few, so this is
    evidence and not a bound.
  - *Next falsifiable step.* Search only on the T-line with `a` near `0`,
    that is balanced types, at `n = 8, 16, 24`. Alternatively, prove an
    effective version of item 3 of the constraint that is uniform in `n`.
