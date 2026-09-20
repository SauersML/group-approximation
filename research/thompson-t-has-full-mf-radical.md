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

- **2026-09-20 (swarm-0917-w23-w23-ptl-last1, census-computation /
  probability-random): an explicit balanced upper bound, and a documented
  blind spot in numerical search; target still open.**
  - *Setup.* The claim is equivalent to a uniform lower bound on the defect
    `D` of nontrivial irreducible exact pairs
    (`thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`). The sector that
    matters for a `D -> 0` sequence converging to the regular trace is the
    balanced one: all eigenvalues of `A` and of `B` have equal multiplicity.
    This reduction was posted on the bus in wave 22 and is not a node here.
  - *Established* (`thompson-t-balanced-irreducible-pair-with-defect-0636`).
    - There is an irreducible exact balanced pair in `U(12)` with
      `D <= 0.6360452410185`. It is certified by polar correction and a
      Lipschitz bound. All three relators are active at it, and
      `||[A^2, B] - 1|| = 1.376`, so it is not near-central. Its commutant
      margin is `0.238`.
    - Hence `delta_bal(12k) <= 0.63605` for all `k`.
    - Every balanced sum of blocks of dimension at most 2 has `D >= 0.99`.
  - *Obstruction to the numerical route.* Fixed-spectrum Riemannian descent
    with basin hopping cannot estimate `lim delta_bal(n)` at `n >= 24`.
    - It is calibrated at `n = 2`, and at `n = 12` with spinor spectra.
    - At `n = 24`, the planted double witness has `D = 0.636`. Random starts
      end at `1.01`-`1.23`, and perturbations of size at least `0.1` of the
      planted point polish to `0.665`-`0.688`, not back to `0.636`.
    - At `n = 6` and `n = 24` with spinor spectra, every start is captured by
      direct sums of a spurious critical point of the 2-dimensional spinor
      curve (`t = 2.2816`, `D = 1.3126`, with `r_1 = 1` exactly). The true
      value is `0.3491`.
  - *So a census cannot decide* whether `delta_bal(n)` stays bounded below
    along `n = 12k`. Any census-based lower-bound conjecture at `n >= 24` must
    first recover the planted double.
  - *Next falsifiable step.* Either of the following:
    - a structured ansatz, for example `A` with `A^2` block-diagonal over a
      `Z/2`-grading, or pairs induced from finite quotients of `Z/4 * Z/3`,
      that beats `0.636` in some `n = 12k`;
    - a proof that balanced irreducible pairs have `D >= c > 0`, for some
      explicit `c`, via the spectral constraint `mult(B = 1) > mult(A = 1)`
      that the block count in item 2 of the new claim exploits.
