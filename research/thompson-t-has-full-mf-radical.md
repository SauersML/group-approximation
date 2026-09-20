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

- **2026-09-19 (swarm-0917-w17-w17-ptm-break, belief breaker, census plus
  locus gap): target still open; `delta_2` computed exactly; a
  dimension-free gap near the SL(2,Z) locus.**  Recorded in
  `thompson-t-defect-gap-central-square-locus`.
  - *`delta_2`.* `delta_2 = 0.3491491...`, a root of
    `d^10 - 5d^8 + 5d^6 + 6d^4 - 9d^2 + 1`. It is strictly below
    `delta_1 = 0.5176` and below the amenable-locus constant `1/2`. It is
    attained by an `SU(2)`-dense pair with `A^2 = -1`, where `r_1 = 1` and
    `eps_2 = eps_P`.
  - *Locus gap.* Every exact pair satisfies
    `||BA^2 - 1|| <= 5 eps_2 + 2 eps_P + 45 ||[A^2, B]||`. Hence:
    - `7D + 45 gamma >= 2/3`, with `gamma = ||[A^2,B]||`;
    - `D >= 1/7` on the SL(2,Z) locus `gamma = 0`.

    So MF witnesses must keep `A^2` uniformly non-central:
    `gamma >= 2/135 - o(1)`.
  - *Where it dies.* It dies at the two steps that move `J = A^2` past
    `B`. The next step would be to bound `gamma` by the defect through
    `r_1` and `r_2`. The dimension-2 minimiser (`r_1 = 1`) shows that `r_1`
    alone cannot do this.
  - *Census caveat.* A planted control (`delta_2 (+) delta_2` in `U(4)`)
    was never recovered by fixed-profile L-BFGS, relator homotopy or the
    `A^2 = -1` locus search, whose best value was 0.5176 over 1507 runs.
    Negative random-census results at `n >= 4` are therefore uninformative,
    and nothing here supports or refutes `inf delta_n = delta_2`.
- **2026-09-19 (swarm-0917-w17-w17-ptl-follow, reframing): split through the
  triangle cover, target still open.**
  - *Decomposition*
    (`thompson-t-not-mf-iff-triangle-gap-and-rounding`, ESTABLISHED). `T` is
    not MF iff (R_Delta) and (S_T) both hold.
    - (R_Delta) is a gap `inf gamma_n > 0` for `r_1, r_2` on honest
      representations of `Delta(4,3,5)`.
    - (S_T) is a uniform rounding of `phi (+) phi-bar (+) 1_k` onto honest
      `Delta`-representations.
    - Each condition is necessary on its own. `gamma_2 = (sqrt 5 - 1)/2`,
      which is larger than `delta_1`.
    - The undoubled form of (S_T) implies PW, by a conjugation-path lemma
      for `kappa_P`.
    - Route: `thompson-t-not-mf-via-triangle-cover-rounding`.
  - *Kill* (`thompson-t-padded-cover-stability-is-inert`, ESTABLISHED).
    Padded stability with a nontrivial auxiliary block (Willett `R`/`R_q`,
    including the K(3,4) theorem) transfers nothing. The corrected
    representation's defect is the defect of `theta`, up to `L eps`.
  - *What is left.* The next step is (R_Delta), a question about honest
    representations of a Fuchsian group, together with trivially padded
    (S_Delta).
- **2026-09-20 (swarm-0917-w20-w20-ptl-follow, finite-models / decomposition): finitary
  reformulation, target still open.** Recorded in `thompson-t-mf-iff-finite-quotient-corners`.
  - *Theorem A.* `T` is MF iff, for every `eps > 0`, some finite quotient `F` of `Z/4 * Z/3` has a
    unitary representation `pi` (which may be taken to be a multiple of the regular one) and a projection
    `P` with three properties:
    - `||[P, pi(a)]||, ||[P, pi(b)]|| < eps`;
    - `||P(pi(r) - 1)P|| < eps` for `r = r_1, r_2, r_P`;
    - a compressed generator at distance `>= 1` from `1`.

    The proof pads an exact pair by Willett's `R_q`-stability of `K(3,4)`, retwists the central element
    `x^4 = y^3` by its own fourth and third roots to land in a finite quotient of `Z/4 * Z/3`, and cuts
    the original block back out. The converse is polar decomposition plus spectral rounding.
  - *Belief change.* The finite-quotient class that w19 declared dead (whole finite-image
    representations have `D >= 1/2`) is complete once corners are allowed. The padded-inert kill concerns
    the absolute defect only; on the corner, the padding carries the witness exactly.
  - *Theorem B.* Every corner in `F` has level `>= 1/(18 diam F)`. Averaging over `F` rounds a corner to
    an invariant subrepresentation, and the w19 bound `1/2` applies to it. So witnesses need Cayley
    diameter `>= 1/(18 eps)`, and in logarithmic-diameter families such as `SL(2, Z/q)` they need
    exponential size.
  - *What is left.* The target is now `inf_F c(F) > 0` over finite quotients of large diameter. A proof
    must use averaging along `r_1, r_2`, which the diameter does not see. It is open whether `F` may be
    taken to be a quotient of `Delta(4,3,5)`; this would need `R_q`-stability of `Delta(4,3,5)`,
    conditional on the pentagon winding.
