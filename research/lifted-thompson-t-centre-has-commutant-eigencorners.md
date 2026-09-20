---
rg: 2
id: lifted-thompson-t-centre-has-commutant-eigencorners
kind: claim
title: Every corona representation of T-bar that moves the central translation has an exact eigencorner of it, with eigenvalue other than 1, in its relative commutant
distinct_from:
  commutant-projection-extraction: that is the same extraction for every countable group and every central element; this is its single instance H = T-bar, eps = z, which is all that the torsion-free seed needs. The general claim implies this one (route lifted-thompson-t-eigencorners-via-projection-extraction); the converse is not claimed.
  lifted-thompson-t-is-not-mf: that says rho(z) = 1 for every rho; this only asks that rho(z) != 1 be witnessed by a commutant eigencorner, and is vacuously implied by it.
  central-eigencorners-die-over-full-radical-quotients: that assumes an eigencorner and shows it is fixed when T has full radical; this asks for the eigencorner.
---

**OPEN.**  Let `Q` be a norm matrix corona, `rho : T̄ -> U(Q)` a homomorphism
and `B = rho(T̄)' ∩ Q`.  If `rho(z) != 1`, then there are a nonzero
projection `P in B` and `lambda in C` with `lambda != 1` such that

```text
rho(z) P = lambda P.                                   (EC)
```

**Approximate form.**  It is equivalent to ask the following, by the diagonal
lemma in `lifted-thompson-t-eigencorners-via-projection-extraction`.
For some `delta > 0` and every `eta > 0` there are a nonzero projection
`q in B` and `lambda` with `|lambda - 1| >= delta` and
`||(rho(z) - lambda) q|| <= eta`.

## Position in the graph

- `lifted-thompson-t-is-not-mf` holds if and only if both this claim and
  `thompson-t-has-full-mf-radical` hold.  The forward direction uses item 3
  of `lifted-thompson-t-mf-radical-dichotomy`, and this claim holds
  vacuously.  The reverse direction is the route
  `lifted-thompson-t-not-mf-via-central-eigencorners`.  So the hole of the
  flagship has split into a Thompson-`T` statement and this corona-commutant
  statement, and each can fail on its own.
- **Where it already holds.**  (EC) holds whenever `sp(rho(z))` has an
  isolated point `lambda != 1`: take the spectral projection, which lies in
  `C^*(rho(z)) <= B`.  In particular it holds whenever `rho(z)` has finite
  order.  So only unitaries `rho(z)` whose spectrum is perfect away from `1`
  are in question.  Assuming `thompson-t-has-full-mf-radical`, item 3 of
  `central-eigencorners-die-over-full-radical-quotients` shows these are the
  only ones that can occur.
- **Why it is not formal.**  In the block and continuous-phase test models of
  `commutant-projection-extraction`, the eigencorner was found either as a
  block projection or as a rank-one wave packet.  For `T̄` every
  bounded-rank corner is excluded.  Suppose the ranks `r_n <= R` and the
  corner representation moves `g`.  Pass to a subsequence of constant rank
  on which it moves `g` by at least `eps`, and use compactness of `U(r)` along
  an enumeration of `T̄`.  This gives a homomorphism `T̄ -> U(r)` that moves
  `g`.  Its image is finitely generated and linear, hence residually finite
  (Mal'cev).  But `T̄` has no proper finite-index subgroup (item 3 of
  `lifted-thompson-t-perfect-centre-cubically-elliptic`), so the image is
  trivial, a contradiction.  So any witness `P` has unbounded rank.
- **Structure available for `T̄` and not for a general `(H, eps)`.**
  - `z` has roots of every order: `g_n^n = z` (item 1 of
    `lifted-thompson-t-perfect-centre-cubically-elliptic`).
  - The dilation `lambda(g)(x) = g(2x)/2` satisfies `lambda(z)^2 = z`.
  - The finite quotients `T̄/<z^(2^k)>` are the rotation centralizers
    `C_T(r_k)`.

  Any proof specific to `T̄` has to use one of these.  The general claim
  `commutant-projection-extraction` has none of them.

## Attempts

- **2026-09-19 (swarm-0917-w16-w16-ptm-last1, operator-algebras): cutting
  inside `C^*(rho(z))` proves (EC) off the arcs of the spectrum, and dies on
  them.**

  *What works.*  Let `mu != 1` be a point of `K = sp(rho(z))` whose connected
  component in `K` is `{mu}`.  In a compact Hausdorff space components equal
  quasi-components.  So for every `eta > 0` there is a set `U` with
  `mu in U`, `U` relatively clopen in `K`, `diam U < eta` and `1 notin U`.
  Its indicator is continuous on `K`, so `P_U = chi_U(rho(z))` lies in
  `C^*(rho(z)) <= B`.  It is nonzero, since `mu in K`, and it satisfies
  `||(rho(z) - mu) P_U|| <= eta`.  That is the approximate form with
  `lambda = mu` and `delta = |mu - 1|`.  The diagonal lemma of
  `lifted-thompson-t-eigencorners-via-projection-extraction` then turns it
  into (EC).  So (EC) holds unless every point of `K \ {1}` lies in a
  nondegenerate arc contained in `K`.

  *Combined with full `T`.*  Assume `thompson-t-has-full-mf-radical`, and
  apply item 1 of `central-eigencorners-die-over-full-radical-quotients` to
  the exact corner obtained above.  Every corona representation `rho` of `T̄`
  with `rho(z) != 1` then has the following property: `sp(rho(z)) \ {1}` is
  nonempty and is covered by nondegenerate arcs of `sp(rho(z))`.  This
  sharpens item 3 of that node from "no isolated points" to "no degenerate
  components".

  *Where it dies.*  On an arc of `K` the algebra `C^*(rho(z)) ≅ C(K)` has no
  nonzero projection supported near a point.  So the eigencorner, if it
  exists, must come from `B` strictly outside `C^*(rho(z))`, that is, from
  the relative commutant of the whole image `rho(T̄)`.  This is the
  connected-arc case of `commutant-projection-extraction`, now for a single
  group.  Neither of the other two structures helps here.
  - The roots `g_n^n = z` give unitaries `rho(g_n)` that commute with
    `rho(z)` but not with `rho(T̄)`.  So their spectral projections are not
    in `B`.
  - The dilation `lambda` gives a second representation `rho o lambda`,
    whose "centre" `rho(t_1)` is a square root of `rho(z)`.  But `t_1` is not
    central, so this again leaves `B`.

  The next step is either a real-rank-zero statement for `B` restricted to
  arcs, or a counterexample built as a corona representation of `T̄` with
  `rho(z)` of arc spectrum.  By the bounded-rank remark above, any such
  counterexample has unbounded rank.

- 2026-09-19 swarm-0917-w16-w16-ptm-follow (stability-approximation,
  follow-through).  Outcome: a reduction to a Thompson-free statement.  The
  target stays OPEN.
  - **Established on the way.**
    - `funar-sergiescu-lifted-thompson-t-is-t311` (imported, verbatim).
    - `lifted-thompson-t-is-a-torus-knot-group-quotient`: `T̄` is a quotient
      of `K(3,4) = <x, y | x^4 = y^3>` with `x^4 -> z`.  The lifts `a`, `b`
      of `C^(-1)B` and `C^(-1)` satisfy `a^4 = b^3 = z` and `(ba)^5 = z^3`.
      This was checked in exact arithmetic in
      `experiments/torus-knot-cover-2026-09-17/`.  Hence
      `rho(T̄)' ∩ Q = {rho(a), rho(b)}' ∩ Q`.
    - `matricially-stable-groups-have-central-eigencorners`: over a
      matricially stable group, every spectral value of a central element
      has an exact commutant eigencorner.
  - **New route.**  `lifted-thompson-t-eigencorners-via-torus-knot-cover`
    reduces this target to `torus-knot-group-k34-has-central-eigencorners`.
    That claim in turn follows from `torus-knot-group-k34-is-matricially-stable`
    (route `torus-knot-group-k34-central-eigencorners-via-stability`).  So the
    flagship follows from `thompson-t-has-full-mf-radical` plus stability of
    one fixed one-relator group, a statement that mentions no Thompson group.
  - **Evidence for the open leaf.**
    - `pg = K(2,2)` is matricially stable (ESS Theorem 4.9).
    - Dadarlat's rational obstruction vanishes, since `H^2(K(3,4); Q) = 0`.
    - Hadwin-Shulman give Hilbert-Schmidt stability only.
    - One-sided correction fails (the `diag(1, i)` example).
  - **Caveat.**  A counterexample to the `K(3,4)` statements refutes only
    this route, not the target: the bad pair need not satisfy the Thompson
    relators.

- 2026-09-19 swarm-0917-w17-w17-ptm-follow (finite-models, follow-through).
  Outcome: a class kill.  (EC) fails for the Brieskorn cover `Λ` of `T̄`.
  The target stays OPEN.
  - **Established.**
    - `brieskorn-345-gauge-pair-has-no-eigencorner`.  There is a corona
      representation `Θ` of `Λ = <x, y | x^4 = y^3, (yx)^5 = x^12>` with
      `||Θ(c) - 1|| = 2` and no commutant eigencorner with `λ != 1`.  It is
      built as follows.
      - Take the left-regular representations of the congruence quotients
        `G_q` of the `(3,4,5)` triangle group.  These have a uniform Kazhdan
        constant (Salehi Golsefidy--Varjú Theorem 1 and Lubotzky
        Prop. 1.11 (ii), quoted verbatim).
      - Twist them by a gauge field with face fluxes `(φ, φ, 3φ)`, where
        `φ` is a Lipschitz phase of the word length.
    - `brieskorn-lattice-345-is-not-matricially-stable`, via
      `matricially-stable-groups-have-central-eigencorners`.
  - **Class killed.**  Every argument for (EC) on `T̄` that uses only
    relations holding in `Λ`.  This includes the torsion data
    `a^4 = b^3 = z`, `(ba)^5 = z^3`, the lattice and Seifert structure, the
    Haagerup property, perfectness and `H_2 = 0`.
    - *Invariant:* a prescribed-flux gauge field on the finite Cayley
      complexes of `Δ = Λ/<c>`, together with their uniform spectral gap.
    - *Death step:* for an almost commuting projection `P`, the modulus
      vector `s_h = ||P e_h||` is almost invariant.  The gap flattens it, so
      `|λ - 1| <= ε + 2 sqrt(2) η / κ`.
  - **Settles the w16 caveat.**  The `K(3,4)` pair failed only
    `(yx)^5 = x^12`.  The gauge pair satisfies it, so the extra Brieskorn
    relation does not restore eigencorners.  So no variant of
    `lifted-thompson-t-eigencorners-via-torus-knot-cover` can go through the
    Brieskorn cover `Λ` in place of `K(3,4)`, whether via eigencorners or via
    matricial stability of `Λ`.
  - **What a proof must use.**  The kernel `N̂` of `Λ -> T̄`, that is, the
    commutator relators of `T`.  The models violate
    `r_1 = [βαβ, α^2 βαβ α^2]` by at least `1` in norm.  The gate is sharp:
    the mechanism needs finite permutation models of `Λ/<c>` with a uniform
    gap, and `T = T̄/<z>` has no nontrivial finite quotients.  So the
    remaining question is (EC) for corona representations of `Λ` that kill
    `N̂`.  Any proof must use a property of `T` that no finite permutation
    model of the triangle group `Δ` shares, for example the central
    quotients `T̄/<z^(2^k)> = C_T(r_k)` listed above.
- **2026-09-20 (swarm-0917-w21-w21-ptm-last1, quantifier-shift).**  Outcome:
  the flagship does not need (EC) in every representation.  One scalar twist
  in one representation suffices.  The target stays OPEN.
  - **Established.**  `lifted-thompson-t-twist-set-is-trivial-or-the-circle`
    (route `...-proof`).  It concerns two sets:
    - `Sigma`, the set of `mu` with `sigma(z) = mu 1` for some corona
      representation `sigma`;
    - `S`, the union of the spectra `sp(rho(z))`.

    Both are closed subgroups of `S^1`, by tensoring, conjugation and
    diagonal limits.  Each is either `{1}` or `S^1`.  `Sigma = S^1` if and
    only if `T` is MF, and `S = S^1` if and only if `T̄` is MF.
    - For `mu != 1` in `Sigma`, item 1 of
      `central-eigencorners-die-over-full-radical-quotients` with `P = 1`
      shows that `T` is not full, so `T` is MF because it is simple.
    - Conversely, if `T` is MF, the `-1` corner of `pi(r_1)` pulled back
      along `iota_1` gives `-1 in Sigma`.
    - The dilation then gives `2^j`-th roots: `sigma(t_j)` is central in
      `sigma(lambda^j(T̄))` and has finite spectrum.  So `Sigma` is
      infinite.

    This is the first place where the dilation, listed above as unused
    structure, does work.  It works on scalar twists and not inside `B`.
  - **New decomposition.**  The new claim `lifted-thompson-t-mf-descends-to-t`
    reads (D): `T̄` MF implies `T` MF.  Equivalently:
    - some representation has an exact eigencorner of `z` with `lambda != 1`;
    - or some representation sends `z` to `-1`, or to any one chosen
      `mu != 1`.

    The route `lifted-thompson-t-not-mf-via-mf-descent` gives
    `flagship <=> thompson-t-has-full-mf-radical AND (D)`.  This target
    implies (D), via `lifted-thompson-t-mf-descent-via-central-eigencorners`.
    (D) is the weakest possible second conjunct, it holds outright when `T`
    is MF, and it fails only in the single world where `T` is full and `T̄`
    is MF.
  - **Consequence for this node.**  The obstruction recorded by w16 is about
    a single representation: arc spectrum, and no projections in
    `C^*(rho(z))`.  It no longer blocks the flagship.  A proof of (D) may
    change the representation by tensor powers, subsequences, diagonal
    limits and precomposition with `lambda^j`.  It need only reach one
    representation with a scalar corner.
  - **Where this dies for (EC) itself.**  The twist-set argument produces
    eigencorners only in *other* representations: corners of
    `sigma o lambda^j`, and diagonal limits.  It gives nothing for a fixed
    `rho` with arc spectrum.  So (EC) for all `rho` is not reached, and in
    the world where `T` is MF it remains a separate open question that the
    flagship does not need.
- 2026-09-20 swarm-0917-w23-w23-ptm-last1 (calibration).  Outcome: a class
  kill.  The target stays OPEN.
  - **Established on the way.**
    `thompson-t-escapes-quotient-free-mf-permanence-closure`: the class
    `D_T` of groups with no copy of `T` contains `T̄` and all amenable,
    residually finite, linear, hyperbolic, LEF and LEA groups.  It is closed
    under subgroups, arbitrary extensions, arbitrary graphs of groups,
    colimits, unrestricted products, ultraproducts and local embeddings.  FA
    for `T` comes from `alpha^4 = beta^3 = (beta alpha)^5 = 1` and Serre's
    bridge lemma, which is proved in full.  So every homomorphism from `T`
    to such a group is trivial.
  - **What it kills.**  Any argument for descent (`T̄` MF implies `T` MF),
    or for the negation of `thompson-t-has-full-mf-radical`, that builds a
    host group from `T̄` and the known MF classes by these operations.  The
    step where every such argument dies is that none of the operations
    creates a copy of `T`.  The only exit is a quotient of `T̄`, and these
    are exactly the central quotients `T̄/<z^j>`.  In corona terms, the exit
    is a representation with `rho(z)` scalar or of finite order, which is
    this node's eigencorner.
  - **Structural fact noted, not used.**  `T̄ = D · F̄` is an exact
    factorization, a Zappa--Szép product.  Here `D ≅ Z[1/2]` is the group
    of dyadic translations and `F̄` is the periodic extension of `F`: write
    `g = (x + g(0)) ∘ f` with `f(0) = 0`.  So `B = rho(D)' ∩ rho(F̄)' ∩ Q`.
    Also, `D` is the intersection of the dilation tower
    `C(t_k) ≅ T̄`, where `t_k = x + 2^(-k)`.  Neither fact produces a
    projection in `B` on an arc of `sp(rho(z))`.  `F̄` does not normalize
    `D`, so the spectral projections of `rho(D)` do not commute with
    `rho(F̄)`.
