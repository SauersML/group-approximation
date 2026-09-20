---
rg: 2
id: lifted-thompson-t-mf-descends-to-t
kind: claim
title: If the lifted Thompson group T-bar is MF then Thompson's T is MF; equivalently, if some corona representation moves the central translation, then some corona representation sends it to a nontrivial scalar
distinct_from:
  lifted-thompson-t-centre-has-commutant-eigencorners: that asks for an exact eigencorner of rho(z) in EVERY representation moving z; this asks for one in SOME representation (or one scalar twist anywhere). (EC) implies this, and this is automatic whenever T is MF, where (EC) is still open.
  lifted-thompson-t-is-not-mf: that says S = {1}; this is only the implication from S = S^1 to Sigma = S^1 and holds outright when T is MF.
  thompson-t-has-full-mf-radical: that is the other conjunct of the flagship; this is true whenever that one is false, so the two fail in disjoint worlds.
---

**OPEN.**  Notation is that of
`lifted-thompson-t-twist-set-is-trivial-or-the-circle`.  Here `Sigma` is the
set of scalar twists of the central translation `z` over corona
representations of `T̄`, and `S` is the union of its spectra.

```text
(D)   T̄ is MF   =>   T is MF.
```

By `lifted-thompson-t-twist-set-is-trivial-or-the-circle`, the following
are equivalent to (D).

- **(D1) Existential eigencorner.**  Suppose some corona representation `rho`
  of `T̄` has `rho(z) != 1`.  Then *some* corona representation `rho'`
  (possibly different from `rho`) has a nonzero projection
  `P in rho'(T̄)' ∩ Q` and `lambda != 1` with `rho'(z) P = lambda P`.
- **(D2) One chosen scalar twist.**  Fix any `mu in S^1 \ {1}`, for
  example `mu = -1`, or `mu = e^(2 pi i theta)` with `theta` irrational.
  If `T̄` is MF, then some corona representation `sigma` of `T̄` has
  `sigma(z) = mu 1`.  The choice of `mu` does not matter.
- **(D3) Spectral to scalar.**  `S = S^1` implies `Sigma = S^1`.

**Why these are equivalent.**
- (D) ⟺ (D3): items 2 and 3 of the twist-set node.
- (D1) ⟹ (D3): apply the corner device to the eigencorner, which gives
  `lambda in Sigma \ {1}`.
- (D3) ⟹ (D2) ⟹ (D1): trivial, with `P = 1`.

## Position in the graph

- **Exact decomposition of the flagship.**
  `lifted-thompson-t-is-not-mf <=> thompson-t-has-full-mf-radical AND (D)`.
  The reverse direction is the route
  `lifted-thompson-t-not-mf-via-mf-descent`.  For the forward direction:
  a full `T̄` has full quotient `T` (item 3 of
  `lifted-thompson-t-mf-radical-dichotomy`), and (D) then holds vacuously.
- **(D) is the weakest possible second conjunct.**  (D) is equivalent to
  "`thompson-t-has-full-mf-radical` implies `lifted-thompson-t-is-not-mf`".
  Any statement `X` with
  `flagship <=> thompson-t-has-full-mf-radical AND X` must therefore imply
  (D) in the presence of that conjunct.
  - In particular `lifted-thompson-t-centre-has-commutant-eigencorners`
    implies (D), by route
    `lifted-thompson-t-mf-descent-via-central-eigencorners`.
  - (D) holds unconditionally whenever `T` is MF, while (EC) is then still
    open.  So (D) is at most as strong as (EC), and strictly weaker as far
    as is known.
- **Where (D) fails.**  (D) fails in exactly one world: `T` has full
  radical and `T̄` is MF.  In that world:
  - every corona representation of `T̄` has `rho(z)` with no scalar
    corners of any kind;
  - `sp(rho(z)) \ {1}` has no degenerate components (see the w16 attempt on
    `lifted-thompson-t-centre-has-commutant-eigencorners`);
  - nevertheless every point of `S^1` is a spectral value of some `rho(z)`
    (item 3 of the twist-set node).
- **What a proof has to do.**  Start from one representation `rho` moving
  `z`.  Using any operations on corona representations, produce one
  representation with an exact eigencorner of `z` away from `1`.  The
  operations need not stay inside `rho(T̄)' ∩ Q`.  Examples: tensor powers,
  conjugates, subsequences, diagonal limits, precomposition with the
  dilation `lambda` or with the endomorphisms `lambda_n`, and cutting down by
  spectral projections of `rho(t_j)` in the image of `lambda^j`.  A
  single-representation obstruction of the kind recorded for (EC) (arc
  spectrum, no projections in `C^*(rho(z))`) does not block this.

## Attempts

- **2026-09-20, swarm-0917-w21-w21-ptm-follow (stability-approximation).**
  The goal was to reduce (D) to an approximate statement using a Zassenhaus
  commutator gap. The result is recorded as the ESTABLISHED node
  `lifted-thompson-t-central-displacement-gap`.
  - **Gap.** `T̄` is finitely generated and perfect. So every homomorphism into
    the unitary group of any unital C\*-algebra satisfies
    `max_i ||sigma(s_i) - 1|| ∈ {0} ∪ [delta, 2]`, for one fixed `delta > 0`.
  - **First conjunct.** A diagonal limit then shows that "`T` full" is
    equivalent to "the set `N` of corona displacements `||rho(z) - 1||` omits
    some interval `(0, eta)`".
  - **Reduction of (D).** Combined with the conjugate tensor square, whose
    displacement is at most `diam sp(rho(z))`, this gives
    (D) ⟺ **(Small)** ⟺ **(Arc)**.
    - **(Small)** says that if some `rho` moves `z`, then there are
      displacements arbitrarily close to `0` but nonzero.
    - **(Arc)** says that if `T̄` is MF, then for every `eps` some `rho` has
      `rho(z) != 1` with `sp(rho(z))` in an arc of length `eps`.
    - Neither form needs an exact scalar or a commutant projection.
  - **Failure world.** In the failure world, every commutant corner (for `z`,
    and for each `t_j` over `lambda^j T̄`) on which `rho` is nontrivial has
    `z`-spectrum of diameter at least `eta`.
  - **Class kill.** Every homomorphism of `T̄` into `U(C(Y, D))`, with `Y`
    connected and one scalar fibre, is trivial. This covers cones and
    suspensions, and in particular the O_2-suspension mechanism.
  - **Where it stops.** Producing representations with small nonzero central
    displacement, or with short-arc spectrum, from one representation that
    moves `z` is open. The conjugate tensor square only shrinks displacement
    down to `diam sp(rho(z))`. By item 5 of the new node, corners and
    precomposition with `lambda^j` cannot bring that diameter below `eta` in
    the failure world. So the step needs a genuinely new operation, for
    example one that uses the endomorphisms `lambda_n` or the
    rotation-centralizer quotients.
