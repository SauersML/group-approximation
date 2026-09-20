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
