---
rg: 2
id: bs12-separated-doubling-spectra-correct-conjugators-unpadded
kind: claim
title: If the base unitary has a gamma-separated squaring-invariant spectrum, an eta-approximate BS(1,2) conjugator is within 7 eta/gamma of an exact one, with no padding and the base unitary kept fixed, and the ratio eta/gamma is sharp
distinct_from:
  bs12-trivially-padded-opnorm-correction: that is the open uniform statement; this settles its conjugator half, with k=0, on the regime eta << gamma and shows that outside it the base unitary must move.
  bs1n-rq-padded-opnorm-stability: that is Willett's stable uniqueness with finite-quotient padding; here there is no padding.
---

**ESTABLISHED** by `bs12-separated-doubling-spectra-unpadded-correction-proof`
(lane proof, swarm-0917-w12, not reviewed; elementary, no priority claimed).

## Statement

Let `B'` be a unitary on a Hilbert space with finite spectrum `Y` such that

- `y^2 in Y` for every `y in Y` (squaring invariance), and
- `|y - z| >= gamma` for all `y != z` in `Y` (chordal separation).

Let `A` be a unitary with `||A B' A^* - B'^2|| <= eta`, and put
`g = min(gamma, 1)`.  If `7 eta < 2 g`, there is a unitary `C` with

```text
C B' C^* = B'^2      exactly,      ||C - A|| <= 7 eta / g.
```

`C` is the polar part of the pinching `A' = sum_y Q_y A P_y`, where
`P_y = E_(B')({y})` and `Q_y = E_(B'^2)({y})`.  The constant comes from the
Wiener-algebra norm of a truncated Cauchy kernel, `||psi_gamma||_A <=
1/2 + 2.33/gamma` (numerically `gamma ||psi_gamma||_A -> 1.576`, about
`pi/2`).

**Sharpness of the ratio.**  For odd `N`, let `D = diag(w^j)` with
`w = e^(2 pi i/N)`, `V` the cyclic shift, `W e_j = e_(hj)` with `h = 2^(-1)
mod N`, and `A_s = W exp(is(V+V^*))`.  Then `gamma = |w-1|`,
`eta <= 2 s gamma`, and every unitary `C` with `C D C^* = D^2` satisfies
`||C - A_s|| >= |J_1(2s)|/2 - sum_(m >= N-1) |J_m(2s)|`, which tends to
`|J_1(2s)|/2`, about `s/2`, as `N` grows.  So a fixed-base correction is
`Theta(eta/gamma)` and no better.

## Consequences for `(TPC)`

1. **Bounded period.**  Combine the statement with the spectral half of
   `bs12-trivially-padded-opnorm-correction`.  If every shadowed eigenvalue has
   doubling period at most `L`, then `Y` lies in the rationals with
   denominators `2^m - 1`, `m <= L`, and is `4/(2^L - 1)^2`-separated.  So
   `(TPC)` holds with `k = 0` and `epsilon = O(4^L delta)` on such pairs.
2. **The hard core.**  A counterexample to `(TPC)` (or to Eilers--Shulman--
   Sorensen Q3) must have shadowed spectrum with separation `o(1)` relative to
   `delta/epsilon`, that is, long periodic orbits.  On it the base unitary has
   to move.  The Fourier-twisted pairs `(A_s, D)` show that this regime is
   reached with bounded `s`.  There `delta = O(s/N) -> 0`, and every correction
   keeping `B' = D` stays `~ s/2` away.
3. **Clean split of the conjugator half.**  The conjugator half is exactly
   `eta/gamma`-controlled.  What stays open is a *base-moving* correction.  For
   long cycles this is the site-removal problem named by the w11 lane node
   bs12-identity-padding-inert-off-doubling-fixed-point, which is not yet
   landed.  That node removes an identity padding from a correction that
   already exists, when 1 is not in the spectrum.  This node constructs the
   correction itself when the spectrum is separated, and needs no gap at 1.
