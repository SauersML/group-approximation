---
rg: 2
id: lifted-thompson-t-not-mf-via-central-eigencorners
kind: route
title: The flagship's single hole is exactly "T is not MF" plus one commutant eigencorner for the central translation
target: lifted-thompson-t-is-not-mf
requires:
  - thompson-t-has-full-mf-radical
  - lifted-thompson-t-centre-has-commutant-eigencorners
  - central-eigencorners-die-over-full-radical-quotients
  - lifted-thompson-t-perfect-centre-cubically-elliptic
---

**Proof.**  Let `rho : T̄ -> U(Q)` be a corona representation.  Suppose, for
a contradiction, that `rho(z) != 1`.
1. By `lifted-thompson-t-centre-has-commutant-eigencorners` there are a
   nonzero projection `P in rho(T̄)' ∩ Q` and `lambda != 1` with
   `rho(z) P = lambda P`.
2. Apply item 1 of `central-eigencorners-die-over-full-radical-quotients`
   with `G = T̄` and `c = z`.  Its hypotheses hold:
   - `T̄` is perfect, by item 2 of
     `lifted-thompson-t-perfect-centre-cubically-elliptic`;
   - `z` is central;
   - `T̄/<z> = T` has full radical, by `thompson-t-has-full-mf-radical`.

   So `lambda = 1`, a contradiction.

Hence `rho(z) = 1` for every corona representation, that is,
`z in Rad_MF(T̄)`. ∎

## The decomposition is exact

The converse also holds, so this route loses nothing:

```text
lifted-thompson-t-is-not-mf
   <=>  thompson-t-has-full-mf-radical  AND  lifted-thompson-t-centre-has-commutant-eigencorners
```

- `=>` (first conjunct).  Item 3 of `lifted-thompson-t-mf-radical-dichotomy`.
- `=>` (second conjunct).  If `rho(z) = 1` for every `rho`, the hypothesis of
  (EC) is never met.
- `<=`.  This route.

The two prerequisites can fail independently, and they fail in different
places.
- `thompson-t-has-full-mf-radical` is refuted by an MF model of `T`.  By item
  4 of `central-eigencorners-die-over-full-radical-quotients`, equivalently by
  an MF model of a single rotation centralizer `C_T(r_k)`.  This is a
  statement about a finitely presented simple group with trivial centre.
  Nothing central is involved.
- `lifted-thompson-t-centre-has-commutant-eigencorners` is refuted by a corona
  representation of `T̄` in which `rho(z) != 1` has spectrum perfect away from
  `1` and has no exact eigencorner in the relative commutant.  This is the
  fibre problem already recorded in `full-mf-radical-abelianized-cover-is-not-mf`
  ("the fibres `B/(pi(z) - mu)` are arbitrary quotients").  It is now pinned
  to a single group and a single central unitary.

## What this route changes

- **The torsion-free seed costs, beyond the Leavitt side, only (EC).**  Via
  `thompson-v-not-mf-via-thompson-t`, the Thompson-`T` conjunct alone already
  gives the binary-Leavitt endpoint.  So the flagship
  `property-t-free-manuscript-results` now reads
  "`T` is not MF, plus (EC) for `(T̄, z)`".  The second conjunct is exactly
  the part that makes a torsion-free seed harder than a torsion seed.  This
  matches the recorded obstruction `virtually-torsion-free-residual-kills-radical-calculus`,
  which says formal calculus cannot supply a torsion-free seed.  (EC) is not
  formal.
- **Central extensions of torsion seeds are not the obstruction.**  Item 2 of
  `central-eigencorners-die-over-full-radical-quotients` shows that a
  perfect finite central extension of a full-radical group is automatically
  full.  So the only thing lost in passing from `C_T(r_k)` (torsion centre) to
  `T̄` (torsion-free centre) is the existence of spectral projections.  That
  is exactly the conjunct (EC).
- **Named failure step for the tensor-corner class.**  Every argument of the
  form "cut to a central eigencorner, tensor with the conjugate, descend to
  the central quotient" dies for torsion-free centres at step 1 above, and
  nowhere else.
