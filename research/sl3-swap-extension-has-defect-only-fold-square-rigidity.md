---
rg: 2
id: sl3-swap-extension-has-defect-only-fold-square-rigidity
kind: claim
title: Approximate SL3 swap extensions have defect-only fold-square rigidity
distinct_from:
  projective-trace-square-transfer-for-sl3-pair: that controls the full projective commutator of every auxiliary unitary against `h`; this asks only that one balanced swap involution acquire commuting principal-angle charts, and concludes only that the square of its fold commutator is near one.
  commuting-conjugate-involution-transfer-for-sl3-pair: that explicitly assumes the native relation `[s,hsh^(-1)]=1` and asks the commuting overlap to select an endpoint; the present swap extension has no such relator and asks the arithmetic amalgamating relations to force this commutation approximately.
  sl3-regular-arithmetic-double-fold-mark-collapse: that concludes scalar collapse of the original adjacent-vertex fold word on canonical microstates; this asks only for a defect-only second-moment relation in the finite swap extension.
  canonical-arithmetic-swap-fold-gram-is-arcsine: that proves every hypothetical canonical sequence has fold-Gram defect tending to `1/16`; the present open claim would force the same defect to zero and thereby exclude those sequences.
  exact-fd-invisibility-has-no-general-hs-robustification: that gives a nonarithmetic sofic group where an exactly invisible word survives in normalized-HS microstates; the present claim asks for an SL3-specific robustification of one explicit fold-square word.
---

**OPEN DEFECT-ONLY MIXED TERMINAL.**  Fix a finite presentation of

```text
E=<SL_3(Z[1/2]),s | s^2=1, [s,SL_3(Z)]=1>
```

and write `h=diag(2,1,1/2)`.  There is a modulus `eta(delta)->0` such that
for every finite-dimensional unitary assignment of presentation defect at
most `delta`, after changing the assigned `s` by `O(delta)` to an exact
self-adjoint involution `S`, the projections

```text
P=(I-S)/2,                 Q=rho(h)P rho(h)^*
```

satisfy

```text
tr(QPQ-(QPQ)^2)
 =(1/2)||[P,Q]||_2^2
 =(1/16)(1-Re tr((rho(h)S rho(h)^*S)^2))
 =(1/32)||(rho(h)S rho(h)^*S)^2-I||_2^2
 <=eta(delta).                                               (SFS1)
```

The zero-defect case is known: every exact finite-dimensional
representation of the arithmetic double folds, so `S` commutes with all of
`A` and the left side vanishes.  The claim is precisely its normalized-HS
robustification at the weakest second-moment level.  It neither asks that
`P=Q` nor controls the first fold trace.

If `T=rho(h)S rho(h)^*`, then `T,S` are involutions and
`(TS)^2=[T,S]`.  Hence `(SFS1)` is equivalently the robust finite-dimensional
invisibility of the single explicit word

```text
[hsh^(-1),s]
```

in the arithmetic swap extension.  Exact finite-dimensional invisibility
alone cannot imply such a bound for a general finitely presented group; the
remaining content must be specifically arithmetic.

Combined with `canonical-arithmetic-swap-fold-gram-is-arcsine`, `(SFS1)`
excludes canonical microstates of `E`, since those force the same left side
to `1/16`.  Thus it already establishes an explicit non-hyperlinear group.

## Attempts and surviving scope

- Exact finite-dimensional representations satisfy `(SFS1)` with zero
  constant by arithmetic co-density and
  `sl3-arithmetic-double-finite-representations-fold`.
- If either arithmetic vertex of the corresponding double is uniformly near
  an exact representation, the established one-near-vertex correction
  cascade makes both vertices jointly near exact and forces `(SFS1)`.  Every
  enemy is therefore in the simultaneous two-outlier sector.
- Positive-cross-Gram rounding supplies no estimate: `G=PQ` has exact packet
  covariance for every `P,Q`.  In a canonical enemy its Gram law is forced
  to be half-arcsine and its left side is exactly asymptotic to `1/16`.
- The exact local identity `(ASR3)` shows that there is no softer spectral
  interpolation left.  A proof must charge the **second fold word** to the
  finite arithmetic presentation, equivalently authenticate an
  original-coordinate polar half-return across the whole principal-angle
  spectrum.
- The claim is not a dimension-blind tracial consequence of the arithmetic
  actor relations: the coset Bernoulli swap model has the same interior
  profile.  Any proof must use finite matrix coordinates or normalized-HS
  correction.
- If the building vertex action `A curvearrowright A/C` is sofic, halo/free-
  wreath permanence makes the binary swap extension sofic and supplies
  canonical permutation microstates with the half-arcsine Gram law.  Those
  models refute `(SFS1)`.  Thus the defect-only word estimate would also
  prove nonsoficity of this explicit nonamenable-stabilizer action; ordinary
  sofic-action approximation cannot be used to prove it.

- **Linearizing the fold word against a Fox Jacobian cannot support the
  estimate.**  A first-order coercivity test — perturb an exact representation
  by `rho(g)exp(i X_g)`, quotient the infinitesimal conjugation and exact
  correction directions, and compare the derivative of the fold word against
  the linearized relator operator — is valid only in a neighbourhood of the
  exact locus.  But `canonical-arithmetic-swap-fold-gram-is-arcsine` puts
  `tr(QPQ-(QPQ)^2)` at `1/16-o(1)` on exactly the microstates `(SFS1)` has to
  control, while every exact finite-dimensional representation gives `0`, and
  that quantity is norm-continuous in the assignment.  So those microstates sit
  at a fixed positive normalized-HS distance from the exact locus and no
  neighbourhood estimate reaches them.  A linearized computation can still be
  run as a *diagnostic* — rapid degeneration of the smallest singular value
  would be evidence against any local coercivity mechanism — but a positive
  answer would carry no weight toward `(SFS1)`.
