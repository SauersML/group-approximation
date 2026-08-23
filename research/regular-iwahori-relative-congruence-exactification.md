---
rg: 2
id: regular-iwahori-relative-congruence-exactification
kind: claim
title: Regular Iwahori pairs are relatively congruence-exactifiable
distinct_from:
  odd-label-stabilization-has-uniform-repair: that completes repair of an already congruence mixed-CRT pair; this asks to move an arbitrary exact modular-vertex pair into that locus before applying the repair.
  iwahori-outlier-repair: that asks directly for a full-rank compatible correction in the localized sector; this isolates a stronger but sharply arithmetic preprocessing theorem sufficient for it.
  character-rigidity-equals-hyperfinite-hs-stability: that controls hyperfinite character sectors and finite-quotient approximability in a weak sense; this asks for generatorwise normalized-HS proximity to congruence vertex representations.
---

Let `pi_(n,+),pi_(n,-):SL_2(Z)->U(d_n)` be exact vertex
representations with Iwahori defect tending to zero.  Suppose the compatible
homomorphism of `SL_2(Z[1/2])` induced in the matrix ultraproduct has the
regular trace.  Then there are exact, same-dimensional vertex
representations `rho_(n,+),rho_(n,-)`, each factoring through a congruence
quotient, such that

```text
d_2(pi_(n,+),rho_(n,+))+d_2(pi_(n,-),rho_(n,-)) -> 0,   (RCE1)
def(rho_(n,+),rho_(n,-)) -> 0.                          (RCE2)
```

This is the sharp arithmetic theorem still missing after exact congruence
repair.  It is deliberately a *relative* statement: the inputs are already
honest representations of each modular vertex, and only their gluing is
asymptotic.  It asserts neither HS stability of arbitrary approximate
`SL_2(Z)` representations nor a classification of all its finite-dimensional
representations.

The claim is open.  Regular trace alone is insufficient to prove it by
spectral bookkeeping, because
`residual-finite-tensor-camouflages-iwahori-transfer-failures` makes any
tensor-stable edge geometry regular-tracial.  Property `(tau)` supplies the
uniform polar/repair estimate only after `(RCE1)` has placed the vertices in
congruence quotients.  It does not establish `(RCE1)`.

## Attempts

- **Central-regular localization.**
  `iwahori-outlier-localization` reduces a failed sequence to collapsing
  mixed gaps between high-dimensional edge irreducibles.  It removes sparse
  arbitrary operator spaces but retains only extension through `SL_2(Z)`;
  `modular-vertex-extension-does-not-force-congruence` shows why this stops
  short of `(RCE1)`.
- **Character rigidity and canonical trace.**  Peterson--Thom rigidity and
  Dogon--Vigdorovich hyperfinite stability handle the
  finite-character/hyperfinite sectors, but do not give generatorwise
  proximity to a finite quotient in the regular sector.  The tensor theorem
  `residual-finite-tensor-camouflages-iwahori-transfer-failures` makes this
  failure sharp: canonical trace can be imposed without changing the edge
  obstruction.
- **Selberg `(tau)`.**  The uniform congruence spectral gap powers polar and
  rank repair after exactification.  Applying it before `(RCE1)` is circular,
  because an arbitrary modular representation has no congruence quotient
  action on which to average.
- **Alternative direct route.**  `skeleton-relative-hs-stability-for-sl2`
  tries to bypass congruence exactification by repairing an exact parabolic
  skeleton and its Weyl holonomy.  It is a route to the same Iwahori endpoint,
  not an established implication to `(RCE1)`.
- **Exact endpoint classification does not give basin capture.**
  `finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence` proves
  directly from `huh^(-1)=u^4`, the S-arithmetic normal-subgroup theorem and
  Serre CSP that every honest finite-dimensional endpoint has finite image
  and odd congruence level. An asymptotically compatible vertex pair gives
  such an endpoint only in a matrix ultraproduct. On its finite-character
  central part, hyperfinite stability already supplies coordinatewise
  congruence correction; on its regular central part, exact endpoint
  classification has no lifting implication. Thus `(RCE1)` is precisely the
  regular-face basin-capture theorem, not a missing representation-
  classification lemma.
- **Moving root coefficients survive regular tensor camouflage.**
  Pure regular congruence packets satisfy an exact opposite-root `L^2`
  tensor isometry. This does not pass uniformly to conductor-dependent
  gauges in a central-regular sequence. By
  `regular-tensor-camouflage-preserves-moving-root-failures`, raising the
  amplified root to the order of the regular quotient cancels that quotient
  factor and recovers the original payload operator tensored with identity.
  Hence every tensor-stable moving-coefficient obstruction survives with
  unchanged norm after canonicalization. Opposite-root orthogonality can
  close `(RCE1)` only after a theorem forces gauges into the authenticated
  congruence root algebra; it cannot itself provide that authentication.
- **Same-core gauge coercivity makes the authentication boundary exact.**
  After a congruence endpoint `(X_0,R_0,S_0)` has been authenticated and the
  repaired tuple has relative form `X=cX_0` with `[c,S_0]=0`,
  `same-core-involution-cubic-gauge-coercivity` globally forces

  ```text
  ||c-1||_2 <= ||X^2-1||_2+||(XS_0^2)^3-1||_2.
  ```

  Thus `(RCE1)` does not additionally require a spectral gap for the
  root-commutant gauge.  What it must supply is precisely the antecedent:
  a nearby exact moving congruence atom, a common exact extender `X_0`, and
  alignment of the input gauge into the commutant of the same `S_0`.
  Regular trace, opposite-root orthogonality, and endpoint classification
  do not presently authenticate those data.
- **The half-parabolic branch no longer has to be authenticated separately.**
  `fourth-power-covariance-unfolds-square-root-branches` proves that two
  exact BS cores satisfy

  ```text
  ||S-S'||_2<=2||S^2-S'^2||_2+2||R-R'||_2.
  ```

  Thus an endpoint decoder only has to align the congruence atom in the
  coordinates `(R,S^2)`; the original half-parabolic root then follows with
  a dimension-free linear bound.  This is genuinely stronger than choosing
  the canonical odd root by an exponent depending on its conductor.  The
  Hadamard firewall to independent first-triangle rounding is fully charged
  by the missing `R` alignment: on that packet `S^2` moves by `O(1/p)` but
  `R` must move by asymptotically at least `1/2`.  The remaining theorem is
  therefore simultaneous `R`/first-parabolic endpoint authentication, not
  root-branch selection after authentication.
- **Qualitative ultraproduct lifting is equivalent to the whole regular
  stability endpoint.**
  `regular-iwahori-exactification-is-regular-branch-liftability` proves that
  this claim is equivalent, using the already established modular-vertex
  exactification, odd-congruence repair and finite-dimensional endpoint
  classification, to same-dimensional correction of every regular
  microstate of `SL_2(Z[1/2])`.  Thus passing to an exact regular
  ultraproduct homomorphism does not weaken the missing theorem.  The two
  vertex restrictions always lift exactly; lifting their common Iwahori
  incidence is the entire problem.
