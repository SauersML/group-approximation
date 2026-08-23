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
- **The square-free presentation removes the entire root-choice stage.**
  `iwahori-square-free-bs14-presentation` replaces `S` by `T=S^2` and
  recovers it by the fixed word `S=R^(-1)T^2R`.  The five relations are

  ```text
  R T R^(-1)=T^4,  X^2=1,  X R X=R^(-1),
  (XT)^3=1,         (XT^2R)^3=1.
  ```

  The word substitutions preserve vanishing normalized-HS defect with
  dimension-independent constants.  Moreover
  `fourth-power-covariance-unfolds-square-root-branches` gives

  ```text
  ||S-S'||_2<=2||T-T'||_2+2||R-R'||_2,
  ```

  so the coordinate change is quantitatively bi-Lipschitz on exact cores.
  The Hadamard firewall is fully charged by the omitted `R` coordinate: its
  `T` displacement is `O(1/p)` but its `R` displacement tends to at least
  `1/2`.  The remaining basin theorem must align `(R,T)` jointly; no
  square-root path lifting or conductor-dependent odd-root choice remains.
- **The finite torsion frame can be made exact before basin capture.**
  `iwahori-two-triangle-torsion-normal-form` changes `(R,T)` by a universal
  linear multiple of the two cubic defects so that `X^2`, `(XT)^3`, and
  `(XT^2R)^3` all hold exactly.  Only inversion and fourth-power covariance
  remain approximate.  Thus a qualitative lifting/semiprojectivity attack
  has been reduced to two fixed structural words over an exact
  `C_2*C_3*C_3` representation; exact endpoint classification and spectral
  rounding have no further role before those two words are synchronized.
- **The two structural rows neither decouple nor satisfy classical small
  cancellation.**
  `iwahori-torsion-frame-relators-have-a-half-piece` computes the inversion
  and covariance words in `C_2*C_3*C_3`.  They have lengths ten and twelve,
  but a cyclic conjugate of the former and the latter share a length-five
  piece.  They therefore fail `C'(1/2)` (hence `C'(1/6)`), and two explicit
  quotient maps show that neither row follows from the other plus the
  torsion frame.  Basin capture cannot be reduced to a one-relator theorem
  or a classical free-product small-cancellation estimate; it must use a
  genuinely joint analytic/flexible mechanism.
- **Same-core gauge coercivity makes the terminal boundary exact.**  Once a
  congruence endpoint `(X_0,R_0,T_0)` has been authenticated on the same
  square-free core, put `c=XX_0`.  The involution and inversion rows give

  ```text
  ||[c,R_0]||_2
  <=||X^2-1||_2+||XR_0X-R_0^(-1)||_2.
  ```

  If the joint authentication promotes this automatically `R_0`-central
  gauge into `{T_0}'`, `same-core-involution-cubic-gauge-coercivity` gives

  ```text
  ||c-1||_2<=||X^2-1||_2+||(XT_0)^3-1||_2.
  ```

  Thus after an endpoint is found there is no spectral-gap, root-selection,
  or nonlinear Koopman problem **provided the endpoint was selected in the
  correct component**.  The distinction is forced by
  `p3-exact-iwahori-endpoints-refute-arbitrary-baseline-alignment`: over one
  exact mod-three core there are two exact endpoints whose relative gauge is
  `R_0`-central but not `T_0`-central, despite both cubics having zero
  defect.  Hence the terminal operation is not promotion relative to an
  arbitrary canonical endpoint.  Basin capture must jointly choose a nearby
  congruence endpoint (or minimize over its exact endpoint fiber), after
  which same-core coercivity applies.
  This exact ambiguity is field-locally exceptional:
  `prime-field-iwahori-weyl-endpoint-is-unique-away-from-three` proves that
  the standard endpoint in `PSL_2(k)` is unique for `char(k)>3` already from
  inversion and the first cubic.  The arbitrary-baseline counterexample is
  enabled by `h(2)=1` in `PSL_2(F_3)`.  This removes a putative generic
  finite-field Weyl ambiguity, but does not control multiplicity commutants,
  higher congruence rings, or the regular moving-level basin.
  The arithmetic label statement now extends through every depth:
  `prime-power-iwahori-weyl-endpoint-is-unique-away-from-three` proves
  uniqueness in `PSL_2(Z/p^kZ)` for all `p>3`.  But
  `congruence-iwahori-endpoint-fiber-contains-core-commutant-orbits` gives
  the exact surviving obstruction: in a regular congruence representation,
  conjugation by any unitary in `{R,T}'` fixes the core and moves the Weyl
  endpoint, and the relative gauge between two such endpoints need not
  commute with `T`.  Thus the open basin theorem is now localized to
  selecting/synchronizing these multiplicity-commutant orbits across moving
  levels; it is not missing any prime-power Weyl-element classification.
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
