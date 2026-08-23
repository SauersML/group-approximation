---
rg: 2
id: bs14-relative-involution-extension-stability
kind: claim
title: An almost Iwahori involution over an exact BS(1,4) core can be repaired with a dimension-free modulus
distinct_from:
  iwahori-outlier-repair: that is formulated through low-energy edge intertwiners for two modular vertices; this is the equivalent relative one-involution problem after the amenable BS(1,4) core has been repaired.
  iwahori-newton-closes-near-sector: that handles a fixed torsion-multiplicity tube by differential rigidity; this asks for a global packetwise repair over arbitrary periodic BS cycle packets.
  bs14-unitary-representations-are-periodic-cycle-packets: that classifies the exact core; this is the open uniform repair theorem for the remaining involution.
---

OPEN.  Let `R,S in U(d)` be an exact representation of `BS(1,4)`,

```text
R S R^(-1)=S^4,
```

and let `X in U(d)` satisfy, with normalized-HS error at most `epsilon`,

```text
X^2=1,
X R X=R^(-1),
(X S^2)^3=1,
(X R S)^3=1.                                         (BRI1)
```

Prove that `(X,R,S)` is within `f(epsilon)` (allowing only `o(d)` flexible
padding if required) of an exact solution, for one modulus `f(epsilon)->0`
independent of `d`, the periodic orbit lengths, and the multiplicity
monodromies in
`bs14-unitary-representations-are-periodic-cycle-packets`.

The exact core decomposes into fourth-power cycle packets.  After
diagonalizing each return monodromy as in
`bs14-unitary-representations-are-periodic-cycle-packets`, every irreducible
packet is multiplicity one and has a scalar return phase `v in T`.  The
relation `X R X=R^(-1)` pairs the `R`-spectral data, hence the scalar phases
`v` and `v^(-1)`, while the two cubic equations require the same `X` to
extend both modular triangles.  The load-bearing content is simultaneous
scalar-packet matching: repairing either cubic equation separately, or
matching only the scalar spectrum of `S`, need not produce one common
involution.

The sharp quantitative version of the missing global step is isolated as
`bs14-flexible-cross-packet-boundary-reconciliation`: the unnormalized
Frobenius energy of the two cubic residuals should pay the rank of one
globally balanced added multiplicity vector.  This explicitly permits
off-diagonal coupling between heterogeneous packets and records the desired
quadratic padding law.  The determinant-neutral `p=1 mod 8` canonical blocks
are now charged by the explicit first-cubic spectrum, but arbitrary phase
mixtures remain outside the authenticated calculation.

## Equivalent half-root-free form

The variable called `S` above was inherited from the square-root
presentation.  `iwahori-square-free-bs14-presentation` shows that one may
instead set `T=S^2` and eliminate `S=R^(-1)T^2R` exactly.  The core `(R,T)`
again satisfies `RTR^(-1)=T^4`, and the relative equations become

```text
X^2=1,       X R X=R^(-1),
(X T)^3=1,   (X T^2 R)^3=1.                           (BRI2)
```

This is an equivalent formulation, not an additional hypothesis.  It
should be used for endpoint authentication: the odd square-root branch is
absent, and the terminal same-core estimate applies directly to gauges
commuting with `T`.  The surviving issue is to authenticate the exact
congruence `(R,T)` core and align the extending involution.

## Attempts

- **Both triangle rows exactify in one common square-free tuple.**
  `iwahori-two-triangle-torsion-normal-form` first rounds `A=XT` to order
  three and sets `T_1=XA_0`; it then rounds
  `B_1=XT_1^2R` to order three and sets `R_1=T_1^(-2)XB_0`.  The
  perturbation and the two surviving defects are bounded linearly by the
  original five defects, uniformly in dimension.  Hence every enemy may be
  normalized so that

  ```text
  X^2=1,       (XT)^3=1,       (XT^2R)^3=1
  ```

  hold exactly and only `XRX=R^(-1)` and `RTR^(-1)=T^4` remain approximate.
  Equivalently, all finite-order lifting is discharged inside the exact
  `C_2*C_3*C_3` torsion frame.  The basin problem is now precisely the
  simultaneous two-structural-word quotient lift; separately rounding more
  torsion relations cannot improve it.

- **Exact torsion does not permit strict structural rounding.**
  `exact-torsion-frame-has-rank-one-strict-counterpackets` applies that
  normalization to the compressed even Weil family.  In
  `F=C_2*C_3*C_3`, the two residual words are explicitly

  ```text
  X A^2 X A^2 B X A^2 X A^2 B,
  A^2 X A^2 B X A B^2 X A^2 X A^2 X.
  ```

  Their defects are `O(p^(-1/2))`, while the exact torsion-frame tuple stays
  uniformly far from every exact quotient representation of the same
  dimension.  One added Weil fixed line repairs it.  Hence no global
  same-dimensional SOS/error-bound argument on the torsion-frame variety can
  close this claim; a successful theorem must spend flexible boundary rank.

- **The square-root firewall is bypassed by retaining the actual BS
  coordinates.**  Independent first-triangle rounding really does fail:
  `relative-first-triangle-rounding-has-an-odd-root-branch-firewall`
  Hadamard-rotates nearly antipodal `S` eigenspaces, moving `S^2` by
  `O(1/p)` while every root of the rounded product stays distance tending to
  one from `S`.  But `iwahori-square-free-bs14-presentation` makes that
  operation unnecessary.  With `T=S^2`,

  ```text
  S=R^(-1)T^2R,
  R T R^(-1)=T^4,  X^2=1,  X R X=R^(-1),
  (XT)^3=1,         (XT^2R)^3=1.
  ```

  The word substitutions preserve vanishing HS defect with fixed linear
  constants.  Quantitatively,
  `fourth-power-covariance-unfolds-square-root-branches` gives

  ```text
  ||S-S'||_2<=2||T-T'||_2+2||R-R'||_2.
  ```

  Hence the wrong Hadamard branch pays `R` displacement tending to at least
  `1/2`.  A coupled construction only has to authenticate `(R,T)` and `X`;
  it never chooses a root.

- **Strict repair fails, and one-dimensional flexible repair is sharp.**
  `even-weil-fixed-line-compression` removes the one `R,S`-invariant fixed
  line from the even Weil representation for every prime `p=1 mod 4` and
  polar-rounds the compressed involution.  The BS core remains exact, all
  four remaining relators have defect `O(p^(-1/2))`, but no exact extension
  exists in dimension `(p-1)/2`.  Adding back one dimension gives an exact
  model.  Property `(T;FD)` upgrades the algebraic nonextension to uniform
  distance from every exact same-dimensional representation: otherwise,
  after adjoining one trivial line, two exact equal-dimensional
  representations would violate the `(T;FD)` intertwiner gap.  Thus strict
  stability fails but the flexible claim survives.
  The sharpened boundary calculation shows more: polar rounding leaves
  `X^2=1` and `XRX=R^(-1)` exactly.  The compressed operator has one deficient
  singular value `p^(-1/2)`, and correcting it preserves the dihedral
  relation.  Thus this canonical obstruction is carried entirely by the two
  cubic constraints.  A proof cannot charge the necessary padding to
  approximate inversion of `R`; it must recover the boundary rank from the
  simultaneous defects of `(XS^2)^3` and `(XRS)^3`.
  The quantitative consequence is isolated as
  `bs14-two-cubic-strict-repair-constants-diverge`: even with the BS core,
  involution, and inversion relation exact, every level-`p` linear strict
  repair constant is at least `c sqrt(p)` (and every Holder constant of
  exponent `theta` is at least `c_theta p^(theta/2)`).  Thus no strict
  orbitwise spectral-matching theorem can be uniform; the remaining claim is
  necessarily the flexible cross-packet reconciliation statement.
  A normalization caveat is load-bearing: the current rank-one compression
  proof gives only an `O(p^(-1/2))` **upper** bound for the maximum cubic
  defect.  Therefore the often-quoted `padding/d=O(defect^2)` sharpness does
  not yet follow from this family.  It additionally requires a lower bound
  `max(cubic defects)>=c p^(-1/2)`, i.e. an explicit statement that one cubic
  word sees the deleted Weil boundary mode without cancellation.
  This missing calculation is now positive on the infinite subsequence
  `p=5 mod 8`: `even-weil-second-cubic-has-a-rank-six-determinant-gap`
  proves that the second cubic has determinant `-1`, rank at most six away
  from the identity, and normalized-HS defect at least `2/sqrt(6d)`.  Hence
  one-dimensional padding is genuinely quadratic in defect there.  The
  determinant-neutral `p=1 mod 8` packets are now covered by
  `deleted-fixed-line-first-cubic-has-explicit-positive-spectrum`, which
  gives a uniform first-cubic Frobenius charge.  Only general cross-packet
  mixtures remain outside the blockwise lower bound.
- **Primitive prime packets are now classified exactly.**
  `prime-bs14-packet-extension-classification` proves that a scalar packet
  extends exactly iff it is the full odd Weil orbit (`p=3 mod 4`,
  `ord_p(4)=(p-1)/2`, `v=1`).  This identifies the exact repair targets, but
  the even-Weil compression shows why exact classification alone cannot
  yield a dimension-free same-dimensional gap.

- **Scalar packets cannot be repaired independently.**  For
  `p=1 mod 4`, the exact even Weil representation restricts on the BS core
  as the direct sum of the trivial fixed line and the primitive nonzero
  packet.  The latter packet has no exact Iwahori extension in its own
  dimension.  Hence the exact Weil involution cannot preserve the two BS
  summands: if it did, its restriction to the nonzero summand would be the
  forbidden exact extension.  Exact repair therefore necessarily uses
  off-diagonal coupling between distinct scalar packets.  After deleting
  the fixed line this coupling has rank at most one, giving defect
  `O(d^(-1/2))`; restoring the line costs relative dimension `1/d`.
  Orthogonal packetwise rounding is thus rigorously ruled out, while a
  global transport that permits boundary mass of order `defect^2` remains
  viable.

- **Core exactification is available.**  The one-solenoid dense-periodic-
  measures theorem gives HS stability of `BS(1,4)`, so the approximate core
  can be repaired before this claim is applied.  This does not control `X`.
- **On the regular face, the exact core is automatically congruence-
  authenticatable.**
  `regular-bs14-cores-align-with-congruence-endpoint-restrictions` uses
  amenability of `BS(1,4)` and slowly growing regular congruence quotients to
  show that every regular exact core is, after conjugacy, `o(1)`-close to the
  restriction of a same-dimensional exact Iwahori endpoint.  This is
  schedule-free and bypasses the moving packet-semigroup charge completely.
  It does not control the supplied `X`: after core alignment, one still has
  to select an exact global endpoint type compatible with the almost
  extender.  Capture by the particular regular endpoint orbit is false:
  `cuspidal-redistribution-refutes-regular-core-orbit-basin` gives exact
  endpoints with the identical regular BS restriction and asymptotically
  regular global characters, but uniformly separated global multiplicity
  types.  Thus the regular obstruction is now an **adaptive endpoint-type
  selection** problem, not core authentication or retraction to one fixed
  orbit.
- **The nonlinear same-core gauge is completely controlled.**  Suppose basin
  capture has produced an exact extender `X_0` over the **same** exact
  parabolic `T=S^2`, and the relative gauge has the commutant form

  ```text
  X=c X_0,                 [c,T]=0.
  ```

  Then `same-core-involution-cubic-gauge-coercivity` gives the global,
  dimension-free estimate

  ```text
  ||c-1||_2 <= ||X^2-1||_2+||(XT)^3-1||_2.
  ```

  Thus arbitrary Fourier modes, sign plateaux, and large operator-norm
  gauges cannot escape after the extending core has been authenticated.
  The remaining hypothesis is strictly earlier: find a nearby exact pair
  `(X_0,R_0,T_0)` and align the repaired input so that its relative gauge
  commutes with that same `T_0`.  Core stability by itself gives only
  `(R_0,T_0)` and does not manufacture or authenticate `X_0`; the inversion
  row and second cubic are still needed for that basin-capture/alignment.
  The word **nearby** is load-bearing:
  `p3-exact-iwahori-endpoints-refute-arbitrary-baseline-alignment` exhibits
  two exact mod-three extenders over one identical core whose relative gauge
  does not commute with `T`.  Therefore one cannot authenticate an arbitrary
  canonical endpoint and expect the second cubic to align every other exact
  endpoint to it.  The flexible repair must select the correct endpoint
  component or optimize over the entire exact endpoint fiber.
  `prime-power-iwahori-weyl-endpoint-is-unique-away-from-three` removes the
  discrete Weyl-label ambiguity at every standard `p^k` level for `p>3`.
  Nevertheless
  `congruence-iwahori-endpoint-fiber-contains-core-commutant-orbits` shows
  that the represented endpoint fiber still contains a full core-commutant
  conjugacy orbit, with exact representatives whose relative gauges are not
  `T`-central.  The remaining flexible reconciliation is therefore exactly
  multiplicity-orbit selection, not scalar group-element matching.
- **The matrix-monodromy obstruction disappears.**  The return unitary is
  diagonalizable, so the core is a sum of scalar-phase packets.  The phase
  coordinate remains essential, but no noncommutative `U(k)` matching
  theorem is needed.
- **Fixed-stratum Newton is insufficient globally.**  It controls packets
  after all torsion multiplicities are fixed.  Small-rank stratum changes
  approach one another in normalized HS as dimension grows and require the
  separate reconciliation step.
- **Finite packet target.**  Refine the core into scalar packets `(O,v)`.
  Express `(BRI1)` as equations on the Hankel coefficients between packets
  whose `R`-spectra are inverse.  A dimension-free transport/matching theorem
  for those scalar packet coefficients, coupled across both cubic
  constraints, would prove the claim.
- **Exact determinant pruning.**
  `iwahori-cycle-packet-determinant-fence` eliminates every scalar packet
  violating `(det R/det S)^3=1`; for prime full quadratic-residue orbits with
  `v=+1`, this already excludes `p=1 mod 4`.  This is only an exact
  classifier.  Determinant defects dilute under normalized-HS amplification,
  so the surviving packet transport still needs a positive-density argument.
