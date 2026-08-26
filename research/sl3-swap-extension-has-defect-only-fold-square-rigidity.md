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
  cascade makes both vertices jointly near exact.  Projective folding then
  gives `|tr(V)|->1` for `V=rho(h)S rho(h)^*S`.  Because `tr(V)` is real for a
  product of involutions,

  ```text
  min_(sigma in {+1,-1}) ||V-sigma I||_2^2=2-2|tr(V)|,
  ```

  so `||V^2-I||_2->0` dimension-independently.  Every enemy is therefore in
  the simultaneous two-outlier sector.
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

- A narrower sufficient terminal is isolated in
  `regular-actor-balanced-swap-has-positive-second-fold-bias`.  On assignments
  whose `A`-restriction already has the regular character and whose swap is
  balanced, it asks only for `liminf Re tr(V^2)>0`, equivalently for the Gram
  defect to stay a fixed amount below `1/16`.  Congruence tensor
  regularization removes its profile restriction, and slowly growing tensor
  powers amplify a fixed positive bias to `Re tr(V^2)->1`.  Hence
  `positive-second-fold-bias-amplifies-to-full-rigidity` proves that this
  apparent weakening is actually equivalent to `(SFS1)`.

- Fixed-depth arithmetic type refinement does not reach that narrower
  terminal.  Every fixed-depth Clifford graph is finite-fiber Folner, and
  spherical quadratures tensor through its Folner windows while preserving a
  nonfolded scalar witness.  This rules out separated arguments using only
  finitely many spherical moments, bounded-depth Clifford cycles, and cross
  commutation.  It is not a countermodel to the full presentation: the first
  surviving input must be a non-tensorial actor/swap incidence on the same
  carrier or depth growing with conductor.

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

- **The new unbalanced torus word does not close the swap terminal by
  itself.**  `unbalanced-torus-and-swap-commutation-do-not-control-fold-square`
  gives an exact `M_2` packet in which `R_tor=1`, the swap commutes with every
  displayed coefficient, both rank-one root-doubling and
  Weyl-word packages are exact, and nevertheless the fold square is `-I`
  (Gram defect `1/8`).  The packet omits the remaining lattice consistency
  making those packages one actor representation, so it is not a full actor
  assignment.  It proves that the next mixed estimate must consume further
  actor relations coupling the coefficients; combined with the bounded-depth
  rank-one fences, a genuine `A_2` relation coupling the branches is the first
  surviving candidate.  The unbalanced word plus the displayed separate
  rank-one consistency does not extract the product-multiplicity coordinate
  used by the established product-sector theorem.

- **The first mixed `A_2` word is still not enough.**
  `one-mixed-a2-word-does-not-control-fold-square` repairs the omitted identity

  ```text
  W_12 E_23 W_12^*=[E_12,E_23]
  ```

  exactly on an internal Pauli qubit while retaining the exact torus, swap,
  and rank-one package in `M_4`.  Its fold has
  `Re tr(V^2)=-1/2` and Gram defect `3/32`.  Consequently the surviving local
  gate needs a second joint chamber relation or a closed rank-two loop which
  removes this internal repair freedom; one eliminated-root equality cannot
  support `(SFS1)`.

- **Even the symmetric pair of mixed chamber words is insufficient.**
  `two-mixed-a2-words-do-not-control-fold-square` adds the `w_23` chamber mate
  of the preceding identity.  An exact dihedral `M_2` packet sets both
  positive root slots to `1`, both opposite-root/Weyl slots to the swap, and
  the denominator to a rotation of order three.  Both torus closures and both
  mixed identities are exact, but the Gram defect remains `3/32`.  The next
  local relation must therefore tie a Weyl slot back to an opposite root (the
  packet violates `W_12E_12W_12^*=B_21`) or use a closed chamber loop which
  forbids this collapsed-root sector.
