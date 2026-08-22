---
rg: 2
id: atlas-a4-rank-three-core-commutant-collapse
kind: claim
title: The fourteen-word A4 core plus collision 19243 forces the relative chart frame into the GL3(2) commutant
distinct_from:
  atlas-a4-componentwise-commutant-collapse: that asks for simultaneous closeness to both full packet-component commutants, including the central C3 sector; this target throws away all sixteen central-C3 pair-cubes and asks only for the rank-three GL3(2) commutant already sufficient for the raw S3 contradiction.
  atlas-a4-relative-packet-commutator-collapse: that asks for commutation with all ten packet letters and therefore the full A8 commutant; this target only asks for the standard rank-three subgroup H.
---

Let `sigma_n` satisfy the exact-regular normalized A4 context-network hypotheses
of `atlas-a4-holonomy-coherence-gap`, and let

```text
U_n in U(20160 k_n)
```

be the relative chart frame.  Retain only the fourteen A4 contexts of
`atlas-a4-rank-three-core` and the collision condition `q_19243 -> 1`.  Let

```text
H=<H_6,K>=diag(GL_3(F2),1) < A8.
```

Prove the dimension-free collapse

```text
dist_2(U_n, lambda_(k_n)(H)') -> 0.                    (A4-H-CORE-COLLAPSE)
```

No conclusion about the two central `C3` packet labels, the full `H_18`
commutant, or the full `A8` commutant is required.

## Attempts

- **Reduced abstract quotient probe.**  The exporter
  `experiments/atlas_a4_packet_19243_quotient.py --core` now forms

  ```text
  (A8*A8)/<< fourteen rank-three pair-cubes, q_19243 >>.
  ```

  A bounded GAP 4.14 probe through Sage on MSI reached coset-table enlargement
  rather than a small collapse and was stopped at sixty seconds.  Thus this
  quotient is not a cheap finite certificate.  No order, infinitude, or factor
  survival claim is inferred from the timeout; the useful output is the exact
  reduced presentation for a later subgroup- or rewriting-specific attack.

- **Two rectangles, not thirty contexts.**  The fourteen-word core is two
  copies of `K_(2,2)`.  After extracting one qutrit/multiplicity edge message
  per distinct pair, `unitary-k2m-rectangle-synchronization` leaves exactly one
  noncommutative rectangle holonomy per component.  The local gauge problem
  should therefore reduce to two `U(k_n)` variables.
- **Use the exact subgroup ladder.**  The two core components are `H_6 ~= S3`
  and `K ~= S3`, and they generate exactly the same standard
  `H=GL_3(2)` that appears in the established five-word tangent certificate.
  Finite-subspace gluing on the two `S3` commutants is automatically stable
  under external multiplicity.
- **Put collision 19243 only where it actually lives.**  Its four second-chart
  syllables generate `K`; its repeated first-chart involution enlarges `H` only
  to the affine hyperplane stabilizer `AGL_3(2)`.  Seek a finite
  connection-Laplacian / representation-ring inequality showing that the
  collision residual kills the two rectangle holonomies modulo `H'`.
- **Exploit the classical audit as the zero-dimensional boundary condition.**
  The fourteen-word core has exactly the same sixty classical automorphism
  alignments as the full thirty-word packet, and `q_19243` kills every one.
  Any remaining obstruction is therefore genuine multiplicity mixing, not a
  missed classical chart position.
- **Do not use the discarded C3 sector unless this target is refuted.**  Those
  sixteen pair-cubes are irrelevant in the classical automorphism sector and
  are not needed by the final two-generator S3 covariance contradiction.  A
  proof here would bypass more than half of the A4 packet and all full-A8
  packet-centrality machinery.
- **The collision equation leaves a continuous line-sector angle.**
  `atlas-19243-has-continuous-regular-s3-line-holonomy` gives exact balanced
  collision solutions with regular `S3` restriction in which an arbitrary
  dihedral reflection survives on `triv direct_sum sign`.  Hence the proposed
  connection-Laplacian must contain an off-diagonal packet term coupling that
  line sector to the two standard copies.  A block-diagonal estimate internal
  to the collision `S3` has zero gap and cannot prove this claim.
- **The cross-component line angle has now been computed exactly.**
  `atlas-a4-two-c3-line-carriers-have-exact-angle-gap` proves that the
  `C3`-fixed line spaces of `H_6` and `K` have largest nonconstant squared
  cosine `1/2+sqrt(17)/18`, hence connection gap
  `(9-sqrt(17))/18`.  The surviving task is no longer to prove an abstract
  angle between the components.  It is the common-`U` compression identity:
  extract the collision's dihedral angle as one vector in the `K` line space
  and show an `H_6` packet residual controls its orthogonal complement to the
  `H_6` line space.  Then the exact angle gap pays that mode quantitatively.
- **The common variable is now canonical.**  With the trivial/sign central
  idempotents of `K`, the free collision angle is
  `Z(U)=E_K^- U^*rho(b_0)U E_K^+`.  The tensor-square version of the exact
  angle theorem gives
  `||Z-P_6 ZP_6||_2^2 >=((9-sqrt(17))/18)||Z||_2^2`.
  Hence the last symbolic packet identity is precisely `(A4-C3-9)` in
  `atlas-a4-two-c3-line-carriers-have-exact-angle-gap`: bound the left side
  by the fourteen shifted common-`U` residuals.  This formulation is
  invariant under the independent gauges of the existential factorizations.
- **The leakage has an exact two-covariance sum of squares.**
  `atlas-common-u-c3-compression-is-two-covariance-residuals` expands the
  left side of `(A4-C3-9)` as the sum of the left and right `C_6` covariance
  residuals of the single operator `E_K^-U^*rho(b_0)UE_K^+`.  Exact
  compression is therefore equivalent to two displayed linear equations.
  The packet endpoint audit shows that `b_0` occurs in none of the fourteen
  edges, so neither residual can telescope along one shifted factorization.
  What remains is sharply a joint packet--collision cycle identity producing
  those two mixed residuals, or a matrix-only trace obstruction forcing them.
- **There is no packet path carrying that mixed residual.**
  `atlas-fourteen-edge-core-has-no-collision-to-c6-path` uses the exact
  `K_(2,2) disjoint_union K_(2,2)` incidence graph and collision localization:
  collision lives entirely at the `K` component, `b_0` is not a packet
  vertex, and `a` lies in the `H_6` component.  Spanning-tree gauge fixing
  leaves one independent rectangle in each component, but no path between
  them.  Thus a word telescope through edge messages cannot prove the two
  covariance equations.  The remaining positive route must use the shared
  literal `U` at the level of the simultaneous shifted-double-coset
  intersection; an exact matrix point of that intersection with nonzero
  covariance would instead refute the target estimate.
- **Linearized simultaneous-double-coset transversality is false.**
  `atlas-fourteen-shifted-tangent-spaces-have-an-s3-flat` differentiates the
  literal eight distinct shifted cells at the reference alignment.  Choosing
  one cyclic fixed-space summand from each tangent sum yields the same
  subgroup `L ~= S3`, so `Fix(Ad rho(L))` is a common tangent flat of
  dimension `3360` on every relative regular coordinate.  It contains
  explicit directions outside `rho(H)'`.  Thus alternating projections onto
  the fourteen packet tangent sums cannot prove commutant collapse.  Since
  the reference packet alignment is not collision-zero, this does not refute
  the nonlinear joint estimate; it says collision must remove this exact
  `S3` flat through a genuinely nonlinear common-`U` coupling.
