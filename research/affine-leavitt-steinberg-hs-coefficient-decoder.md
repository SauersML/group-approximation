---
rg: 2
id: affine-leavitt-steinberg-hs-coefficient-decoder
kind: claim
title: Decode the affine active Leavitt cell from normalized-HS Steinberg microstates
distinct_from:
  finite-window-decoder: that asks for three multiplicative products on a fixed-density Pauli corner extracted from an outer-character atlas; this asks for the named affine active idempotent and one relative binary Leavitt cell inside the fixed group St_5(L_A(k[C_aff])).
  hs-steinberg-root-kernel-is-linear-sofic: that promotes the whole quotient by the common root kernel to a rank-metric matrix ultraproduct; this needs only one active coefficient and four named Leavitt operators, together with comparison to one root word.
  approximate-relative-leavitt-cell-kills-active-trace: that proves the terminal trace inequality after coefficient operators have been decoded; this is precisely the missing root-to-coefficient extraction.
  affine-leavitt-decoder-interface-is-mark-collapse-equivalent: that audits the existential carrier formulation and proves it is equivalent to direct marked-root collapse; the present statement is retained as a correct endpoint, but not as a smaller independent decoder lemma.
  affine-leavitt-prescribed-root-spectral-carrier-decoder: that repairs the interface by fixing the carrier from the exactified order-p marked root before the Leavitt contractions are chosen.
---

OPEN. Fix the finite presentation of

```text
Gamma_A=St_5(L_A(k[C_aff]))
```

and the word `w_A=x_12(A)` from
`affine-leavitt-steinberg-mark-is-fd-invisible`. Prove that there are a
constant `C`, a threshold `delta_0>0`, and a modulus
`omega(delta)->0` such that every normalized-HS `delta`-representation
`U` of this presentation, for `delta<delta_0`, produces an orthogonal
projection `P` and contractions `S_0,S_1,T_0,T_1` in the same matrix algebra
with

```text
||T_i S_i-P||_2 <= omega(delta),                 i=0,1,
||S_0 T_0+S_1 T_1-P||_2 <= omega(delta),          (ALD1)
```

and

```text
||w_A(U)-I||_2^2 <= C tr(P)+omega(delta).          (ALD2)
```

Here `k` is the repository's fixed finite splitting field of characteristic
`p>=5`.  There is no characteristic-two specialization of the active packet;
`odd-root-cannot-drive-central-d8-actuator` records the exact order
obstruction to replacing this native mark by a binary central sign.

Only these three coefficient relations are required. No off-diagonal
Leavitt relation, full coefficient-algebra representation, rank control on
every small error, or correction of the whole almost representation is part
of the claim.

Together with `approximate-relative-leavitt-cell-kills-active-trace`, `(ALD1)`
gives `tr(P)<=3omega(delta)`. Then `(ALD2)` collapses the marked root with a
dimension-free modulus. This is the exact remaining analytic interface for
the affine active Leavitt construction.

## Attempts

- **The existential carrier is logically vacuous as an intermediate
  object.**  `affine-leavitt-decoder-interface-is-mark-collapse-equivalent`
  proves that `(ALD1)--(ALD2)` imply direct marked-root collapse, while direct
  collapse satisfies them with `P=S_i=T_i=0`.  Thus this claim remains a
  correct sufficient endpoint but is not a compressed root-to-coefficient
  lemma.  The nonvacuous replacement
  `affine-leavitt-prescribed-root-spectral-carrier-decoder` fixes `P` to be
  the nontrivial spectral carrier of the exactified order-`p` root word.

- **Exact finite-dimensional decoding is closed.** Root subgroups have finite
  image, their common kernel generates a finite coefficient quotient, and
  the relative Leavitt relation kills `A`; this is the proof of
  `affine-leavitt-steinberg-mark-is-fd-invisible`.
- **A common carrier is insufficient.** `carrier-not-decoder` shows that a
  finite root table can retain the relevant carrier while failing to recover
  multiplicative coefficient data. The proof must use paired Steinberg root
  triangles, not only a joint spectral projection.
- **HS error is not rank error.** An arbitrarily small full-rank perturbation
  has normalized rank one, so the exact common-kernel argument cannot be
  transferred by deleting the support of every small error.
- **The requested window is now minimal.** The trace endpoint consumes only
  `T_0S_0`, `T_1S_1`, and `S_0T_0+S_1T_1`. A promising attack is therefore a
  finite root-character orbit for the active central idempotent, coupled to
  three paired root triangles, with a conditional expectation used only to
  recover those products.
- **The exact one-to-two word is now explicit.** After passing to the
  coefficient-central envelope, `affine-active-doubling-is-elementary-matrix-conjugacy`
  writes every active coefficient branch as one Whitehead elementary word.
  More strongly, the distinguished active idempotent itself already doubles
  by that word in the original free relative envelope; centrality is not
  needed for the mark.  However,
  `single-affine-leavitt-branch-chart-is-stationary` proves that this
  conjugacy and the finite head alone form a virtually-free chart with exact
  finite marked countermodels.  The decoder must therefore use the paired
  Steinberg multiplication triangles in addition to the conjugator.
- **Full coefficient centrality loses the affine advantage.**
  `coefficient-central-affine-leavitt-envelope-is-morita-trivial` computes the
  active quotient as two copies of `M_3(L_2(k))`.  Therefore the explicit
  conjugator is a diagnostic model, not by itself a decoder for the original
  free relative envelope.  A useful covariance law must be nontrivial on the
  affine head rather than centralizing it completely.
- **Canonical fixed windows are decoded exactly as far as they can be.**
  `steinberg-root-shear-plancherel-covariance` proves
  that every fixed row-root window has asymptotically uniform Fourier blocks
  and that multiplication is the explicit dual shear.  But
  `plancherel-root-shears-have-no-compression-pressure` shows that closing one
  window and retaining only those full permutations is stationary.  The
  positive datum discarded by that closure is quantified by
  `relative-leavitt-active-subspaces-expand-by-two`: every old active
  coefficient window has a new binary boundary at least as large as itself.
- **Finite torus characters grade roots but do not linearize coefficients.**
  `finite-torus-root-fourier-has-stationary-aliases`
  computes every character corner and every full conjugation-weight
  component in the finite Frobenius packet `(k,+) rtimes Lambda`.  Every
  nontrivial weight has squared HS mass `1/|Lambda|`, while its additive
  defect is at least
  `p/((p-1)sqrt(|Lambda|))` even at zero group defect.  Multiplication is
  convolution over all character weights, so a purported degree-one or odd
  component retains equal-mass higher-weight aliases.  The surviving decoder
  must use the complete block system nonlinearly to recover only `(ALD1)` and
  must exclude this stationary packet by an additional coercive relation.
- **A strictly weaker sufficient target is available.**  The decoder above
  asks for one modulus valid for arbitrary approximate representations.
  Nonhyperlinearity only needs canonical delta microstates.  By
  `fixed-depth-canonical-mark-estimates-rule-out-hyperlinearity`, constants
  may grow arbitrarily with a fixed proof depth.  The remaining scalar target
  `affine-leavitt-boundary-shear-payment` asks the paired root triangles to
  charge the expanding boundary and leave residual marked mass `2^-N` at
  depth `N`.
- **No regular-trace contradiction is asserted.** The decoder is a
  finite-matrix stability statement. It need not extend to the left regular
  representation or any arbitrary tracial representation of `Gamma_A`.
- **A purely tracial square-function proof is impossible.**
  `affine-leavitt-tracial-square-function-firewall`
  proves that fixed word polynomials, packet conditional expectations,
  Gram/SOS forms, spectral coarea, and dimension-free finite-tracial `L2`
  estimates all survive substitution of the left regular representation.
  They therefore cannot collapse the nontrivial mark.  Any successful
  decoder must expose one explicitly finite-matrix coordinate before a
  square-function or coarea ledger is applied; same-reservoir multiplicity,
  superrank transport, or a polynomial-identity factor comparison are the
  currently isolated possibilities.
- **Odd characteristic does not remove the prefix actuator.**
  `odd-leavitt-prefix-whitehead-transport` proves that the signed word
  `E_12(x)E_21(-y)E_12(x)` conjugates the coarse prefix corner to its fine
  descendant in the actual field characteristic `p>=5`.  What fails to
  follow from group-word defect is the common-carrier spectral-selector
  covariance, not the algebraic return itself.
- **The mixed Reynolds endpoint is now one checksum, with a grading
  firewall.**  `balanced-controlled-whitehead-return-checksum` specializes
  the controlled fine-reflection packet to the signed Whitehead actuator:
  canonical balanced orientation leaves at least `1/32-o(1)` normalized
  adjoint leakage for every return, and one finite trace-square overlap
  estimate at level `1/16-o(1)` would convert it immediately into ordinary
  HS word energy.  But
  `orientation-graded-mixed-returns-have-a-balanced-double` proves that any
  enlarged exact cell retaining the stable-letter `C_2` grading admits a
  balanced marked double.  Thus more even Whitehead/Steinberg relations
  cannot force that checksum; the decoder must break the orientation grading
  or expose a genuinely finite-matrix coordinate.
- **One odd selector row is still insufficient.**
  `odd-selector-row-balances-or-kills-outer-action`
  imposes the most direct grading-breaking equality `t=W r W^*`, with `r`
  the coarse Pauli reflection.  An exact eight-dimensional marked model
  absorbs it by taking `t=C tensor diag(1,-1)`; approximate satisfaction
  forces `mu` toward zero and therefore strengthens, but does not return, the
  `1/32` Reynolds gap.  Requiring `W` to normalize the whole packet removes
  the countermodel only by making the controlled outer action inner, which
  kills the intended exact completeness model.  A viable odd coupling must
  therefore address the averaged/self-similar coefficient range rather than
  one reflection.
- **A Reynolds range cannot be replaced by one physical carrier.**
  `controlled-reynolds-density-has-no-fixed-physical-carrier` uses the two
  pure controlled orientations and their balanced direct sum.  The adjoint
  density is `1/16,1/16,1/32`, while every fixed group-algebra projection and
  every ordinary word energy varies affinely under the same direct sum.
  Thus one physicalized averaged coefficient has unavoidable error at least
  `1/64`.  The self-similar decoder must control a genuine trace-square
  overlap, or make one pure extension unavailable through payload-coupled
  odd relations; a fixed returned corner is not enough.
- **No finite packet supplies a pure odd-row anchor.**
  `finite-marked-involution-anchor-has-one-third-wrong-mass` considers an
  arbitrary finite group with central mark and a noncentral involution `a`.
  Its marked Plancherel-average character is zero, so at most two-thirds of
  the marked regular mass can have normalized trace `1/2`, the trace needed
  for the literal controlled reflection.  At least one-third remains in
  wrong orientation types (and a unique marked type has trace zero
  everywhere off the center).  Hence the self-similar anchor must be
  genuinely infinite/type-selective or coupled to the affine/Fano payload;
  enlarging the finite router cannot orient the return.
- **Exact depth pressure is now quantified.**
  `leavitt-prefixes-form-exponential-heisenberg-packet` gives `2^n` Pauli
  pairs over the active root, and
  `leavitt-steinberg-quadratic-radius-pressure`
  realizes them by words of length `O(n^2)`.  Thus the decoder need not invent
  dimension pressure; it must make this existing packet robust with a
  dimension-independent relator ledger.
- **Finite-depth robustness is effective but not uniform.**
  `affine-leavitt-profile-computable-checkpoints` computes a threshold for
  each complete depth-`n` packet and forces dimension `.99p^(2^n)`.  The
  unresolved content of `(ALD1)--(ALD2)` is exactly replacing those unrelated
  thresholds by one amplification-stable modulus.
