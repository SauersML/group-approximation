---
rg: 2
id: jnvwy-pasting-does-not-close-ldpc-synchronization
kind: claim
title: JNVWY tensor-code pasting is same-algebra but not a uniform bounded-template LDPC synchronizer
distinct_from:
  fixed-field-plane-point-loses-uniform-low-degree-robustness: that audits the Reed--Solomon low-degree specialization; this audits the general interpolable tensor-code theorem and the repeated binary LDPC interface.
  quantum-low-degree-is-not-a-direct-finite-template-compiler: that concerns relative-small-cancellation incidence after low-degree decoding; this concerns the earlier same-Hilbert shared-face synchronization gate.
  bounded-template-average-blr-occurrence-decoder: that records the general tensor-code obstacle as one item in a broader metapixel audit; this gives the exact parameter and occurrence dichotomy for the current repeated-overlay proposal.
---

The tensor-code soundness theorem of Ji--Natarajan--Vidick--Wright--Yuen is
genuinely positive in one important respect: for a tracial strategy in a von
Neumann algebra `A`, its global projective codeword measurement `{G_c}` is
constructed **inside the same algebra `A`**.  Thus no dilation or matrix-size
change prevents its use in normalized Hilbert--Schmidt questions.

It nevertheless does not establish
`repeated-ldpc-shared-face-marginal-synchronization`, for three quantitative
reasons.

Before making this comparison, the repeated overlay must be balanced.
`unbalanced-pair-sum-overlay-has-scalar-syndrome-escape` gives a scalar all-one-syndrome
escape when the `M` original checks are diluted among `Theta(M^2)` pair-sum
checks.  JNVWY's augmented test does not make this weighting mistake: its
line-consistency component retains fixed sampling weight alongside its
commutation component.  Repeating every original LDPC face `M` times repairs
the scalar escape, but does not change any of the three obstructions below.

1.  The theorem is for the augmented axis-line test of an interpolable
    tensor code `C^(tensor m)`, not for arbitrary bounded-width LDPC parity
    faces or their pairwise sums.  Its hypotheses include a point
    measurement shared across every direction, line-codeword measurements,
    and the separate subcube commutation test.  The repeated LDPC overlay
    supplies none of the interpolation/pasting maps used in that proof.

2.  With base length `n`, distance `d`, and `t=n-d+1`, the formal error has
    the form

    ```text
    eta = poly(m,t,r) (poly(epsilon,1/n)+exp(-Omega(r/m^2))),
    r>=12mt.                                               (JTP1)
    ```

    Hence the published modulus is not uniform when the tensor dimension
    `m` or interpolation parameter `t` grows.  In particular, for a fixed
    binary base code, `m` must grow to obtain unbounded message dimension,
    and `(JTP1)` does not give a length-independent `omega(epsilon)`.

3.  The geometry is not bounded occurrence.  A point of `[n]^m` lies on one
    axis line in every one of the `m` directions.  The augmented test also
    asks for joint answers at two arbitrary points in randomly chosen nested
    subcubes.  Splitting the common point measurement into bounded-degree
    occurrences requires first proving that those copies represent one
    measurement with enough consistency to invoke the theorem.  That is the
    shared-face synchronization problem again, not a consequence of the
    tensor-code theorem.

There is a sharp finite-template dichotomy.  If the binary base code has
dimension `k`, a line answer has `|C|=2^k` possibilities while the tensor
message dimension is `k^m`.  For unbounded messages, either `k` grows, so the
line-answer PVM is not a fixed finite packet, or `m` grows, so point incidence
and the coefficient in `(JTP1)` are unbounded.  Keeping both bounded keeps
`k^m` bounded.

Thus JNVWY gives the correct kind of same-algebra global PVM only after one
accepts growing robustness loss or growing local packets/incidence.  A new
constant-parameter operator agreement composition would be needed to use it
at the Cairn gate.
