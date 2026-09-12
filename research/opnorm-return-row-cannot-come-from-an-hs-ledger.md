---
rg: 2
id: opnorm-return-row-cannot-come-from-an-hs-ledger
kind: claim
title: The operator-norm return row is strictly stronger than its normalized-HS shadow, and separates exactly at carrier density
distinct_from:
  one-coarse-to-fine-prefix-isometry-closes-the-reservoir: that establishes the normalized-HS floor for the coarse-to-fine cell; this compares that floor with the operator-norm floor of the same cell and locates the exact point at which the two lanes stop feeding each other.
  paired-same-reservoir-boundary-lemma: that is the open normalized-HS boundary ledger this calibration is about; this does not attempt it, and instead states which of its intermediate estimates can and cannot be reused by an operator-norm decoder.
  rank-deficient-return-row-has-operator-norm-one: that computes the operator-norm floor; this is the comparison of that floor with the 2-norm floor and the resulting transfer rules between the two lanes.
  rank-deficient-return-has-a-singular-value-plateau: that computes the whole singular-value plateau of the row and so gives every Schatten floor at once; this is the resulting statement about which lane can feed which, and its content is the transfer no-go rather than the spectral count.
  gauge-cokernel-checksums-cannot-produce-a-normalized-hs-gap: that rules out one family of checksums as sources of a normalized-HS gap, inside the HS lane; this rules out the whole HS lane as a source of an OPERATOR-NORM row, and is a statement about norms rather than about checksums.
---

**ESTABLISHED.**  Fix `M_d(C)` with normalized trace `tau=tr/d` and
normalized Hilbert--Schmidt norm `||A||_2=tau(A^*A)^(1/2)`.  Let `P!=0` carry
exact matrix-unit systems of sizes `r<s` with common identity `P`, let
`e=e_11`, `f=f_11`, let `J` be unitary, and put `L=(1-f)Je` as in `(ROW1)`.
Then, exactly:

```text
||L||_2 <= ||L||_op <= sqrt(d) ||L||_2,                    (LDG1)

tau(P)(1/r-1/s) <= ||L||_2^2 <= tau(P)/r,                  (LDG2)

||L||_op = 1.                                              (LDG3)
```

Consequences, and they run in one direction only.

1. **Operator-norm implies normalized-HS, free.**  A bound
   `||L||_op<=omega` gives `||L||_2<=omega` with no density hypothesis.  So
   the operator-norm row of `opnorm-leavitt-coarse-fine-return-row` **implies
   outright** the normalized-HS row `(CFI10)` that
   `one-coarse-to-fine-prefix-isometry-closes-the-reservoir` reduces its
   target to, and implies it on carriers of arbitrarily small density where
   the HS statement is vacuous.

2. **Normalized-HS does not imply operator-norm, and the loss is exactly the
   density.**  By `(LDG2)`, `||L||_2` is pinned to `sqrt(tau(P))` up to the
   absolute factors `sqrt(1/r-1/s)` and `sqrt(1/r)`, while `||L||_op=1`
   regardless.  Their ratio is `tau(P)^(-1/2)`, which is unbounded.  The
   `sqrt(d)` in `(LDG1)` is therefore not slack in a crude inequality: on the
   very configuration at issue it is attained up to constants.

3. **The two lanes trade one obligation for the other.**  The operator-norm
   lane deletes the positive-density obligation entirely -- the reblocking of
   `torsion-normal-generator-has-full-support-corona-core`, the paired mass
   ledger of `paired-same-reservoir-boundary-lemma`, the `1/36` floor and the
   four-word `s_4` placement of
   `four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap` all become
   unnecessary.  In exchange it demands a **strictly stronger** estimate of
   the same row.

## One plateau, two endpoints

`rank-deficient-return-has-a-singular-value-plateau` sharpens the picture and
explains why the separation is exactly a density: the singular value `1` of
`L` has multiplicity at least `rank(e)-rank(f)`, so the normalized Schatten
norms obey `||L||_(p,norm) >= ((rank(e)-rank(f))/d)^(1/p)`.  Both floors above
are endpoints of that one plateau -- `(LDG2)` is `p=2` and `(LDG3)` is
`p=infinity` -- and the gap between them is the plateau's *relative*
multiplicity `(rank(e)-rank(f))/d = tau(P)(1/r-1/s)`.  So clause 2 is not an
artefact of choosing the 2-norm: **every** finite `p` degrades with the
carrier density, and only `p=infinity` does not.  A ledger that improved from
`p=2` to any larger finite `p` would still be defeated by a low-density
carrier.

## The operational rule this sets

*No estimate produced by summing, averaging, or tracing can prove the
operator-norm row.*  Every trace ledger, Reynolds average, superrank drop,
energy floor and standard-polynomial comparison in this program outputs a
bound on `||.||_2`, and by clause 2 such a bound is compatible with
`||L||_op=1` on a low-density carrier -- indeed it is *forced* to be
compatible with it, since `(LDG3)` holds unconditionally.  So none of the
following can be reused for `opnorm-leavitt-coarse-fine-return-row`:
`balanced-controlled-whitehead-return-checksum`,
`coarse-fine-selector-covariance-has-quarter-trace-floor`,
`controlled-fine-reflection-superrank-orientation-law`,
`cyclic-coarse-fine-selector-rows-spread-carrier-error`, or any successor of
the same type.

What can be reused is operator-norm-native: the lossless conjugacy
addressing of `conjugacy-addressed-opnorm-challenges-are-lossless`, the
frozen-coordinate capacity diagonal of
`opnorm-coordinatewise-capacity-diagonal`, the support profile of
`finite-group-opnorm-support-profile`, and the exactification modulus of
`opnorm-packet-exactification-is-dimension-free`.

This is a constraint on method, not an obstruction: nothing here says the
operator-norm row is false or unreachable.  It says the reachable inputs are
the operator-norm ones, and that a claim to have "transferred" the HS
same-reservoir work to the operator-norm lane should be disbelieved on sight
unless it exhibits an operator-norm input.
