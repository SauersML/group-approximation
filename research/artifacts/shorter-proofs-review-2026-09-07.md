# Version-45 shortening review: what is new, what already landed

2026-09-07.  Audit of a third forwarded dossier, six proposed proof
replacements for `non_mf_groups_exist.tex`.  All six were re-derived here and
all six are correct.  Most of them are already in the manuscript or already in
the graph; three items are new and are the only ones authored as nodes.

## Verdict per section

**§1, Kazhdan projection as a norm limit of finitely supported probability
averages.**  Correct: a lazy symmetric average over a finite Kazhdan
generating set acts as the identity on invariant vectors and with norm at
most `1-delta` on their complement, uniformly over all unitary
representations, so its powers converge to `e_L` in `C*_max(L)`.  NEW as a
named tool; the printed proof of `thm:transport` uses general scalars
`(a_ell)` with a trivial-character correction `|sum a_ell - 1| < epsilon`,
which the probability average removes.  It does not conflict with
`kazhdan-projection-not-in-l1`: that says `e_L` is not in the image of
`l^1(L)` and that the averages are not `l^1`-Cauchy, which is compatible
with convergence in the `C*_max` norm.  Node
`kazhdan-projection-is-norm-limit-of-finite-averages`.

**§2, approximate-fixed-vector lemma replacing the Hilbert ultraproduct.**
Correct, and ALREADY LANDED: the printed proof of `thm:transport` lifts `P`
to projections `P_n` by functional calculus and has no ultraproduct, no
representation of the corona on it, and no ultrafilter.  Clause (2) is
`lem:kazhdan-projection-order`, and abstractly it is clause 1 of the
established `kazhdan-projection-finite-target-calculus`; the finiteness input
is the polar-decomposition argument, which the dossier also keeps.

What is NOT yet landed is the free strengthening.  The printed proof
restricts to `sup_n ||x_n||_op <= c`, but every estimate in it is applied to
`x_n` through operators bounded on `(M_(d_n),||.||_2)`, so `c` may be taken
to be `sup_n ||x_n||_2`.  Node
`hs-bounded-kazhdan-transport-without-ultraproduct`.

**§3, corner fact and the short proof of `thm:normal-kazhdan`.**  The corner
identity is clause (CI1) of the established
`matrix-corona-projection-ideal-and-corner-calculus`, and unitary lifting by
polar decomposition is already used throughout.  The proof of
`thm:normal-kazhdan` printed since commit c156f3d53 is
`normal-kazhdan-via-corner-trace-character`, which reaches the contradiction
through an ultrafilter trace state `T_omega([a_n]) = lim_omega tr_(r_n)(a_n)`.
The dossier replaces that by a finite probability average `a` with
`||a - e_K|| < 1/2` and the elementary chain

```text
1 = lim_n |tr_(r_n)(B_n)| <= limsup_n ||B_n|| = ||pi(a)|| < 1/2,
```

using `|tr(W) - 1| <= ||W - I||_2`.  This removes the last ultrafilter from
the section, so it is recorded as a fourth route,
`normal-kazhdan-via-finite-average-corner`.

**§4, eliminating the inverse matrix from the ring proof.**  ALREADY LANDED.
`eq:intertwine` in the manuscript is exactly `u e_(ij)(a) = e_(ij)(sat) u`
with the row-increment justification, and the paragraph after it computes
`uc = e_12(e) u` from `e^2 = e`, `te = 0`, `es = 0` and concludes
`ucu^(-1) = e_12(e)`.  Re-derived here independently: with `ts = 1` and
`e = 1 - st` one has `e^2 = e`, `es = 0`, `te = 0`; `u(aE_(ij))` has the
single entry `sa` at `(i,j)`, while `sat E_(ij) u` contributes
`sa(ts) = sa` at `(i,j)` and `sa(te)t^(j-1) = 0` at `(i,4)`; and both `uc`
and `e_12(e)u` equal `u + et E_14`.  Nothing to author.

**§5, the amenable-extension trace proposition.**  ALREADY IN THE GRAPH, as
the dossier itself says.  `locally-rf-groups-have-quasidiagonal-canonical-trace`
is the first assertion and `factorization-property-closed-under-amenable-extensions`
is the second, the latter proved for nonsplit extensions by inducing
representations and compressing to Folner windows -- the same argument, with
the same boundary estimate (6).  The corollary about `tau_K` quasidiagonal
and `tau_(K rtimes Z)` amenable but not quasidiagonal is
`integer-crossed-products-can-destroy-quasidiagonal-traces`.  Nothing to
author.

**§6, functoriality of the defect subgroup.**  ALREADY IN THE GRAPH as clause
(ICD2) of `intrinsic-compression-defect-functoriality-and-saturation`, stated
for every homomorphism with no surjectivity hypothesis.  Nothing to author.

## Standing caution the dossier states and this audit repeats

Replacement proofs must not inherit the `\leanverified` markers of the
statements they replace, and the HS-bounded strengthening in particular would
be a new statement under an old marker.  See
`GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedKazhdanTransportCommutantEquality`,
which certifies the operator-norm-bounded form.

## Estimate

The dossier's estimate of two to three saved pages is not assessed here; four
of its six items are already in the current text or the current graph, so the
remaining saving is smaller than stated.
