---
rg: 2
id: effective-fp-nonhyperlinearity-transfer
kind: claim
title: An effective non-hyperlinearity certificate transfers to a finitely presented host at a near-quadratic cost
artifacts:
  - research/artifacts/two-paper-ingestion-2026-08-19.md
distinct_from:
  finitely-presented-nonsofic-group-exists: that is the unconditional existence of a finitely presented nonsofic group via the finite-table cover, a qualitative statement about soficity; this is a quantitative transfer statement about hyperlinearity certificates and assumes a certificate as input.
  quantitative-higman-embedding-with-dehn-control: that is the imported embedding; this is the composite with the transfer lemma, and its content is the resulting defect budget.
  subgroup-dehn-function-is-the-hyperlinearity-modulus: that is the general lemma for an arbitrary host; this instantiates it at the host produced by the Chornomaz-Wagner embedding and reads off the exponent.
---

Let `G` be a finitely generated group whose word problem is solvable by a
non-deterministic Turing machine with time function at most `T(n)`, with
`T(n)^2` superadditive.  Fix `eps>0` and let `H_eps` be the finitely presented
host of `quantitative-higman-embedding-with-dehn-control`, so that `G <= H_eps`
is boundedly distorted and

```text
delta_(G,H_eps)(n) <= T(n)^(2+eps).
```

Then:

**(EFT1)**  If `G` is not hyperlinear, neither is `H_eps`, and `H_eps` is
finitely presented.

**(EFT2)**  Quantitatively, an effective non-hyperlinearity certificate for `G`
at scale `(n, epsilon, alpha)` in the sense of `(SDM3)` yields one for `H_eps`
at relator defect

```text
delta < epsilon / T(n)^(2+eps).
```

**(EFT3)**  When the word problem of `G` is quasilinear and `G` is
non-hyperbolic, the exponent is quasi-optimal: the transfer cost is
`n^(2+eps)`, and by the isoperimetric gap of Gromov and Ol'shanskii no
quasi-isometrically embedded host can do better than quadratic.

**What this is and is not.**  `(EFT1)` alone needs none of this machinery -- it
is the standard heredity of hyperlinearity under subgroups together with any
Higman-type embedding, and this repository already reaches finitely presented
witnesses through `torsion-free-higman-embedding` and the finite-table cover,
neither of which requires a decidable word problem.  The content is `(EFT2)`
and `(EFT3)`: they say what the finite presentation *costs* in defect budget,
and that the cost is essentially the square of the word-problem time.

That matters for this program specifically, because every route to the goal
here is a defect-budget argument.  A certificate proved at the finitely
generated witness with an explicit modulus does not become a finitely presented
theorem for free; it becomes one after paying `delta_(G,H)`, and until this
node there was no statement in the graph of what that payment is.
