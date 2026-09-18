---
rg: 2
id: bs12-trivially-padded-opnorm-correction
kind: claim
title: Approximate BS(1,2) pairs are operator-norm close to exact pairs after block sum with an identity block
distinct_from:
  bs1n-rq-padded-opnorm-stability: that is Willett's theorem, where the block-summed auxiliary is an arbitrary finite-quotient representation; here the auxiliary must be the trivial representation, which is the only padding the Higman gate can glue.
  bs14-hs-stability-does-not-supply-relative-op-basin: that concerns normalized-HS stability; this is an operator-norm, dimension-uniform statement.
  higman-seam-gate-needs-only-padded-bs-correction: that proves this statement plus glued-cycle collapse gives the Higman marked collapse; this is the open local prerequisite itself.
---

**OPEN.**  `(TPC)`: for every `epsilon>0` there is `delta>0` such that for all
`N` and unitaries `A,B in U(N)` with

```text
||A B A^* - B^2|| <= delta
```

there exist `k>=0` and unitaries `C,Z in U(N+k)` with `C Z C^* = Z^2` and

```text
||C-(A (+) 1_k)|| <= epsilon,      ||Z-(B (+) 1_k)|| <= epsilon.
```

This is implied by same-dimension matricial stability of `BS(1,2)` (the case
`k=0`), which is Eilers--Shulman--Sorensen arXiv:1808.06793v4, Section 6,
Question 3, and is open.  It implies nothing about the auxiliary in
`bs1n-rq-padded-opnorm-stability`, which is published and has uncontrolled
padding.  Neither implication is known to reverse.

Why it is a separate prerequisite: by
`higman-seam-gate-needs-only-padded-bs-correction`, `(TPC)` together with the
glued-cycle collapse `higman-exact-packet-cycles-collapse-opnorm` gives the
Higman marked collapse.  Any per-seam correction whose auxiliary summand is
not trivial reaches that gate only through instances of `(TPC)`.  `(TPC)` is
purely about `BS(1,2)` and can fail even if the Higman collapse is true.

## Attempts

Recorded when the claim was created on 2026-09-18 (reframing).  These are
partial, not a proof.

- *Spectral half.*  An operator-norm defect `delta` matches the eigenvalues of
  `B` with those of `B^2` within `c delta` (Bhatia--Davis--McIntosh constant
  for normal matrices).  That matching is a permutation `s` of eigen-indices
  with `|2x_j - x_(s(j))| <= c delta` (angles mod `1`).  Each cycle is a
  periodic pseudo-orbit of the doubling map.  Expansivity (use the
  contracting inverse branch) shadows it by a true periodic orbit `y_j` with
  `|x_j-y_j| <= c delta`.  So `B` can be replaced by `B'` with the same
  eigenvectors and exactly squaring-invariant, cycle-constant multiplicity
  spectrum, with `||B-B'|| <= c delta`.  This half needs no padding.
- *Conjugator half.*  With `B'` fixed, `A` is a `3c delta`-approximate
  intertwiner from `B'` to `B'^2`.  Correcting it with `B'` fixed can fail, in
  the same way as for Voiculescu's pair (shift against a fine clock).  The
  twisted pair `A=A_0 V` (with `A_0 e_j=e_(j/2)` on `Z/N`, `N` odd, and `V` the
  shift) is nevertheless exactly correctable after moving `B`: since
  `A_0^* V A_0 = V^2`, conjugating `B'` by a power of `V` absorbs the shift.
  So the Bott-type twist is not an obstruction.  This is consistent with
  `K_*(C^*(BS(1,2)))` carrying no Bott class, since `H_2(BS(1,2))=0`.
- *Where it stops.*  No general construction corrects the conjugator with
  only an identity padding, and no same-dimension or trivially padded
  obstruction is known.  Stable-uniqueness proofs need absorbing auxiliaries
  containing nontrivial finite-quotient representations.  Exact packets
  cannot be deformed to trivial ones because the spectrum of `Z` is rigid in
  the odd roots of unity.  So Willett's `R_q`-padding does not specialize to
  trivial padding.
