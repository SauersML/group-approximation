---
rg: 2
id: higman-seam-gate-needs-only-padded-bs-correction
kind: claim
title: The Higman four-seam gate needs only trivially padded BS(1,2) correction, and padding with any other auxiliary feeds it only when that auxiliary is itself a collapsing Higman cycle
distinct_from:
  higman-four-cycle-intrinsic-mf-seed: that is the open marked collapse and states that an operator-norm packet proof needs same-dimension BS(1,2) correction; this proves same-dimension correction is not needed, only correction after block sum with an identity block, and shows that nontrivial auxiliary block sums (Willett R_q padding, stable uniqueness) feed the gate only through their trivial instances.
  higman-hs-microstates-are-near-glued-exact-bs-cycles: that performs the normalized-HS exactification with no padding; this is the operator-norm reduction with padding and the auxiliary-gluing obstruction.
  three-higman-bs-seams-vanish-fourth-is-product-holonomy: that classifies exact packets and scalarizes the fourth seam for one packet type; this is a quantifier-level reduction and says nothing about which cycles collapse.
  bs1n-rq-padded-opnorm-stability: that is the imported padded stability theorem for BS(1,n); this determines which padded corrections the Higman gate can consume.
---

**ESTABLISHED (elementary proof; not Lean-verified).**  Write a packet for an
exact pair `C Z C^* = Z^2` of unitaries.  Consider the following statements,
with indices in `Z/4`.

`(HMF5)` (from `higman-four-cycle-intrinsic-mf-seed`): for every `epsilon>0`
there is `delta>0` such that every finite-dimensional unitary tuple with
`max_i ||U_i U_(i+1) U_i^* - U_(i+1)^2|| <= delta` has `max_i ||U_i-1|| <= epsilon`.

`(TPC)` trivially padded correction for `BS(1,2)`: for every `epsilon>0` there
is `delta>0` such that for all `N` and `A,B in U(N)` with
`||A B A^* - B^2|| <= delta` there are `k>=0` and an exact packet `(C,Z)` in
`U(N+k)` with

```text
||C-(A (+) 1_k)|| <= epsilon,   ||Z-(B (+) 1_k)|| <= epsilon.   (TPC1)
```

`(CGC)` collapse of glued exact cycles: for every `epsilon>0` there is
`eta>0` such that for all `M` and exact packets `(C_i,Z_(i+1))` in `U(M)` with
`||Z_(i+1)-C_(i+1)|| <= eta` for every `i`, one has `max_i ||C_i-1|| <= epsilon`.

Then:

1. **Reduction.**  `(TPC)` and `(CGC)` together imply `(HMF5)`.  Same-dimension
   matricial stability of `BS(1,2)` (the case `k=0`), which
   Eilers--Shulman--Sorensen leave open, is not needed.
2. **Equivalence of the second gate.**  `(HMF5)` implies `(CGC)` with
   `eta(epsilon)=delta(epsilon)/3`.  So under `(TPC)`, `(CGC)` is equivalent to
   `(HMF5)`: it is the marked collapse restricted to exact-packet cycles.
3. **Exact auxiliaries must be trivial.**  If `V_0,...,V_3` in `U(K)` satisfy
   `V_i V_(i+1) V_i^* = V_(i+1)^2` exactly, then every `V_i=1`.  The proof uses
   only spectra and orders, with no Malcev residual finiteness and no
   Higman no-finite-quotient theorem.
4. **Auxiliary gluing obstruction.**  Let four exact packets `(C_i,Z_(i+1))` on
   a common space `H (+) K` satisfy
   `||C_i-(U_i (+) A_i)||, ||Z_(i+1)-(U_(i+1) (+) B_i)|| <= epsilon` for some
   operators `A_i,B_i` on `K`.  This is the output shape of any per-seam
   padded correction, including Willett's `R_q`-padding
   (`bs1n-rq-padded-opnorm-stability`) after the per-seam auxiliary spaces
   are arranged in one common space.  Then the family is a `(CGC)` input with
   seam `eta` only if the auxiliary seams satisfy
   `||B_i-A_(i+1)|| <= eta+2epsilon`.  Conversely, auxiliary seams below
   `eta-2epsilon` make it a `(CGC)` input.  When it is an input, `(CGC)` with modulus `epsilon'` forces
   `||A_i-1|| <= epsilon'+epsilon` and `||B_i-1|| <= eta+epsilon'+2epsilon`.
   Every such family is then a `(TPC)` instance at accuracy
   `3epsilon+2epsilon'+eta`.  Take a sequence of such families whose
   auxiliary seams and `epsilon` tend to `0`, with one auxiliary generator
   bounded away from `1`.  That sequence yields a sequence of Higman tuples
   contradicting `(HMF5)`.

## Obstruction (class killed)

The class is every per-seam padded operator-norm correction of the four
`BS(1,2)` packets, with an uncontrolled auxiliary summand, used as the local
step of the four-seam gate.  Examples are Dadarlat-style weak stability,
Willett's `R_q`-stability, very flexible stability, and stable uniqueness
theorems with absorbing auxiliaries.

- **Invariant.**  On a common padded space, the auxiliary summands of the
  four corrected packets satisfy the same cyclic seam conditions as the
  original tuple.  In the exact case, the squaring permutation of the spectra
  and the smallest-prime chain `p_0<p_1<p_2<p_3<p_0` are also invariant.
- **Step where every member dies.**  The step is gluing the auxiliary
  summands of different seams.  If they glue exactly, they are trivial (item
  3).  If they glue approximately, they already form a `(CGC)` input, and
  under `(CGC)` they are almost trivial (item 4).  So such a method reaches
  the gate only through its trivially padded instances, that is, through
  `(TPC)`.  Absorbing auxiliaries, which contain nontrivial finite-quotient
  representations and are needed by stable-uniqueness proofs, are never
  consumed.

Consequently the local prerequisite of the packet route to
`higman-four-cycle-intrinsic-mf-seed` is exactly `(TPC)`
(`bs12-trivially-padded-opnorm-correction`).  It is strictly no stronger than
the open Eilers--Shulman--Sorensen question.  The published padded theorem
does not supply it.

Proof: `higman-seam-gate-needs-only-padded-bs-correction-proof`.
