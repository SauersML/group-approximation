---
rg: 2
id: uniform-normal-rank-certificate-for-degree-kernels
kind: claim
title: A uniform certificate that no degree-m word normally generates the kernel
distinct_from:
  leavitt-degree-kernel-normally-generated-by-one-word: that asks for one explicit word over one explicit group that does normally generate its kernel, which would be a counterexample; this asks for a uniform reason that no word ever does, which would be a proof. They are opposite answers to the same question and cannot both be established.
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

For every nonabelian simple `S`, every `m >= 1` and every `w in N_m` with
`deg_t(w) = m`, construct a quotient

    N_m  -->>  D_w ,

compatible with the conjugation action of `S * <t>`, in which the image of
`w` has **proper** normal closure.

Producing such a `D_w` uniformly proves `kl-holds-over-two-generator-simple-groups`
and hence `kervaire-laudenbach-nonsingular-conjecture`.  By
`degree-kernel-abelianization-is-infinite-cyclic`, `D_w` cannot be chosen
abelian: the abelian quotient is `Z` and every candidate word already
generates it.

## Attempts

None run here — this is where the 2026-08-17 audit stopped, and it is
recorded as the target rather than as a result.  What is known about the
shape of a solution:

1. **It must be nonabelian**, by the invalidating computation above.  This is
   the one firm constraint, and it is what kills the otherwise obvious
   first-homology approach.
2. **Candidate machinery**, in rough order of concreteness: a finite
   nonabelian quotient of `N_m` in which `w`'s normal closure is visibly
   proper; a Peiffer-commutator quotient of the identities among relations; a
   crossed module or second relation module; an explicit `pi_2` class of the
   relative presentation.
3. **Uniformity is the difficulty, not existence.**  For a *fixed* `S`, `m`
   and `w` a proper quotient is often easy to exhibit; what the conjecture
   needs is a construction that does not consult `w` beyond its degree, and
   no such construction is known even for one infinite family of `S`.
4. **The degree hypothesis is not an extra handle.**  If `w in N_m` normally
   generates `N_m` then `deg_t(w) = ±m` automatically: the quotient is `C_m`,
   and by `kl-simple-failure-leaves-only-the-cyclic-quotient` a quotient that
   kills `S` is `C_{|deg_t(w)|}`, while `deg_t(w) = 0` would let it surject
   onto `Z`.  So writing `deg_t(w) = m` into the statement restricts nothing,
   and a certificate cannot buy anything by assuming it.

A negative result here — a family of `S`, `m`, `w` for which no such quotient
exists — would not refute the conjecture, only this route to it.
