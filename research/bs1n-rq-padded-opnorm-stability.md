---
rg: 2
id: bs1n-rq-padded-opnorm-stability
kind: claim
title: BS(1,n) quasi-representations are operator-norm close to honest representations after padding by finite-quotient representations
distinct_from:
  bs12-trivially-padded-opnorm-correction: that is the open same-statement with the padding forced to be the trivial representation, which is what the Higman four-seam gate consumes; this is Willett's published theorem, whose padding is an arbitrary representation factoring through a finite quotient and is not controlled.
  bs14-hs-stability-does-not-supply-relative-op-basin: that audits normalized-HS stability of BS(1,4); this is an operator-norm statement with an uncontrolled block-sum.
---

**ESTABLISHED (literature).**  For every integer `n` with `|n|>=2` (in
particular `n=2`), `BS(1,n)=<a,b | b a b^(-1)=a^n>` is `R_q`-stable in
Willett's sense:

for every finite `S` in `BS(1,n)` and `epsilon>0` there are a finite `T` and
`delta>0` such that for every unital `(T,delta)`-representation
`phi : BS(1,n) -> M_N(C)_1` there are a representation
`theta : BS(1,n) -> U(k)` and a representation `pi : BS(1,n) -> U(N+k)`,
both factoring through finite quotients, with

```text
||(phi(s) (+) theta(s)) - pi(s)|| < epsilon       (s in S).     (RQ1)
```

No control on `k` or on the isomorphism type of `theta` is asserted.

Source: R. Willett, *Conditional representation stability, classification of
\*-homomorphisms, and relative eta invariants*, arXiv:2408.13350 (current
version, PDF dated May 25, 2026, read 2026-09-18): Definition 1.3,
Definition 1.6 with `Q=R=R_q` (Remark 1.8), Theorem 7.9(i), and the last
paragraph of Example 7.11, quoted verbatim in
`bs1n-rq-padded-opnorm-stability-citation`.

## Translation to generator pairs

For `n=2` a pair of unitaries `(A,B)` in `U(N)` with
`||A B A^* - B^2|| <= delta` (here `A` is the conjugating letter) defines,
for every finite `T`, a `(T,C_T delta)`-representation `phi` with
`phi(A)=A`, `phi(B)=B`: fix words `w_g` with `w_e` empty and evaluate them;
for `s,t in T` the word `w_s w_t w_(st)^(-1)` is a product of at most `C_T`
conjugates of the relator or its inverse, and each conjugate evaluates within
`delta` of `1` by bi-invariance.  (Eilers--Shulman--Sorensen,
arXiv:1808.06793, Proposition 2.16, gives the same translation for
finitely presented groups.)  So `(RQ1)` applies to presentation-level
approximate pairs with `S={a,b}`.

## What it does not give

It does **not** give same-dimension matricial stability (Eilers--Shulman--
Sorensen, Section 6, Question 3, remains open), and it does not give the
trivially padded statement `bs12-trivially-padded-opnorm-correction`.  The
padding in Willett's proof comes from a stable-uniqueness theorem, whose
auxiliary summand is not the trivial representation.
`higman-seam-gate-needs-only-padded-bs-correction` shows why this matters for
Higman's group.  Each seam gets its own auxiliary summand, and those summands
can be glued only if they already form a Higman cycle of exact packets. Once
glued, they are exactly trivial, and under the glued-cycle collapse they are
almost trivial.
