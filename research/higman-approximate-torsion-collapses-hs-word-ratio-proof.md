---
rg: 2
id: higman-approximate-torsion-collapses-hs-word-ratio-proof
kind: route
title: Robust gcd iteration around the four-cycle terminates by Higman's smallest-prime lemma
target: higman-approximate-torsion-collapses-hs-word-ratio
requires: []
artifacts:
  - research/artifacts/higman-hs-ratio-scaling-scout-2026-09-17.md
---

Norms are normalized 2-norms of a trace, and all elements are unitaries. We
use `||uxv||_2=||x||_2`, `||x^k-y^k||_2<=k||x-y||_2`, and
`||uxu^(-1)-x||_2<=2||u-1||_2`. Put `eps_j=||g_j g_(j+1) g_j^(-1)-g_(j+1)^2||_2=||r_j-1||_2`
and `tau=||g_i^m-1||_2`. A *linear bound* means a bound
`sum_j c_j eps_j + c tau` with constants `c_j, c >= 0` depending only on
`m` and `i`.

**Lemma A (power transfer).** If `||g_j^a-1||_2<=delta` with `a>=1`, then
`||g_(j+1)^(2^a-1)-1||_2 <= (2^a-1)eps_j + 2delta`.
Proof: `g_j g_(j+1)^(2^k) g_j^(-1)=(g_j g_(j+1) g_j^(-1))^(2^k) ~ g_(j+1)^(2^(k+1))` within `2^k eps_j`.
Conjugating by `g_j^(a-1-k)` preserves distances, and telescoping gives
`g_j^a g_(j+1) g_j^(-a) ~ g_(j+1)^(2^a)` within `(2^a-1)eps_j`. Also
`g_j^a g_(j+1) g_j^(-a) ~ g_(j+1)` within `2delta`. So
`||g_(j+1)^(2^a)-g_(j+1)||_2<=(2^a-1)eps_j+2delta`, which equals
`||g_(j+1)^(2^a-1)-1||_2`.

**Lemma B (robust gcd).** If `||g^a-1||_2<=alpha`, `||g^b-1||_2<=beta` and
`c=gcd(a,b)`, choose integers `0<=u<=b/c` and `0<=v<=a/c` with
`ua-vb=c`. Then
`||g^c-1||_2=||g^(ua)-g^(vb)||_2<=||g^(ua)-1||_2+||g^(vb)-1||_2<=u alpha+v beta`.
This is a linear bound if `alpha` and `beta` are.

**Lemma C (collapse).** If `||g_j-1||_2<=eta`, then
`||g_(j+1)-1||_2=||g_(j+1)^2-g_(j+1)||_2<=eps_j+2eta`, because
`g_j g_(j+1) g_j^(-1) ~ g_(j+1)` within `2eta`.

**Higman's lemma.** If positive integers `A_0,...,A_3` satisfy
`A_(j+1) | 2^(A_j)-1` for all `j in Z/4`, then all `A_j=1`. If some `A_j=1`,
then `A_(j+1) | 1`, and so all are 1. Otherwise let `p_j` be the smallest
prime of `A_j`. From `p_(j+1) | 2^(A_j)-1`, the order `o` of 2 modulo
`p_(j+1)` satisfies `1<o<=p_(j+1)-1` and `o | A_j`. So `p_j<=o<p_(j+1)`
for all `j`, which is impossible around a cycle.

**Iteration.** We maintain, for some generators `g_j`, an integer
`a_j>=1` and a linear bound `delta_j>=||g_j^(a_j)-1||_2`. Start with
`a_i=m`, `delta_i=tau`. Now visit `j=i,i+1,i+2,...` cyclically. At `j`
with `a_j` defined, put `b=2^(a_j)-1` and `beta=(2^(a_j)-1)eps_j+2delta_j`.
By Lemma A this bounds `||g_(j+1)^b-1||_2`. If `a_(j+1)` is undefined,
set `(a_(j+1),delta_(j+1))=(b,beta)`. Otherwise replace `a_(j+1)` by
`gcd(a_(j+1),b)` and `delta_(j+1)` by the Lemma B bound. Every quantity
stays a linear bound.

After the first three visits all four `a_j` are defined. Each later
visit replaces some `a_(j+1)` by a divisor. A strictly smaller divisor
can occur only finitely often, since the `a_j` are positive integers. So
after finitely many visits a full round leaves every `a_j` unchanged, and
then `a_(j+1) | 2^(a_j)-1` for all `j`. By Higman's lemma all `a_j=1`.
The number of visits and all constants depend only on `(m,i)`, since the
iteration uses only these integers and not the tuple. Therefore
`||g_0-1||_2<=L` for a linear bound `L=sum_j c_j eps_j+c tau` (Lemma C is
not even needed once `a_0=1`).

Cauchy--Schwarz gives
`e(g_0)<=(sum_j c_j^2+c^2)(sum_j e(r_j)+e(g_i^m))`, so
`K_(m,i)=sum_j c_j^2+c^2`.

Remarks. The constants are of tower type in `m`. For instance, `m=3` at
`i=1` passes through `a_2=7`, `a_3=127` and `a_0=2^127-1`. Using torsion on
both odd generators avoids the tower. That is the explicit 25397 of
higman-order-three-torsion-ratio-bound. The whole argument happens inside
one tracial algebra, so it holds in every dimension and in ultraproducts.
