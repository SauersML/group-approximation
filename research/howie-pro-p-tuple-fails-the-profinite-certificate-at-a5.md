---
rg: 2
id: howie-pro-p-tuple-fails-the-profinite-certificate-at-a5
kind: claim
title: Howie's pro-p tuple is not a near-miss for non-weak soficity, since its presented group is a perfect central extension of A_5
distinct_from:
  glebsky-rivera-w-sofic-criterion: that is the closure criterion for weak soficity; this kills the one explicit tuple the corpus had proposed as the best candidate certificate, at a single finite quotient of order 60.
  literal-mark-conjugacy-width-unbounded: that shows the non-MF group's mark has unbounded relator width, a statement about infinitely many finite quotients of a non-residually-finite group; this shows Howie's tuple already fails in one finite quotient, because its presented group is finite.
  non-weakly-sofic-finitely-presented-reduction: that reduces existence of a non-weakly-sofic group to a finitely presented one; this records a necessary condition on the finite list and applies it to one tuple.
---

**ESTABLISHED.** In `F = <x, y>` put

```text
g_1 = x^-2 y^-3,     g_2 = x^-2 (xy)^5,     a = x y^2 .
```

Howie (Math. Z. 187 (1984) 25--27, as quoted by Glebsky--Rivera, J. Algebra 320
(2008), Section 2) shows `a not in N(g_1, g_2)`, while `a` lies in the pro-`p`
closure of `[g_1]^F [g_2]^F` for every prime `p`. The corpus records this tuple as
"the best known near-miss" for the profinite certificate of
`research/artifacts/non-weakly-sofic-word-certificate.md`, missing only the
non-nilpotent finite quotients. It misses much more.

**Theorem.**
1. `P = F / N(g_1, g_2) = <x, y | x^2 = y^-3 = (xy)^5>` is a perfect central
   extension of `A_5` by a cyclic group of order at most `2`. So `P` is `A_5` or
   `SL(2,5)`, of order at most 120.
2. The homomorphism `q : F -> A_5` with `q(x) = (1 2)(3 4)` and `q(y) = (1 3 5)`
   kills `g_1` and `g_2`, and `q(a)` is nontrivial.
3. So `q(a)` is not in `[q(g_1)]^(A_5) [q(g_2)]^(A_5) = {1}`, and certificate
   condition (2) fails at the finite group `A_5`.

**Necessary condition (general).** Any certificate `(g_1, ..., g_k; x)` must
have `x` in the finite residual of `F/N(g_1, ..., g_k)`. In a finite quotient
where every `g_i` dies, the product of their conjugacy classes is `{1}`. So the
presented group is not residually finite. Howie's presented group is finite,
so his tuple carries no profinite information.

**What survives.** Glebsky--Rivera's open question, whether a finite product of
conjugacy classes of a free group is profinitely closed, stands. What is gone is
the claim that a concrete rank-two, width-two candidate has been on the table
since 1984. No explicit candidate certificate is recorded anywhere in this graph.
A candidate must start from a finitely presented group that is not residually
finite, with the marked word in its finite residual.

Derivation: `howie-pro-p-tuple-fails-at-a5-proof`.
