---
rg: 2
id: counting-steinberg-residual-finitely-normally-generated
kind: claim
title: For some m >= 4 the finite residual of St_m of the counting ring is the normal closure of finitely many elements
distinct_from:
  fp-rf-group-with-unbounded-prime-torsion: that is the target existence statement; this is one concrete sufficient hole about one explicit finitely presented Kazhdan group.
  counting-ring-steinberg-group-has-every-torsion-order: that establishes finite presentation, torsion of every order and the containment of the residual in K_2; this asks for finite normal generation of that residual.
---

**OPEN (2026-09-17, swarm-0917-w6-w6-z-last2).**

**Statement.** Let `R = R_count = Z<u,x,e | xu-ux-x, ue, eu>`. For some
`m >= 4`, let `G = St_m(R)`, and let `G_res` be the intersection of all
finite-index normal subgroups of `G`. Then `G_res` is the normal closure in `G`
of finitely many elements.

**What is known.** By `counting-ring-steinberg-group-has-every-torsion-order`:
- `G` is finitely presented and has property (T);
- `G_res <= K_2(m, R) = ker(G -> E_m(R))`;
- `G / G_res` is residually finite and has elements of every finite order.

So this claim is exactly what the route
`unbounded-prime-torsion-via-counting-ring-steinberg` still needs.

**Sufficient mechanisms.** Each can fail independently of the other.
- **(M1) `St_m(R)` is residually finite.** Then `G_res = 1`, and `G` itself is
  the example.
- **(M2) `K_2(m, R)` is finitely normally generated in `G`.** Then
  `E_m(R) = G / K_2(m,R)` is finitely presented. It is residually finite by (C3)
  of `counting-ring-is-residually-finite-with-every-additive-order`, and it
  contains `1 + r_n E_12` of order `n`. (M2) holds if `E_m(R)` has a finite
  presentation, for example relative to the Steinberg relations.
- Anything in between also works: finitely many elements of `K_2(m,R)` whose
  normal closure contains `G_res`, with the quotient residually finite.

**Candidate elements of `K_2(m, R)`.** For `a, b` in `R` with `ab = ba = 0`, the
words `[x_12(a), x_21(b)]` (Dennis–Stein type) lie in `K_2(m, R)`. They map to 1
in `E_m(R)` because `1 + aE_12` and `1 + bE_21` commute when `ab = ba = 0`.

Natural sources:
- `a = u`, `b = r_n`;
- `a = r_n`, `b = r_{n'}`, whenever the products vanish in `R`.

A priori infinitely many of these are needed, one family per `n`. It is not known
whether finitely many of them normally generate the rest, or whether they die in
every finite quotient.

**Constraints and warnings.**
- Unstable centrality of `K_2(m,R)` in `St_m(R)` is not known for noncommutative
  `R`. Nothing here assumes it.
- Stably, Waldhausen's splitting for tensor rings suggests that `K_2(R)` is
  `K_2(U)` plus Nil-type terms built from the torsion bimodule
  `M = (+)_j (Z/j) x^j`. Those terms may be infinitely generated. This is
  unverified and is a warning sign for (M2), though not for (M1) or the claim
  itself.
- The restricted-product obstruction of attempt 6 in
  `fp-rf-group-with-unbounded-prime-torsion` gives no contradiction here. The
  group `G / G_res` is not built as a restricted product over the torsion
  orders.

## Attempts

1. **Congruence detection of `K_2` (2026-09-17, swarm-0917-w6-w6-z-last2).**
   *Inconclusive; deferred.*
   - **Idea.** Detect nontrivial elements of `K_2(m,R)` by pushing them into
     `St_m(S)` for finite quotient rings `S`, using the maps `rho_{N,n,P,Q}` of
     `counting-ring-rf-every-additive-order-proof`. This would attack (M1).
   - **Where it stops.** For `S = End_{Z/N}(V) = M_d(Z/N)` we have
     `St_m(S) = St_(md)(Z/N)`. For `md >= 3`, surjective stability over the
     semilocal ring `Z/N` gives `K_2(md, Z/N) = K_2(Z/N)`. That group is `Z/2`
     when `4 | N`, and 0 otherwise.
   - **Consequence.** The Dennis–Stein words `<u, r_n>` map into a group of
     order at most 2 in every such congruence quotient. So congruence quotients
     through these matrix representations cannot certify (M1) for infinitely
     many independent symbols. A proof of (M1) needs finite quotients of `G` that
     do not factor through `St_m` of a finite ring, or a proof that those symbols
     are trivial in `St_m(R)` itself.
   - **Not attempted.** Deciding (M2) by computing Waldhausen's Nil terms for
     `T_U(B)`.

