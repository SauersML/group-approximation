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

2. **Annihilator symbols of prime order, detected by a Hochschild trace
   (2026-09-18, swarm-0917-w7-w7-z-follow).** *Dead as a route to refuting (M2).
   Attempt 1's symbols are trivial.*
   - **Idea.** Find elements `h_p` of `K_2(3,R)` whose images in the stable,
     central `K_2(R)` have order `p` for infinitely many primes `p`. The
     normal closure in `St_m(R)` of finitely many elements of `K_2(m,R)` maps
     onto a finitely generated subgroup of `K_2(R)`. So such `h_p` would show
     that `K_2(m,R)` is not finitely normally generated for any `m`, and would
     kill (M2).
     - The candidates are `h = <a,b> = [x_12(a), x_21(b)]` with `ab = ba = 0`,
       for example `a = x^i e x^j` and `b = x^k e x^p e x^l`, where
       `p ∤ j+k` and `p ∤ l+i`, so that `pb = 0`.
     - The detector is `Phi`: a ring map `R -> M_d(F_p[eps1,eps2]/(eps)^2)`,
       followed by the Dennis trace into `HH_2`, then the map to
       `Omega^2 (x) F_p = F_p eps1^eps2`. This sends `h` to
       `2(tr(D1a D2b) - tr(D2a D1b))`.
     - These finite rings are not of the form `M_d(Z/N)`, so Attempt 1's
       bound of order 2 does not apply to them.
   - **Proved (splitting criterion, in `St_3`).** Suppose `ab1 = 0` and
     `b2 a = 0`. Then `x_21(b1 b2) = [x_23(b1), x_31(b2)]`, and both factors
     commute with `x_12(a)`, so `[x_12(a), x_21(b1 b2)] = 1`. The same holds
     for `a = a1 a2` with `b a1 = 0` and `a2 b = 0`.
     - Hence Attempt 1's words `<u, r_n>` are trivial in `St_m(R)`: take
       `b1 = e` and `b2 = x^n e`, and use `ue = 0` and `x^n e u = 0`.
   - **Where every member dies (split-point orders).** Let `ab = ba = 0` and
     `b = b1 b2`. Put `c1 = a b1` and `c2 = b2 a`. The following hold:
     - `c1 b2 c1 = (ab) a b1 = 0` and `c2 b1 c2 = b2 (ab) a = 0`;
     - `1 + c1 b2 = 1`;
     - `(b2 a b1)^2 = 0`.

     So the Dennis–Stein identities apply:
     - (D3) `<a, b1 b2> = <c1, b2><c2, b1>`;
     - (D2) `<c, y>^q = <qc, y>` whenever `cyc = 0`.

     Therefore `h^(q1 q2) = 1`, where `q1` and `q2` are the additive orders of
     `c1` and `c2`. The same holds for factorizations of `a`.
     - For words, `q1` and `q2` are gcds of merged middle indices (the normal
       form of `counting-ring-rf-every-additive-order-proof`). They are not the
       index `p` in the middle of `b`.
     - In the family above, `q1 = j+k` and `q2 = l+i`, both prime to `p`,
       while `h^p = 1`. So `h = 1`.
     - The same holds for every symbol of word pairs of `e`-degrees
       `(1,2)` or `(2,1)`. There, `ord(A) = beta` is forced prime to both
       split orders by `AB = BA = 0`.
     - A sample of degree `(3,2)` survives one split with bound `p`, but dies
       at the next split with bound 2.
     - D2 and D3 are the standard Dennis–Stein relations. They are imported
       for noncommutative rings (Keune; Kolster, J. Algebra 1985) **without a
       verbatim citation**, so this kill is conditional on that import.
   - **Computation.**
     `experiments/counting-ring-steinberg-2026-09-17/phi_dennis_trace_scout.py`
     solves for the full tangent space of first-order deformations of
     block-shift base representations over `F_p`. It checks `ab = ba = 0` to
     first order, then computes the form `Phi`.
     - Result: `rank(Phi) = 0` in every case run. These were `p = 3, 5, 7`,
       `d <= 10` and random `e_0` for `a = ex` and `b = x e x^p e x^2`, plus
       `p = 3`, `d = 9` for `a = x^2 e x^2` and `b = x^3 e x^3 e x^3`.
     - This agrees with the kill.
   - **What this changes.** Annihilator symbols built from words carry only
     the torsion present at their split points. So "unbounded prime torsion in
     `K_2`" is not produced by symbols whose `p`-torsion sits in an unsplit
     middle index.
     - A refutation of (M2) still needs a symbol whose recursive split bounds
       all share a prime `p`, for infinitely many `p`, or the Nil-term
       computation.
     - (M1) is untouched.

