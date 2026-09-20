---
rg: 2
id: pu-ultraproduct-normal-subgroup-lattice-is-not-distributive
kind: claim
title: A bounded-rank determinant charge makes the normal subgroup lattice of an unbounded-rank ultraproduct of projective unitary groups non-distributive, refuting Stolz--Thom Theorems 4.16 and 4.20, and it is invisible to the width of a simple group
distinct_from:
  kl-kernel-lies-in-the-compact-unitary-width-radical: that identifies the width radical with a common kernel into quotients of algebraic ultraproducts of U(d); this describes those quotients, showing they are not classified by eigenvalue profiles, and shows the extra invariant cannot separate an element of a simple group.
  classical-unitary-ratio-witnesses-amplify-to-metric-models: that kills the operator, Hilbert--Schmidt and rank lengths as witnesses of unbounded width; this is about the whole eigenvalue profile and about a non-length invariant, the charge, on the bounded-rank part.
  thompson-v-has-unbounded-compact-unitary-relator-width: that is the V width statement; this gives a profile criterion that implies it and explains why a profile criterion cannot be sharp for general groups.
  thompson-v-has-bounded-compact-unitary-relator-width: that is the opposite V width statement, still open; this kills the route to it through the Stolz--Thom classification of normal closures.
artifacts:
  - research/pu-ultraproduct-lattice-not-distributive-proof.md
---

**ESTABLISHED** (route `pu-ultraproduct-lattice-not-distributive-proof`; lane
swarm-0917-w23-w23-nh-break, belief breaker, reframing; unreviewed).

**Setting.**
- `u` is a non-principal ultrafilter and `n_i -> infinity` along `u`.
- `G = prod_u PU(n_i)` is the *algebraic* ultraproduct, the setting of Stolz--Thom (arXiv:1207.0977v3, PLMS 108 (2014)).
- The *projective rank* of `x in PU(n)` is `pr(x) = min { rk(xt - 1) : xt a lift of x in U(n) }`.
- `B` is the set of `[x_i] in G` with `sup_i pr(x_i) < infinity` on a `u`-large set. It is a normal subgroup of `G`.
- `*S1 = prod_u S^1` is the algebraic ultrapower of the circle group.

## Theorem

**(A) Charge.**
- For `x = [x_i] in B`, let `xt_i` be the lift with `rk(xt_i - 1) <= r`. It is unique once `n_i > 2r`.
- Define `chi(x) = [det xt_i] in *S1`.
- `chi : B -> *S1` is a surjective homomorphism, and `chi(g x g^-1) = chi(x)` for every `g in G`.
- So for every subgroup `A <= *S1`, the set `N_A = chi^-1(A)` is a normal subgroup of `G`.
- `A -> N_A` is a lattice embedding of the subgroup lattice of `*S1` into the normal subgroup lattice of `G`. It
  preserves both `cap` and products.

**(B) Non-distributivity.**
- Let `lambda = e^i` and `mu = e^(i sqrt 2)` be constant sequences. Put `A_1 = <lambda>`, `A_2 = <mu>` and
  `A_3 = <lambda mu>`.
- Then `N_(A_1) cap (N_(A_2) N_(A_3)) = N_(A_1)`, while `(N_(A_1) cap N_(A_2)) (N_(A_1) cap N_(A_3)) = N_1` is strictly smaller.
- So the lattice of normal subgroups of `G` is **not distributive**. This is false:
  - Stolz--Thom Theorem 4.20;
  - the unbounded-Lie-type clause of their Main Theorem 5.1(1), verbatim "The lattice N of normal subgroups of G is
    distributive.".

**(C) Profiles do not classify normal closures.** Let `p = diag(lambda-bar, 1, ..., 1)` and `q = diag(mu-bar, 1, ..., 1)` in
every `PU(n_i)`.
- Their Stolz--Thom profiles `F_p` and `F_q` are equivalent, so `p ≼ q` and `q ≼ p`.
- But `p` is not in `N(q)`, the normal closure of `q`, and `q` is not in `N(p)`.
- So Stolz--Thom Theorem 4.16 ("g ≼ h is equivalent to g ∈ N(h)") fails in the direction `≼ => in N(h)`. The direction
  `in N(h) => ≼` is their Proposition 4.13.
- This is the ultraproduct form of Dowerk--Thom Remark 5.3, which refutes the finite Lemma 4.15.

**(D) Profile necessary condition for width** (Dowerk--Thom Proposition 4.8, cited verbatim in the route).
- Let `ell_t(x) = inf_(|z|=1) mu_t(1 - z x)` on `U(d)`.
- If `a(U) in Cons_K(R(U))`, then `ell_(K t)(a(U)) <= K max_(r in R) ell_t(r(U))` for all `t >= 0`.
- So a *profile witness* for every `K` implies unbounded width. A profile witness is a pair `U`, `t` with
  `ell_(Kt)(a(U)) > K max_r ell_t(r(U))`.

**(E) The charge is invisible to simple groups.**
- Let `Gamma = <S | R>` be non-abelian simple, `1 != a in Gamma`, and let `phi : F(S) -> G` be an ultraproduct of
  tuples with `phi(R) subset B` and `phi(a) in B`.
- Put `A = <chi(phi(r)) : r in R>`. Then `chi(phi(a)) in A`.
- The charge constrains `a in N(phi(R))` only when `N(phi(R)) subset B`, that is, when `phi(R) subset B`.
- So charge compatibility between `a` and the relators can never witness unbounded width of a simple group. This covers
  Thompson's V.

## What this changes

- **A published classification is false, not just unproved.**
  - The following sources flag Stolz--Thom Section 4 as flawed and Theorem 4.20 as open:
    - Schneider--Thom (arXiv:1709.06286): "The statement of [3, Theorem 4.20] should be considered as open problem at
      the moment.";
    - Thom's survey (arXiv:1712.01052);
    - Dowerk--Thom (arXiv:1506.08549), on Lemma 4.15.
  - (B) settles it negatively for every unbounded-rank ultraproduct of the groups `PU(n)`.
  - We found no earlier disproof in the sources checked. A thesis, "On ultraproducts of compact quasisimple groups"
    (d-nb.info/1232413577), was not read.
- **Class killed: profile-classification routes to either V width node.**
  - *The route.* The width radical is a common kernel into quotients `G/N` (`kl-kernel-lies-in-the-compact-unitary-width-radical` (B)).
    A tempting route decides `a in N(R)` inside `prod_u U(d_i)` by comparing eigenvalue profiles, as in Stolz--Thom
    4.16 or any rank-independent relative covering lemma that reads only `F` or `ell_t` data.
  - *Invariant.* The charge `chi` on the bounded-rank part.
  - *Death step.* The covering step, "profile domination implies membership with rank-independent `K`". The pair
    `p, q` of (C) has equivalent profiles and is separated by `chi`.
  - *What survives.*
    - Dowerk--Thom's corrected Theorem 1.1 has a `ceil(n/s)` factor, and the charge shows that factor is necessary.
    - So any bounded-width proof for V must either localize to blocks of dimension `O(rank)` or use simplicity.
    - By (E), simplicity does absorb the charge.
- **What is not changed.**
  - Neither V width node is decided.
  - (D) gives a checkable sufficient criterion for `thompson-v-has-unbounded-compact-unitary-relator-width`. By (E), the
    charge adds nothing for V.
  - The corrected conjecture left open for V is that profile domination alone decides the width radical of a simple group.
    It is recorded as an attempt on `thompson-v-has-bounded-compact-unitary-relator-width`.
