---
rg: 2
id: o2-zp-cartan-fixing-all-primes-or-at-most-one
kind: claim
title: Cartan-fixing for order-p actions on O_2 holds at every prime or at most one, and any two primes decide the UCT problem
distinct_from:
  barlak-li-uct-iff-z2-z3-actions-fix-cartan: that characterizes Problem II through the primes 2 and 3; this allows any two distinct primes and adds that the set of primes where Cartan-fixing holds is all primes or has at most one element.
  coprime-uhf-stabilizations-detect-uct: that is the permanence theorem for one algebra and two coprime UHF factors; this transports it through Barlak--Li II Theorem 4.16 to automorphisms of O_2.
artifacts:
  - research/artifacts/stw-uct-per-prime-cartan-2026-09-12.md
---

**ESTABLISHED (derivation, this repository).**  For a prime `p` write `D_p` for:
every outer strongly approximately inner `Z_p`-action on `O_2` fixes some Cartan
subalgebra of `O_2` globally.

1. For any two distinct primes `p ≠ q`, `D_p` and `D_q` both hold if and only if
   every separable nuclear C\*-algebra satisfies the UCT.
2. Hence `{p prime : D_p}` is either the set of all primes or has at most one
   element.
3. If a separable nuclear `A` fails the UCT and `p^a · [id_A] = 0` in `KK(A, A)`
   for a prime `p`, then `D_r` fails at every prime `r ≠ p`.

Proof: `o2-zp-cartan-fixing-all-primes-or-at-most-one-proof`.

So a positive answer needs Cartan-fixing at any two primes, while one separable
nuclear algebra outside the UCT class forces order-`r` automorphisms of `O_2`
with no invariant Cartan subalgebra at all primes `r` except at most one.

**Credit.**  In crossed-product form, for pointwise outer locally
Kirchberg-representable actions, item 1 is Barlak--Szabó, Trans. Amer. Math. Soc.
369 (2017), arXiv:1403.7312, Theorem 4.17.  The Cartan form follows the proof of
Barlak--Li II Corollary 4.17, which states only the pair `2, 3`.  Items 2 and 3 are
immediate consequences, recorded without priority claim.
