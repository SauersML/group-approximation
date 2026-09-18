---
rg: 2
id: bounded-char-p-certificates-transfer-to-characteristic-zero
kind: claim
title: Bounded-size one-sided inverse pairs over F_p group algebras exist, over all groups at once, only for primes below a computable bound, so prime-by-prime stable-finiteness certificates need unbounded size
distinct_from:
  c-linear-sofic-iff-bounded-dimension-large-characteristic: that compares rank models of one group across characteristics and blocks Sylvester certificates for component (a); this bounds, uniformly over all groups, the primes at which bounded algebraic certificates for component (b) can exist.
  linear-sofic-group-algebra-is-stably-finite: that turns a one-sided inverse pair over F_p[G] into non-linear-soficity; this shows such pairs of any fixed size exist at only finitely many primes, over all groups together.
  root-splits-into-large-and-fixed-characteristic-witnesses: that proves a group outside L_inf is in only finitely many L_p; this is the algebraic analogue for certificates, uniform in the group, and it rests on Kaplansky's theorem in characteristic zero rather than on rank models.
  group-not-linear-sofic-in-any-positive-characteristic-exists: that is the open component (b); this is an obstruction on the size of its stable-finiteness certificates and settles nothing about existence.
artifacts:
  - research/bounded-char-p-certificates-transfer-proof.md
---

**ESTABLISHED (2026-09-17, lane `sw-070`, unreviewed)** by `bounded-char-p-certificates-transfer-proof`.

**Setting.** A *`(k, m)`-pair over `F[G]`* is a pair `a, b` in `M_k(F[G])` with `ab = 1` and `ba != 1`, where each of
`a` and `b` is supported on at most `m` group elements. A *table of size `m`* is the partial multiplication table of
an `m`-element subset `W` of a group, with the identity marked. Windows, models and separation `1/4` are as on
`root-splits-into-large-and-fixed-characteristic-witnesses`.

**Theorem.**
1. **Uniform Kaplansky prime bound.** For all `k, m >= 1` there is `p_K(k, m)` such that for every prime
   `p > p_K(k, m)`, every field `F` of characteristic `p` and every group `G`, `M_k(F[G])` has no `(k, m)`-pair.
   - The function `p_K` is computable: the bound is read off a formal proof, which exists by the completeness theorem.
   - Equivalently, in the space of marked groups, the clopen set of groups with a pair of size `k` supported in the
     ball of radius `r` over `F_p` is empty once `p > p_K(k, |B_r|)`.
2. **Uniform window bound.** For every `m` and `eps > 0` there is `p_*(m, eps)` such that every table of size `m`
   that has a complex `(W, eps)`-model has a model over `F_p` for every `p > p_*(m, eps)`.
   - Hence, if a group has a table of size `m` with no `(W, eps)`-model over `F_p` for infinitely many `p`, it is
     not `C`-linear sofic.
3. **Consequences for component (b).**
   - Let `(G_p, a_p, b_p)` be any prime-by-prime family of stable-finiteness certificates, with `(a_p, b_p)` a
     `(k_p, m_p)`-pair over `F_p[G_p]`. Then `p <= p_K(k_p, m_p)` for every `p`. So `max(k_p, m_p) -> infinity`,
     and no bounded family serves infinitely many primes.
   - This covers every certificate that ends in a matrix pair, including formal strict pairs
     (`formalizable-strict-pairs-certify-non-linear-soficity`) through the size of their linearization, and every
     uniform integral design, such as a fixed Leavitt-type pattern reduced mod `p`.
   - A witness of component (b) that is `C`-linear sofic must fail on tables whose size tends to infinity with `p`,
     at every fixed `eps`.
   - **Scope.** The economical form of the root (item 5 of `root-splits-into-large-and-fixed-characteristic-witnesses`)
     needs certificates only at the finitely many primes in `S(H)`. Bounded certificates there are not excluded. The
     obstruction kills only attacks on component (b) on its own that use a bounded pattern.

**Why it is an obstruction.** A single construction that gives a strict pair in every characteristic, with size
independent of `p`, would give a strict pair in characteristic zero. Kaplansky's theorem forbids that. So component (b)
cannot be proved by one bounded algebraic pattern read in all characteristics. Its certificates must grow with `p`,
at least as fast as the inverse of `p_K`.

**Calibration.**
- *Fixed characteristic.* The ultraproduct at a fixed prime has characteristic `p`, where stable finiteness is open.
  So the method proves nothing at a single prime, as it must.
- *Zero divisors.* Torsion gives zero divisors `(1 - g)(1 + g + ... + g^(n-1)) = 0` in every characteristic, including
  zero. The transfer is consistent with this, since it only transfers statements that are false in characteristic zero.
- *Sofic groups.* Their group algebras are stably finite in every characteristic (Elek--Szabo), so item 1 is vacuous
  for them.

**Credit.** Kaplansky's stable finiteness in characteristic zero, Łoś's theorem and the Chevalley spreading-out
(`c-linear-sofic-iff-bounded-dimension-large-characteristic`) are classical. The compactness transfer is standard
model theory, and experts may know item 1. Item 2 is only the form of (i) implies (iii) of
`c-linear-sofic-iff-bounded-dimension-large-characteristic` made uniform over the finitely many tables of size `m`. The novelty check was bounded; the contribution here is its use as a size
obstruction for component (b).
