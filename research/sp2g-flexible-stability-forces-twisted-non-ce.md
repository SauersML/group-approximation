---
rg: 2
id: sp2g-flexible-stability-forces-twisted-non-ce
kind: claim
title: Flexible HS-stability of a Kazhdan group forces almost-trivially twisted group algebras to be non-Connes-embeddable
distinct_from:
  dogon-sp2g-weak-ucp-nonhyperlinear: that is Dogon Corollary 1.9, concluding non-hyperlinearity of Deligne's extension; this is Dogon's criterion Theorem 3.1 in contrapositive form, concluding non-Connes-embeddability of the twisted algebras themselves, which is the content any stability proof must contain.
  deligne-sector-gap-is-exactly-nonhyperlinearity: that is an equivalence for the finite mod-three Deligne triple cover of Sp_4(Z); this concerns almost-trivial circle-valued twists of an arbitrary Kazhdan group and a stability hypothesis.
  effective-twisted-factor-existence-is-fp-nonhyperlinearity: that identifies existence of a non-Connes-embeddable twisted factor with finitely presented non-hyperlinearity; this derives such non-embeddability from weak ucp-stability, so it feeds that equivalence.
  non-rf-kazhdan-weak-ucp-iff-non-hyperlinear: that concerns NON-residually-finite Kazhdan groups, where weak ucp-stability is non-hyperlinearity; this applies to residually finite Kazhdan lattices such as Sp_2g(Z), through their almost-trivial twists.
---

**THEOREM (Dogon arXiv:2211.10492v3, Theorem 3.1, in contrapositive form;
read from the PDF on 2026-09-12).**  Let `Gamma` be a countable group with
property (T) that is weakly ucp-stable, for instance flexibly HS-stable.
Let `c_n in Z^2(Gamma, T)` be 2-cocycles such that

1. each class `[c_n] in H^2(Gamma, T)` is nontrivial, and
2. `c_n(g,h) -> 1` for all `g,h in Gamma`.

Then the twisted group von Neumann algebra `L_(c_n)(Gamma)` is not Connes
embeddable for all but finitely many `n`.

Proof.  If infinitely many `L_(c_n)(Gamma)` were Connes embeddable, the
subsequence along those `n` would satisfy conditions (1)--(3) of Dogon's
Theorem 3.1, which then says `Gamma` is not weakly ucp-stable.  That is a
contradiction.  Flexible HS-stability implies weak ucp-stability by the
immediate direction of `kazhdan-weak-ucp-stability-is-flexible-stability`.

Dogon's Theorem 3.1, verbatim: "Let Gamma be a countable property (T)
group. Assume there exists a sequence of 2-cocycles c_n in Z^2(Gamma,T)
with the following properties: (1) For each n, the cohomology class
[c_n] in H^2(Gamma,T) is nontrivial. (2) For all g,h in Gamma,
c_n(g,h) -> 1. (3) For all n, the twisted group von Neumann algebra
L_(c_n)(Gamma) is Connes embeddable. Then Gamma is not weakly
ucp-stable."  The proof uses Proposition 3.2 (weak ucp-stability with
values in the matrix ultraproduct), a dilation theorem, and the
Nicoara--Popa--Sasyk characterization of property (T).

**Use for `Sp_(2g)(Z)`.**  Here the cocycles come from the infinite cyclic
Deligne/Maslov extension `1 -> Z -> Gamma~ -> Sp_(2g)(Z) -> 1` composed
with characters of `Z` tending to 1.  Dogon's proof of Corollary 1.9 feeds
this extension to Theorem 1.6, whose proof produces such nontrivial
almost-trivial twists; this node uses that at statement level and does not
re-derive Dogon's Section 7 cohomological lemmas.  Consequences:

- **Refutation test.**  A Connes embedding of the twisted algebras along
  any such sequence refutes `sp2g-z-flexibly-hs-stable`.
- **Strength.**  Stability proves non-Connes-embeddability of the twisted
  algebras, and by `effective-twisted-factor-existence-is-fp-nonhyperlinearity`
  that already gives a non-hyperlinear group.  The stability hypothesis is
  not weaker than the goal on this sector.

DERIVATION
sp2g-flexible-stability-twisted-non-ce-citation
