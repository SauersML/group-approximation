---
rg: 2
id: non-rf-hyperbolic-via-sp21-congruence-property
kind: route
title: Under the congruence subgroup property every infinite hyperbolic filling of the lattice has finite profinite completion
target: non-residually-finite-hyperbolic-group
requires:
  - sp21-lattice-has-congruence-subgroup-property
  - normal-subgroups-of-arithmetic-lattices-are-congruence-open
  - relatively-hyperbolic-dehn-filling
  - hyperbolic-group-relative-to-maximal-elementary-subgroup
---

**Credit.** This implication is Lubotzky, *Some more non-arithmetic rigid
groups*, Contemp. Math. 387 (2005), arXiv:1105.4785, §4, Remark 4.2: "If there
is one such uniform lattice L satisfying CSP, then there exists a hyperbolic
group without any finite index subgroup". lit-scout-2 read it from the PDF on
2026-09-12. The argument below is an independent write-up of the same
mechanism. No novelty is claimed.

Let `Γ` be the lattice with the congruence subgroup property.  It is cocompact
in `Sp(2,1)`, so it is non-elementary hyperbolic (Švarc--Milnor), and torsion-free.

*Two independent elements.*  Take `g != 1`; torsion-free makes `E(g) = <g_0>`
infinite cyclic.  Strong approximation gives a prime `𝔭` with
`Γ ->> G(O/𝔭)`, a non-cyclic finite group.  A finite group is never the union
of the conjugates of a proper subgroup, so some element avoids every conjugate
of the image of `<g_0>`.  Any lift `h in Γ` is nontrivial, of infinite order,
and not conjugate into `E(g)`.

*The filling.*  Osin's Corollary 1.7 (quoted in the citation route, stated for
any relatively hyperbolic structure) applied twice makes `Γ` hyperbolic relative
to `{1, E(g), E(h)}`.  Fill `N = <g^n>` in `E(g)` and nothing else, for `n` so
large that `N` avoids the finite set of `relatively-hyperbolic-dehn-filling`.
The quotient `Q_n = Γ/<<g^n>>` is hyperbolic (its peripherals are finite or
`Z`), and `E(h) ≅ Z` injects, so `Q_n` is infinite.

*Finite profinite completion.*  `M = <<g^n>> != 1`, so its closure in the
congruence completion `Γ̄` has finite index
(`normal-subgroups-of-arithmetic-lattices-are-congruence-open`).  With finite
congruence kernel `C`, the closure of `M` in `Γ̂` maps onto that closure, so it
has finite index in `Γ̂`.  Every finite quotient of `Q_n` factors through
`Γ̂/closure(M)`, so `Q_n` has only finitely many finite quotients.  Being
infinite, `Q_n` is not residually finite.  `QED`
