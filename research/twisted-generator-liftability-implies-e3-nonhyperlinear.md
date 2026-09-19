---
rg: 2
id: twisted-generator-liftability-implies-e3-nonhyperlinear
kind: claim
title: Twisted-generator ucp liftability forces the alpha-fibre to have no matricial model, hence the Deligne cover is non-hyperlinear
artifacts:
  - research/artifacts/lifting-program-2026-08-21.md
distinct_from:
  maslov-sector-tracial-generator-ucp-liftability: that is the open liftability assertion TGL1; this proves TGL1 is not a weak stepping stone but goal-hard — it is equivalent to the alpha-fibre having no tracial matricial model at all, and implies non-hyperlinearity of the Deligne cover.
  deligne-sector-gap-is-exactly-nonhyperlinearity: that identifies the Maslov defect gap and the one-word collapse with non-hyperlinearity of the cover; this adds the LIFTING assertion to the same equivalence cluster through Stinespring dilation and the Kazhdan corner lemma.
  llp-non-rf-kazhdan-group-is-non-hyperlinear: that consumes the full local lifting property of a group algebra; this consumes only the fixed-generator, fixed-quotient liftability of one twisted fibre and reaches the same witness.
---

**THEOREM.**  Let `alpha` be a nontrivial mod-three Deligne multiplier of
`Gamma = Sp_4(Z)` and `A_alpha = C^*(Gamma; alpha)`.  The following are
equivalent:

```text
(1) TGL1 of maslov-sector-tracial-generator-ucp-liftability: every unital
    *-homomorphism Theta : A_alpha -> prod_omega M_(d_n) admits ucp maps
    phi_n : A_alpha -> M_(d_n) with Theta(u_s) = [(phi_n(u_s))] on the
    canonical generators;
(2) NO unital *-homomorphism A_alpha -> prod_omega M_(d_n) exists, for
    any dimension sequence and ultrafilter: no trace on A_alpha has
    matricially approximable GNS.                                  (TG1)
```

Moreover `(2)` applied to the canonical fibre trace of
`p_alpha L(E_3) p_alpha` gives: **TGL1 implies that Deligne's triple
cover `E_3` is not hyperlinear** — the goal witness.  (The converse
direction of the equivalence is vacuity: if no `Theta` exists, TGL1
quantifies over an empty set.)

**Mechanism** (`twisted-generator-liftability-proof`).  A ucp generator
lift Stinespring-dilates to a genuine `alpha`-projective unitary
representation `pi_n` of `Gamma`; the conjugation representation
`Ad pi_n` is an honest representation of the Kazhdan group `Gamma`
(the cocycle cancels), so the corner lemma
`kazhdan-almost-invariant-corner-near-invariant-projection` turns the
almost-invariant Stinespring corner into a NONZERO finite-rank
projection commuting with `pi_n(Gamma)`, i.e. a nonzero
finite-dimensional `alpha`-projective representation — which
`deligne-triple-cover-fd-central-invisibility` forbids.  So a lift can
never coexist with a `Theta`, and TGL1 can hold only vacuously.

**No QWEP backdoor.**  Two soft-looking shortcuts fail, in opposite
directions.  A GLOBAL ucp lift `A_alpha -> prod M_(d_n)` of some `Theta`
would exhibit the fibre as a ucp-retract of an injective von Neumann
algebra, giving it WEP; for the property (T) von Neumann fibre this
means hyperfiniteness — impossible.  And in the converse direction,
Connes embeddability of the fibre would give QWEP, but QWEP supplies no
LOCAL lifts either: `B(H)` has WEP yet fails the LLP (Junge--Pisier).
So if `E_3` is hyperlinear, the resulting `Theta`'s simply have no
generator lifts, which is exactly how the vacuity equivalence `(TG1)`
predicts the world looks on that side.  The peers' companion route
`brown-ucp-generator-lift-closes-maslov-gap` (TGL1 plus
`deligne-twisted-fibres-have-no-amenable-trace` gives the Maslov gap) is
the tracial packaging of the same mechanism: their no-amenable-trace
input is the Kirchberg-side face of the Deligne invisibility used here.

**Lane intelligence.**  TGL1 should therefore not be attacked as a
"strictly weaker lifting assertion": as stated it is at least as strong
as the goal.  What remains genuinely weaker-than-LLP territory is
liftability for the UNTWISTED fibre (`sp2g-z-full-c-star-algebra-has-llp`
and `sl3-z-weakly-ucp-stable`-type statements), where genuine
finite-dimensional representations exist and the corner argument
produces congruence representations instead of contradictions.
