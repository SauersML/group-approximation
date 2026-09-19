---
rg: 2
id: clifford-cover-hilbert-embeddable-route
kind: route
title: Upgrade the Clifford cover's weak-soficity witness to a hyperlinear one
target: hyperlinear-nonsofic-group
requires: [kun-thom-clifford-cover-weakly-sofic, hilbert-embeddable-length-hyperlinearity, hilbert-embeddable-witness-for-kun-thom-wreath]
artifacts:
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
---

`kun-thom-clifford-cover-weakly-sofic` proves the Clifford cover
`E_S=Vtilde_S semidirect G` weakly sofic and **not sofic**.
`hilbert-embeddable-length-hyperlinearity` converts a weak-soficity witness
with conditionally negative definite lengths into a hyperlinear one.
`hilbert-embeddable-witness-for-kun-thom-wreath` is the open input: that the
witnesses for `W` or for its Clifford cover admit a uniform Hilbert
embeddable reparametrization.  Composing the three gives a hyperlinear
nonsofic group.

## Scope, which is load bearing

* The criterion is **sufficient only**.  A negative answer to the open input
  would not show `E_S` nonhyperlinear, since hyperlinearity is not known to
  return a weak-soficity witness.  This route can close the target but
  cannot refute it.
* The reparametrization is now **named**, so this scope condition is
  discharged rather than existential: `hilbert-embeddable-amplification`
  supplies `f(t)=1-e^(-t)`, which is Bernstein and so preserves conditional
  negative definiteness, reproduces Glebsky's cap `min{t,1}` within absolute
  constants so the cap is not load bearing, and whose powers `1-e^(-rt)`
  amplify a fixed positive separation to `1-o(1)` via
  `tr(rho^(tensor r))=(tr rho)^r`.  What remains open is only whether the
  witnessing lengths for this group admit it, not which `f` to use.
* **Proved constraint on the witness family.**  The finite groups carrying
  the witness cannot have a uniform character ratio bound
  `|chi(x)|/chi(1)<=c<1`: on such a family every Hilbert embeddable
  invariant length is uniformly bi-Lipschitz to the discrete length, so the
  witness would be an LEF witness and `E_S` would be LEF, hence sofic,
  contradicting `kun-thom-clifford-cover-weakly-sofic`.  The same applies to
  `W`.  Glebsky's groups are projections of closed subgroups of products of
  finite groups and carry large abelian quotients, so the constraint looks
  satisfiable, but it rules out quasirandom carriers.  It is a **filter, not
  a potential refutation**: the hoped-for upgrade of it into an obstruction
  was closed negatively by the lamp lane, since the character-gap interaction
  bounds only on the lamp subgroup and rigidity places the defect elsewhere.
* Lamp dilution is **not** a hurdle for this route and is not cited as one.
  The normalized separation of a two-site element is twice the fraction of
  the character orbit meeting exactly one of the two sites, which for a
  generic orbit tends to `1/2`, so the mark stays separated by an absolute
  constant however many sites there are; the `2/#A` decay came from
  averaging over singleton orbits.

## Consistency with the wall lane

The models produced here are `rho_n o phi_n` with `rho_n` an honest
representation of a finite group.  They are normalized-Hilbert--Schmidt
almost multiplicative, because `||rho_n(d)-1||_2^2=2(1-Re tr rho_n(d))->0`
for a defect element `d` of vanishing length, but they need **not** be
operator-norm almost multiplicative, since a unitary of trace near one may
have eigenvalues near `-1` on a corner of vanishing normalized rank.  That is
exactly the defect profile forced by `wall-models-avoid-norm-microstates`, so
this route and the relative-wall lane are consistent and describe the same
seam from opposite ends.
