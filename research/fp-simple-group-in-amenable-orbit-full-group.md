---
rg: 2
id: fp-simple-group-in-amenable-orbit-full-group
kind: claim
title: Some finitely presented infinite simple group acts nontrivially by bounded piecewise translations of an essentially free amenable measure-preserving action
distinct_from:
  fp-infinite-simple-amenable-group: That asks for an amenable finitely presented simple group; this asks only for a measure-preserving amenable-orbit realization, which is weaker (an amenable group realizes itself by its Bernoulli shift) and still gives soficity.
  hyperlinear-fp-infinite-simple-group: That is the existence root; this is a structural sufficient condition that gives the stronger conclusion, soficity, through amenable-orbit-full-group-subgroups-are-sofic.
  labbe-shift-derived-full-group-is-finitely-presented: That is finite presentation of one candidate; this is the class question, of which that candidate is the only live instance recorded.
---

**OPEN.** There are a countable amenable group `Lambda`, an essentially free
measure-preserving action of `Lambda` on a standard probability space `(X, mu)`,
a finitely presented infinite simple group `S`, and a homomorphism
`rho : S -> W(Lambda ~ X)` that is nontrivial on a set of positive measure.
Here `W(Lambda ~ X)` is the group of Borel bijections `g` with
`g(x) = c_g(x) x` for a Borel `c_g : X -> Lambda` of finite range.

**Why it matters.** Simplicity makes `rho` faithful modulo null sets, so
`amenable-orbit-full-group-subgroups-are-sofic` makes `S` sofic, hence hyperlinear.
That is `hyperlinear-fp-simple-via-amenable-orbit-full-group`. It needs no
amenability of `S`, so it is strictly easier to meet than
`fp-infinite-simple-amenable-group`.

**Model test.** The trivial homomorphism fails the nontriviality clause.
`D([[Z^2 ~ Omega_U]])` for Labbé's shift satisfies every clause except finite
presentation, which is open.

## Attempts

- **Groups containing Thompson's V.** Dead:
  `stabilizer-rigid-groups-avoid-amenable-orbit-full-groups`. The fixed-point
  character of a realization is trivial-plus-regular by Dudko--Medynets, the
  action is then free off its fixed points, and a free realization would make V
  amenable. This removes the Thompson, Higman--Thompson, Brin--Thompson and
  Röver--Nekrashevych groups, Matui's SFT full groups and the Leavitt unit groups,
  as far as they contain V.
- **Infinite simple Kazhdan groups.** Dead:
  `kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`. Følner indicators
  give almost invariant vectors on the orbit-fibred space, and invariant vectors
  force finite orbits. This removes the Kazhdan Kac--Moody lattices and the
  Titz Mite--Witzel kernels.
- **Minimal `Z`-subshifts, topological realizations.** Dead:
  `periodic-approximable-subshifts-host-no-fp-simple-group`.
- **Minimal aperiodic `Z^2` SFTs.** Live, and the only gate is finite presentation:
  `fp-simple-amenable-orbit-via-labbe-shift` needs
  `labbe-shift-derived-full-group-is-finitely-presented` and nothing else open.
  Unlike `fp-simple-amenable-via-labbe-shift-full-group`, it does not need
  `labbe-shift-derived-full-group-is-amenable`.
- **Kac--Moody lattices without (T).** Not excluded by the Kazhdan barrier. The
  Scope paragraph of the stabilizer-rigid claim applies to groups with only
  trivial ergodic invariant random subgroups. `caprace-thom-v2-leaves-km-character-rigidity-open`
  records such IRS rigidity for specified compact-hyperbolic Kac--Moody lattices,
  but whether those include the finitely presented simple family, and the
  measurable details of the IRS variant, were not checked.
- **Lattices in products of trees (Burger--Mozes, Rattaggi).** Not excluded: they
  have the Haagerup property, so the Kazhdan barrier does not apply, and no
  character or IRS classification for them is recorded here. A realization would
  give a character `g -> mu(Fix g)` below `1` off the identity, so a character
  rigidity theorem of type (CR) would kill them as it kills V.
- **Thompson's T and Lodha's finitely presented simple circle groups.** Not
  checked. They contain F, so the non-amenability step is available, but no
  character classification for them is recorded here.
- **Interval and polygon exchange groups.** Every countable group of them with
  translations in an essentially free countable abelian group lies in some
  `W(Lambda ~ X)`, so it is sofic. No finitely presented infinite simple subgroup
  is recorded, and none was searched for.
