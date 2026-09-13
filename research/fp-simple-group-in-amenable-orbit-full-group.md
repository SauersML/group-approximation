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
- **Aperiodic tiling full groups with an invariant measure.** Live, with two named
  instances. Each is gated only by finite presentation, and neither needs amenability.
  - Labbé's Wang shift: `fp-simple-amenable-orbit-via-labbe-shift` needs
    `labbe-shift-derived-full-group-is-finitely-presented`. Unlike
    `fp-simple-amenable-via-labbe-shift-full-group`, it does not need
    `labbe-shift-derived-full-group-is-amenable`.
  - The Penrose tiling group of Chornyi--Juschenko--Nekrashevych, which is the full
    group of a free translation action of `Z^2 ⊕ Z/5` on a cut torus:
    `fp-simple-amenable-orbit-via-penrose-group` needs
    `penrose-derived-full-group-is-finitely-presented`.
  - **Expert heuristic against this gate.** Nekrashevych, arXiv:2509.05524, line
    3362: "Full groups of shift-invariant groupoids, on the other hand, are rarely
    finitely presented." Every finite-presentation theorem found for full groups
    (Matui, Li, Nekrashevych, Belk--Bleak--Matucci--Zaremsky) uses compression,
    which an invariant measure of full support forbids.
- **IRS-rigid non-amenable groups.** Dead:
  `irs-rigid-nonamenable-groups-avoid-amenable-orbit-full-groups`. A realization free
  off its fixed points forces amenability, and ergodic decomposition turns IRS
  rigidity into that freeness. So a non-amenable witness must be a finitely presented
  infinite simple group with a **nontrivial ergodic invariant random subgroup**.
  - `caprace-thom-v2-leaves-km-character-rigidity-open` records IRS rigidity for
    specified compact-hyperbolic Kac--Moody lattices. Those are excluded with or
    without (T). Whether that class contains the finitely presented simple
    Caprace--Rémy lattices was not cross-checked.
  - Both live candidates below do have nontrivial IRSs: stabilizers of random points
    of their non-free measure-preserving Cantor actions.
- **Lattices in products of trees (Burger--Mozes, Rattaggi).** Not excluded: they
  have the Haagerup property, so the Kazhdan barrier does not apply, and no
  character or IRS classification for them is recorded here. A realization would
  give a character `g -> mu(Fix g)` below `1` off the identity, so a character
  rigidity theorem of type (CR) would kill them as it kills V.
- **Thompson-like groups that need not contain V.** Dead:
  `no-proper-character-groups-avoid-amenable-orbit-full-groups`.
  - It covers every alternating full group of a minimal, purely infinite, essentially
    principal Cantor groupoid, through Gardella--Tanner's corollary that such groups have
    no proper characters.
  - It covers every simple non-amenable group with a Dudko--Medynets compressible action.
  - It covers Thompson's `T`, given its classical simplicity, through Dudko--Medynets
    Theorem 2.10 with `R = F'`.
- **Lodha's finitely presented simple circle group `S`.** Dead, given simplicity of `T`.
  `S` contains `T`: the simplicity proof in arXiv:1710.06220 (TeX lines 1501--1504) runs
  inside `S` and concludes "`T∩N≠∅`. Since `T` is simple, it follows that `T<N`" for a
  normal subgroup `N` of `S`. A nontrivial realization of the simple group `S` restricts
  to a nontrivial realization of `T`, which item 5 of
  `no-proper-character-groups-avoid-amenable-orbit-full-groups` excludes.
- **Interval and polygon exchange groups.** Every countable group of them with
  translations in an essentially free countable abelian group lies in some
  `W(Lambda ~ X)`, so it is sofic. No finitely presented infinite simple subgroup
  is recorded, and none was searched for.
