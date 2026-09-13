---
rg: 2
id: hyperlinear-fp-infinite-simple-kazhdan-group
kind: claim
title: Some finitely presented infinite simple group with property (T) is hyperlinear, preferably sofic
distinct_from:
  hyperlinear-fp-infinite-simple-group: that asks for any finitely presented infinite simple hyperlinear group; this adds property (T), which removes the amenable-orbit and tree-splitting certificates that are live there.
  infinite-simple-kazhdan-hyperlinear-group: that is Pestov's Open Question 9.1, answered by a LEF group that is not finitely presented; this demands a finite presentation, for which LEF is impossible.
  kac-moody-lattice-is-non-hyperlinear-or-llp-failure: that is a proved dichotomy for the Caprace--Remy lattices; this is the existence question that a hyperlinear lattice would answer.
  fp-simple-nonsofic-group: that is the established nonsofic member of the same class of groups, the binary Leavitt unit group; this asks for the opposite approximation property in that class.
---

**OPEN.** There is a finitely presented infinite simple group `S` with Kazhdan's
property (T) that is hyperlinear. Preferred strengthening: `S` is sofic.

**Why it matters.**
- It is Pestov's Open Question 9.1 with a finite presentation added. The finitely
  generated case is answered by `simple-kazhdan-lef-group-from-minimal-subshift`, whose
  certificate is LEF. A finitely presented LEF group is residually finite, and an
  infinite simple group is not, so a witness here needs approximations that are not
  exact on any finite ball of relations.
- It answers `hyperlinear-fp-infinite-simple-group` (route
  `hyperlinear-fp-infinite-simple-group-via-kazhdan-witness`).
- `S` is not residually finite, so by `llp-non-rf-kazhdan-group-is-non-hyperlinear` a
  witness has `C*(S)` failing Kirchberg's local lifting property: a new LLP failure, in a
  group with no nontrivial finite-dimensional representation.

**Model test.** `SL_3(Z)` is sofic and Kazhdan, not simple. The subshift group is simple,
Kazhdan and sofic, not finitely presented. The binary Leavitt unit group is finitely
presented, simple and Kazhdan, and nonsofic (`fp-simple-nonsofic-group`), so only its
hyperlinear half is open. The trivial group is not infinite.

**Candidates recorded in this graph.**

| Group | fp, simple, (T) | Approximation status |
|---|---|---|
| Caprace--Remy lattices `Lambda_A(F_q)/Z` | `simple-kazhdan-kac-moody-lattices-exist` | open both ways |
| Titz Mite--Witzel kernels | `titz-witzel-simple-kazhdan-cat0-lattices-exist` | open both ways |
| binary Leavitt unit group | `leavitt-unit-group-finitely-presented`, `binary-leavitt-unit-group-is-simple`, `rank-twelve-leavitt-simple-non-mf` | nonsofic; hyperlinear open (`binary-leavitt-unit-group-hyperlinear`) |

## Attempts

- **LEF, marked limits, residual amenability.** Dead.
  - An fp LEF group is residually finite.
  - `fp-simple-groups-escape-soft-hyperlinear-permanence` kills marked limits and
    residual amenability.
- **Permanence certificates.** Dead as a source of a new witness.
  - The closure argument of `sofic-permanence-closure-omits-simple-fa-nonsofic-groups`
    uses nonsoficity only to put the base class inside `D_S` (groups with no copy of `S`).
    For `S` finitely presented, infinite, simple and Kazhdan, every LEF group and every
    amenable group already lies in `D_S`.
  - So subgroups, directed unions, extensions, graphs of groups and marked limits
    starting from LEF and amenable groups never produce a group containing `S`. Direct,
    wreath and graph products are iterated extensions and amalgams, so they are covered.
- **Amenable orbit full groups.** Dead: `kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`.
- **Stability shortcut.** Dead by hypothesis. An infinite sofic Kazhdan group is not
  permutation stable (Becker--Lubotzky), and an infinite hyperlinear one is not HS-stable
  (see `infinite-simple-kazhdan-hyperlinear-group`, Attempts).
  - Conversely, for fp simple `S`, one almost-homomorphism to symmetric groups that is not
    asymptotically trivial already makes `S` sofic: its ultraproduct is a nontrivial hence
    injective homomorphism into a universal sofic group. The Leavitt case of this is
    `binary-leavitt-unit-group-is-permutation-stable`.
- **Measure equivalence.** Open. By `paunescu-class-is-measure-equivalence-invariant`,
  either every lattice of `Aut(X_+) x Aut(X_-)` for a Kac--Moody twin building lies in
  Paunescu's class `𝒮` or none does. A lattice in `𝒮` has a sofic free action and is sofic.
  - Every lattice there is Kazhdan, so the seed would have to be a Kazhdan group all of
    whose p.m.p. actions are sofic.
  - None is recorded: `sl3z-admits-nonsofic-action` is open.
- **Kac--Moody lattices (lane ex-fp-kazhdan-kac-moody, 2026-09-13).** Live.
  - *Sources, read from the PDFs this date.* For the simply connected type-`(2,4,6)`
    group over `F_q`, the bound `q > 1764^3` of `simple-kazhdan-kac-moody-lattices-exist`
    drops to `q >= 4`:
    - Caprace--Thom arXiv:2606.27993v2, Proposition 4.1(1): type `(2,4,6)` with
      `q_min >= 3` gives (T) for the building completions.
    - Their Corollary 5.3: every invariant random subgroup of `Lambda/Z` is a convex
      combination of `delta_e` and `delta_(Lambda/Z)`.
    - Caprace--Remy arXiv:math/0607664v2, Theorem 20: `[Lambda,Lambda]/Z` is simple, and
      `Lambda = [Lambda,Lambda]` for `q > 3`.
    - Proof of their Corollary 21: finite presentation from Abramenko--Muhlherr 1997 once
      `q_min > 2`.
  - The approximate problem is a gauge problem over the Curtis--Tits triangle of finite
    groups `SL_2(q)^2`, `Sp_4(q)`, `G_2(q)` (to be landed as a finite gate).
- **Titz Mite--Witzel kernels.** Live: `titz-witzel-soficity-is-one-finite-csp`.
- **Leavitt unit group, hyperlinear half.** Live: `binary-leavitt-unit-group-hyperlinear`.
