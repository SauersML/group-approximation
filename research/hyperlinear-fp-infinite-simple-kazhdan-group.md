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
| Titz Mite--Witzel kernels | `titz-witzel-simple-kazhdan-cat0-lattices-exist`; torsion-free, `cd = 2` | open both ways; no recorded nonsoficity certificate can refute: criterion and lamps (`vcd-two-groups-contain-no-kazhdan-commuting-pairs`), Kun--Thom doubles (`compressed-doubles-raise-cohomological-dimension`) |
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
  For IRS-rigid candidates the Haagerup extension is dead too:
  `irs-rigid-kazhdan-groups-avoid-haagerup-orbit-full-groups`.
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
  - *Explicit instance.* `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`: for the
    simply connected type-`(2,4,6)` group over `F_q`, the recorded bound `q > 1764^3` drops to
    `q >= 4` (Caprace--Thom Proposition 4.1(1) and Corollary 5.3; Caprace--Remy Theorem 20 and
    Corollary 21, read at source). These lattices are also IRS-rigid.
  - *Gate.* `km-246-lattice-is-sofic`, route `hyperlinear-fp-kazhdan-via-km-246-lattice`. By
    `almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial`, every almost action that is
    not asymptotically trivial is already a sofic approximation with free finite charts. In the
    recorded Levi form the charts are `T.SL_2(q)^2`, `T.Sp_4(q)`, `T.G_2(q)`.
  - *Barriers landed by this lane.*
    - `irs-rigid-kazhdan-groups-avoid-haagerup-orbit-full-groups`: no realization by bounded
      piecewise translations of a free action of a Haagerup group.
    - `compression-triples-avoid-proper-cat0-groups`: the compression certificate is vacuous in
      proper CAT(0) polyhedral groups whose finitely generated torsion subgroups are finite. This
      extends the `cd = 2` vacuity below to these lattices, which have infinite virtual
      cohomological dimension, conditional on a torsion hypothesis recorded there.
- **Titz Mite--Witzel kernels (lane ex-fp-kazhdan-titz-witzel, 2026-09-13).** Live, on two
  routes.
  - *Sofic form:* `hyperlinear-fp-kazhdan-via-titz-witzel-kernel`, gated by the
    three-permutation CSP `titz-witzel-soficity-is-one-finite-csp`.
  - *Hyperlinear form:* `hyperlinear-fp-kazhdan-via-mf-titz-witzel`. An MF residual is
    hyperlinear by `kazhdan-mf-hyperlinear-fragment`. This route reopened when
    `simple-kazhdan-groups-have-full-mf-radical` was refuted. Its failure for every residual is
    what `titz-witzel-exact-kazhdan-mf-radical-over-z` needs, so the MF question
    (`titz-witzel-residual-is-mf`) settles one of the two claims either way.
  - *What separates them from Khanh's group.* The Leavitt group is nonsofic through a compressed
    infinite Kazhdan subgroup with a commuting non-LEF partner, and it contains `V`, so its
    virtual cohomological dimension is infinite. The Kac--Moody lattices contain the finite
    subgroups `U_w` of unbounded order, so theirs is infinite too. The Titz Mite--Witzel residuals
    have `cd = 2`. There, by `vcd-two-groups-contain-no-kazhdan-commuting-pairs`, a commuting
    partner of an infinite Kazhdan subgroup is finite, and no infinite lamp group embeds. So they
    are the recorded candidates on which the compression and lamp certificates are vacuous.
    Kun--Thom doubles are excluded too: a double over a compressed Kazhdan subgroup has
    cohomological dimension at least three (`compressed-doubles-raise-cohomological-dimension`).
    The pairs themselves do occur in dimension two (`cd-two-group-with-infranormal-kazhdan-pair`),
    and their double is a finitely presented torsion-free nonsofic group of dimension exactly three
    (`fp-torsion-free-nonsofic-group-of-cd-at-most-three`). A nonsoficity proof for these kernels
    therefore needs a mechanism not yet recorded.
- **Leavitt unit group, hyperlinear half.** Live: `binary-leavitt-unit-group-hyperlinear`, via
  `hyperlinear-fp-kazhdan-via-leavitt-unit-group`.
- **Candidate scan beyond the recorded families (sk-fp-sofic-d, 2026-09-13; bounded).** No new
  family.
  - López Neumann, arXiv:2101.09071v2, Theorem 1.1 (read from the PDF): "There are infinitely many
    measure equivalence classes containing finitely presented, Kazhdan, simple groups. These groups
    are Kac-Moody lattices over finite fields with well-chosen non-affine Weyl groups."
    - His introduction lists the known infinite finitely presented simple groups as Burger--Mozes
      groups, non-affine Kac--Moody lattices and variants of Thompson groups.
    - For the measure-equivalence route this means the donor search splits into infinitely many
      classes. A donor must be Kazhdan, since (T) is a measure equivalence invariant, and must have
      the lattice's ℓ²-Betti profile up to proportionality (Gaboriau).
  - Amir--Lazarovich, arXiv:2605.09493 (abstract): simple uniform lattices in products of trees
    and two-dimensional Davis complexes of right-angled Coxeter groups. These complexes are CAT(0)
    cube complexes, so the lattices have the Haagerup property (Niblo--Reeves) and are not Kazhdan.
    They belong to `hyperlinear-fp-infinite-simple-group` only.
  - Chatterji--Kassabov, arXiv:2601.22907 (abstract): finitely presented Kazhdan groups with strong
    fixed-point properties, where "property (T) is added at the expense of weakening the simplicity
    requirement". So they are not candidates.
  - Search bound: two web queries and four arXiv abstract pages.
  - Details: `research/artifacts/sk-fp-sofic-d-candidates-and-interpolation-2026-09-13.md`.
