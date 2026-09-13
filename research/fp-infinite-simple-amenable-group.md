---
rg: 2
id: fp-infinite-simple-amenable-group
kind: claim
title: An infinite simple amenable group can be finitely presented
root: true
distinct_from:
  hyperlinear-fp-infinite-simple-group: That asks for a finitely presented infinite simple group which is hyperlinear. This asks for one which is amenable, which is stronger, since amenable groups are hyperlinear.
artifacts:
  - research/artifacts/fp-simple-amenable-full-groups-2026-09-12.md
---

**OPEN.** There is a finitely presented, infinite, simple, amenable group.

**Status.** The sources were read from arXiv TeX on MSI; see the artifact,
Section 1.
- The finitely generated version is Kourovka Problem 15.5 (de la Harpe, "well-known
  problem"). Juschenko--Monod answered it with `D([[phi]])` for minimal
  subshifts `phi` (arXiv:1204.2132).
- Matui (arXiv:math/0404117, Theorem 5.7) shows those groups are never finitely
  presented, and so do Grigorchuk--Medynets (arXiv:1105.0719) through LEF.
- The Kourovka source contains no finitely presented version of the question.
- We found no written statement of this question. Who asked it, and where, is
  not recorded, and the web search budget ran out before a wider search.
- Every finitely presented infinite simple group recorded in this graph or in
  the sources above is non-amenable. The Thompson-like families, the SFT full
  groups and the Leavitt unit groups contain `V`. Torsion-free lattice examples
  such as the Burger--Mozes groups contain `F_2`.

**Why it matters.** An example would be hyperlinear and sofic, so it would
answer `hyperlinear-fp-infinite-simple-group` through
`hyperlinear-fp-simple-via-amenable-example`. It would also be a finitely
presented infinite simple group with no free subgroups.

## Attempts

- **Compressible or Thompson-like hosts.** Dead.
  `amenable-full-group-forces-invariant-measure`: if a group realizing the
  moving bisections of a minimal groupoid is amenable, the groupoid carries an
  invariant probability measure. So a nonempty clopen set holding two disjoint
  copies of itself makes `[[G]]` and `D([[G]])` non-amenable. This covers one-sided
  irreducible SFT groupoids (Matui's finitely presented simple groups) and every
  host containing `V`.
- **Full groups of minimal `Z`-subshifts.** Dead for every finitely generated
  subgroup, by `periodic-approximable-subshifts-host-no-fp-simple-group`. This
  covers the Juschenko--Monod groups and Nekrashevych's simple periodic groups,
  which embed there (arXiv:1601.01033, line 138). Residually finite minimal
  actions are dead through Xin Ma's LEF theorem (arXiv:2209.00580, Theorem C).
- **SFT neighbourhoods over general groups.** Partial, live.
  `fp-subshift-full-group-subgroups-extend-to-sft`: a finitely presented subgroup
  of the full group of a free subshift extends isomorphically to an SFT
  neighbourhood. If the subgroup is infinite and simple, its generators fix
  every finite orbit there.
  - Survivors (S1): free subshifts over amenable groups that are not virtually
    cyclic, such as `Z^2`, sitting inside SFTs with no moved finite orbits.
    Model case: a minimal aperiodic `Z^2` SFT. Neither the existence of such an
    SFT nor the amenability of its full group was checked.
  - Survivors (S2): non-free coding factors and non-expansive groupoids, for
    example the recurrent groupoids of Juschenko--Nekrashevych--de la Salle.
    Theorem 2 of the artifact does not reach these.
- **Forcing `X` itself to be an SFT when `Gamma = Alt(Lambda ~ X)`.** Plausible,
  through universal commutator identities for cylinder 3-cycles, but the
  disjointness bookkeeping for general `Lambda` was not carried out. See the
  artifact, Section 4.
- **Minimal aperiodic `Z^2` SFTs (case S1).** Live, and a concrete candidate is
  wired. The details are in `research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md`.
  - **Existence.** Such SFTs exist: `minimal-aperiodic-wang-shift-exists`
    (Labbé, arXiv:1802.03265, Theorem 1).
  - **The candidate is f.g., infinite and simple.** `D([[Omega_U]])` is, by
    `minimal-z2-subshift-derived-full-groups-are-fg-simple`
    (Chornyi--Juschenko--Nekrashevych, Matui, Nekrashevych).
  - **Every recorded obstruction fails:**
    `labbe-shift-derived-full-group-escapes-known-obstructions`.
    - Compressibility fails because of a full-support invariant measure.
    - The SFT neighbourhood can be `Omega_U` itself.
    - By `sfts-without-finite-orbits-are-not-residually-finite-actions`,
      there are no periodic approximations and no residually finite action.
  - **Suggested mechanism dead as stated.** The idea was that finite
    presentation forces periodic points. It cannot work through the extension
    theorem, since the SFT neighbourhood can be `Omega_U`, which has no finite
    orbit.
  - **Route.** `fp-simple-amenable-via-labbe-shift-full-group` needs the two
    open claims `labbe-shift-derived-full-group-is-amenable` and
    `labbe-shift-derived-full-group-is-finitely-presented`.
  - **Contrasts.**
    - Elek--Monod (arXiv:1201.0257) give a different minimal `Z^2` system
      with `F_2` in its full group.
    - ChJN (arXiv:1602.04255, line 88) record amenable rank-2 interval
      exchange realizations as `Z^2` full groups. Whether those systems have
      periodic approximations, or are residually finite, was not checked.
    - The Penrose tiling group has the same profile, and its amenability is
      recorded open (ChJN line 95).
- **Groups acting on the circle, and periodic groups of the line (2026-09-13,
  z1-10-simple-amen-build).** Dead: `amenable-infinite-simple-circle-groups-fix-a-point`.
  An amenable infinite simple group acting faithfully on the circle fixes a point, so
  an example acting on a one-manifold acts on the line.
  - This removes Thompson's `T`, Lodha's circle group, and every infinite simple group
    of homeomorphisms of `R` commuting with `t -> t + 1` whose circle action has no
    global fixed point.
  - Hyde–Lodha's finitely presented simple `Q_2`, torsion-free and of type `F_∞`, is one
    of them and is not amenable (`hyde-lodha-periodic-simple-groups-are-not-amenable`;
    dead route `fp-simple-amenable-via-hyde-lodha-group`). It had escaped the earlier
    obstructions, since it contains no `V` and is not a lattice in a product of trees.
  - **Every one-manifold is dead.** `amenable-fg-simple-groups-are-not-left-orderable`,
    through Witte Morris's theorem (`amenable-left-orderable-groups-are-locally-indicable`):
    a finitely generated infinite simple amenable group is not left-orderable, so each
    of its actions on the line or the circle is trivial. This removes every
    finitely generated simple group of line homeomorphisms, with or without periodic
    structure, including Hyde–Lodha's groups from quasi-periodic labellings, and every
    group acting faithfully and orientation-preservingly on one orbit of a flow.
- **Interval exchange groups (2026-09-13, z1-10-simple-amen-build).** Dead:
  `fp-simple-groups-have-no-interval-exchange-action`. Finitely generated interval
  exchange groups are LEF by rational specialisation (`interval-exchange-groups-are-lef`),
  so they contain no finitely presented infinite simple group. This removes the host
  where amenability is proved, the rank-2 interval exchange groups of
  Juschenko–Matte Bon–Monod–de la Salle. Polygon exchanges, where Labbé's shift lives,
  are not covered.
