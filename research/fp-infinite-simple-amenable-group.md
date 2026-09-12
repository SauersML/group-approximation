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
