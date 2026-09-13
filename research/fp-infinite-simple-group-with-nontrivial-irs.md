---
rg: 2
id: fp-infinite-simple-group-with-nontrivial-irs
kind: claim
title: Some finitely presented infinite simple group has a nontrivial ergodic invariant random subgroup
distinct_from:
  fp-simple-group-in-amenable-orbit-full-group: That asks for a realization inside an amenable orbit full group, which gives soficity; this asks only for a nontrivial ergodic IRS, which every non-amenable such realization produces, so a non-amenable witness there answers this claim.
  irs-rigid-nonamenable-groups-avoid-amenable-orbit-full-groups: That proves IRS-rigid non-amenable groups have no nontrivial realizations; this is the existence question for the complementary property among finitely presented simple groups.
---

**OPEN.** There is a finitely presented infinite simple group `S` with an ergodic
measure-preserving action on a standard probability space whose stabilizer invariant
random subgroup is neither `delta_{1}` nor `delta_S`. Equivalently, `S` has a
nontrivial ergodic action that is not essentially free.

**Why it matters.**
- **A necessary condition for the orbit certificate.** A non-amenable witness of
  `fp-simple-group-in-amenable-orbit-full-group` has a nontrivial ergodic IRS
  (`irs-rigid-nonamenable-groups-avoid-amenable-orbit-full-groups`, Consequence). If
  every finitely presented infinite simple group were IRS-rigid, the certificate could
  only reach amenable groups. It would then refute both
  `labbe-shift-derived-full-group-is-finitely-presented` and
  `penrose-derived-full-group-is-finitely-presented`, since those groups have
  nontrivial IRSs.
- **Separating rigidity from finite presentation.** Every finitely presented simple
  family recorded in the graph is either IRS-rigid or undecided (Attempts). An example
  would show that finite presentation does not force stabilizer rigidity.

**Model test.** The trivial action gives `delta_S`, and a Bernoulli shift gives
`delta_{1}`, so neither witnesses the claim. `D([[Z^2 ~ Omega_U]])` acting on Labbé's
shift with its invariant measure has a nontrivial IRS (its elements fix sets of
positive measure without acting trivially), but it is not known to be finitely
presented.

## Attempts

- **Groups without proper characters.** Dead. For an infinite simple group whose
  characters are trivial plus regular, Steps 2--3 of
  `stabilizer-rigid-groups-avoid-orbit-full-groups-proof` show that every
  measure-preserving action is essentially free off its global fixed points. So its
  ergodic IRSs are trivial. This removes:
  - `V` (Dudko--Medynets);
  - every alternating full group of a minimal purely infinite essentially principal
    Cantor groupoid (Gardella--Tanner);
  - `T`, given its classical simplicity
    (`no-proper-character-groups-avoid-amenable-orbit-full-groups`).
- **Specified Kac--Moody lattices.** Dead for the compact-hyperbolic class of
  Caprace--Thom, which has exactly the two trivial ergodic IRSs
  (`caprace-thom-v2-leaves-km-character-rigidity-open`). Whether that class contains the
  finitely presented simple Caprace--Rémy lattices was not cross-checked.
- **Undecided families.**
  - Lattices in products of trees (Burger--Mozes, Rattaggi). The known Stuck--Zimmer
    type theorems (Creutz--Peterson, Creutz) need higher-rank or property (T) factors,
    which `Aut(T)` lacks.
  - Titz Mite--Witzel kernels.
  - Other Kac--Moody lattices.
  - Khanh's Leavitt unit group, which contains `V` but has no recorded character
    classification.
  - Lodha's circle groups and twisted Brin--Thompson groups.
- **Tiling candidates.** Live: `fp-simple-irs-via-labbe-shift` and
  `fp-simple-irs-via-penrose-group`. Each is gated by the same finite-presentation claim
  that gates the hyperlinear root.
