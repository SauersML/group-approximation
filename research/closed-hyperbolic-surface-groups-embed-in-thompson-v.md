---
rg: 2
id: closed-hyperbolic-surface-groups-embed-in-thompson-v
kind: claim
title: The fundamental group of a closed hyperbolic surface embeds in Thompson's group V (survey Question 4.7)
distinct_from:
  virtually-special-groups-embed-in-some-brin-thompson-group: that embeds surface groups in some higher Brin--Thompson group nV; this asks for n = 1, Thompson's V itself, where the right-angled Artin route provably fails.
  every-raag-embeds-in-brin-thompson-group-2v: that puts every right-angled Artin group in 2V; V contains only the products of free groups among them (`raag-subgroups-of-v-contain-no-one-ended-hyperbolic-group`).
  hyperbolic-groups-satisfy-boone-higman: that embeds every hyperbolic group in some finitely presented simple group (BBMZ); this asks for the specific finitely presented simple group V.
  closed-mcg-finite-index-subgroups-do-not-embed-in-v: that excludes finite-index subgroups of closed mapping class groups from V through Z^2 * Z; surface groups contain no Z^2, so that obstruction does not apply here.
requires:
  - cocompact-fuchsian-groups-embed-in-v-all-or-none
  - raag-subgroups-of-v-contain-no-one-ended-hyperbolic-group
artifacts:
  - research/artifacts/gq-bh-bh-bbmz-problems-status.md
---

**OPEN.** For some (equivalently, by
`cocompact-fuchsian-groups-embed-in-v-all-or-none`, every) closed hyperbolic
surface `Σ`, the group `π_1(Σ)` is isomorphic to a subgroup of Thompson's group `V`.

**Source.** Belk--Bleak--Matucci--Zaremsky, arXiv:2306.16356v3, Question 4.7. It is
transcribed only as a fragment in `research/artifacts/bh-survey-open-cases-status-2026-09-12.md`:
"Do any one-ended hyperbolic groups embed into V? ... closed hyperbolic surface?".
The surface-group case is the one this node records. The general question, for all
one-ended hyperbolic groups, is wider.

## Equivalent forms

By `cocompact-fuchsian-groups-embed-in-v-all-or-none` the following are equivalent:
1. this claim;
2. `π_1(Σ_2) ≤ V`, for the closed orientable genus-2 surface;
3. the (2,3,7) triangle group `⟨a, b | a^2, b^3, (ab)^7⟩ ≤ V`;
4. every cocompact Fuchsian group, and every closed hyperbolic surface group
   (orientable or not), embeds in `V`.

Form 3 is the most concrete. `V` contains `⟨a, b | a^2, b^3⟩ ≅ PSL_2(Z)`, a free
product of finite groups. The question is whether some such pair in `V` also
satisfies `(ab)^7 = 1` without further relations. (The embedding of free products of
finite groups is recalled, not checked here.)

## What is known

- **Yes for 2V** (this depends on an unrefereed preprint and on a surface-group
  citation not read at source):
  - Salo proves every f.g. right-angled Artin group embeds in `2V`
    (`every-raag-embeds-in-brin-thompson-group-2v`; Salo's arXiv:2103.06663 is
    unrefereed).
  - Some RAAG contains a closed hyperbolic surface group, e.g. `A(C_5)`
    (Servatius--Droms--Servatius; not read at source here).
  - Groups that virtually embed in `nV` embed in `nV` (Belk--Bleak--Matucci, as
    quoted in `virtually-special-groups-embed-in-brin-thompson-citation`).

  Together these give every closed hyperbolic surface group and every cocompact
  Fuchsian group in `2V`. So Question 4.7 is exactly the `n = 1` case.
- **The RAAG route to V is dead** (`raag-subgroups-of-v-contain-no-one-ended-hyperbolic-group`).
  The only RAAGs inside `V` are products of free groups. No one-ended hyperbolic
  group virtually embeds in one of those.
- **Known non-embeddings do not apply.**
  - `Z^2 * Z` does not embed in `V` (Bleak--Salazar-Díaz), but surface groups
    contain no `Z^2`.
  - `BS(1,n)` does not embed in `V` (`bs-1-n-does-not-embed-in-thompson-v`), but
    surface groups contain no solvable non-cyclic subgroups.
  - Groups whose torsion is not bounded by word length are excluded from coCF
    groups (`cocf-group-torsion-order-bounded-by-word-length`), but surface groups
    are torsion-free.

## Attempts

1. **2026-09-18, lane `bh-bbmz-problems`.** Reduced the question to a single group
   (form 2 or 3) and killed the RAAG route (the two nodes above).
   - The positive direction needs a construction of a one-ended subgroup of `V` that
     does not go through RAAGs.
   - The negative direction needs an invariant of subgroups of `V` that sees surface
     groups. The Z^2-based dynamics of Bleak--Salazar-Díaz sees nothing here.
   - A candidate is Lehnert's conjecture (`lehnert-conjecture-every-cocf-group-embeds-in-v`),
     since whether surface groups are coCF is also open. That turns a no into a
     coCF question, not an answer.

- **bh-free-41, 09-18 (support and attractor route; stalled).** These three landings are lane proofs and have not been reviewed:
  - `cyclic-centralizer-subgroups-of-nv-have-meeting-supports`: in every `nV`, all nontrivial supports meet.
  - `cyclic-centralizer-subgroups-of-v-touch-attractors`: in `V`, every support meets the attractors, the repellers, or the identity region of any other element's flow power.
  - `support-constraints-on-v-subgroups-cannot-see-one-endedness`: free subgroups of `PSL_2(Z) ≤ T` satisfy every such condition with full supports.

  One serious pass on the next idea also failed. The idea was an equivariant map from the orbit closure of the attractors onto `∂Γ = S^1` that clashes with the Cantor topology.
  - Such maps exist and clash with nothing. Belk–Bleak–Matucci embed every hyperbolic group in the rational group `R` through its horofunction boundary, a Cantor set carrying a continuous, finite-to-one, equivariant surjection onto `∂Γ`. I recalled this and did not read it at source.
  - The Bowen–Series coding of a surface group gives the same picture.
  - So connectedness of `∂Γ` alone gives no obstruction. A negative answer to Q4.7 must see the difference between `V` and `R`, that is, synchronous against asynchronous transducers, and not just the Cantor-versus-circle topology.
