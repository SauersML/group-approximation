# bh-g1-effective: master-route gate G1(f), (M2)

Lane: bh-g1-effective, 2026-09-18. Every item below is a lane proof and has not been reviewed.

## Results
1. `rf-toeplitz-subshifts-from-normal-chains-are-free`: the residually finite Toeplitz
   subshift is free at every point. The same argument gives a unique non-constant coset per
   level at every point, not only on the base orbit.
2. `effectively-rf-groups-have-effective-minimal-free-subshifts`: (M2) holds for every
   infinite effectively residually finite group with solvable word problem. This includes all
   infinite fp residually finite groups and all infinite f.g. linear groups.
3. `free-products-with-z-inherit-m2-from-universal-points`: A * Z satisfies (M2) as soon as
   A has one computable point that is hyperaperiodic (H) and universal at the origin (U).
   - *Skeleton:* the Bass–Serre tree of A * Z, with pointers toward a computable end.
   - *Height labels:* Sturmian.
   - *Fibers:* the A-fibers are that point, rooted at each vertex's parent edge.
4. `decidable-groups-embed-in-fp-groups-satisfying-m2`: the form of (M2) the master route
   actually needs. Its route is `m2-envelopes-via-free-product-with-z` (Clapham, then
   `* Z`). The open premise is `decidable-groups-have-universal-hyperaperiodic-points`.
5. Attempt 8 on `decidable-fp-groups-have-effective-minimal-free-subshifts`: effectivity
   accounting and the status of St_10(R_L).

## Literature checked (web and abstracts; bounded search)
- Aubrun–Barbieri–Thomassé, arXiv:1507.03369: effectively closed strongly aperiodic
  subshifts exist for every decidable group. They are not minimal.
- Barbieri–Sablik–Salo, arXiv:2104.05141v4 (p. 1–3 read): products of two non-amenable
  groups are self-simulable, and self-simulable decidable groups have strongly aperiodic
  SFTs. No minimality claim found.
- Carrasco-Vargas, arXiv:2303.14820: computable translation-like Z-actions with decidable
  orbit membership, and Medvedev degrees. No minimal free effective subshift.
- Amir–Hellouin de Menibus, ICALP 2025: strong computable type for G-shifts, a
  characterization. Not a construction.
- Gao–Jackson–Seward: non-effective.

No source was found that states (M2) for non-residually-finite groups.

## Why the free product helps, and what it does not do
- *The mechanism.* In a Γ-ball, only the top tree vertex is seen away from its rooted fiber.
  Every other vertex's parent edge lies in the ball. So the only uncontrolled content is
  "one fiber at one far offset". (U) supplies it near the root of a descendant, and the
  Sturmian heights supply the rest.
- *What it does not do.* For centrally repetitive points (the Álvarez López colorings in
  Attempt 7), (U) is equivalent to the global modulus. The seam problem is therefore moved
  to one position, not removed.

## Lesson for general BH
(M2) is trivial wherever there are finite quotients. The inputs to Boone–Higman have none, so the
real (M2) problem is to find a non-profinite skeleton. Free products with Z supply one
(Bass–Serre), at the price of a single-position universality statement: a library-closed
completion near one point. That is the zero-dimensional form of the small-library,
cross-depth locality asked for by G2-fp and bh-free-22.
