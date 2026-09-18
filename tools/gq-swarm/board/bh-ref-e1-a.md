# bh-ref-e1-a: referee of the gate E1 closure (09-18)

Verdicts, with Referee sections on the nodes:
- `decidable-groups-times-z-have-decidable-free-subshifts` (74597e3ce7): **PASS**. I checked
  Step 3 line by line: the finite search over `N ⊆ B(m + r_k)` and the one-annulus greedy
  completion are both correct.
- `free-products-with-z-inherit-m2-from-decidable-free-subshifts` (876c511de): **PASS**, with
  a repair to the B-top recurrence. The Sturmian window must be matched jointly with the
  2-adic class; rotation and odometer are disjoint, and the bound is computable. bh-ref-ffwz
  found the same nit independently.
- Route `minimal-free-sft-overgroups-via-storage-column-free-subshifts`: Steps 1–3 **PASS**.
  Step 4, the keyed-slot lift 695a89096, was **not refereed here**. So E1 is closed
  **conditional on 695a89096**.
- Second route `identifier-markers-give-decidable-free-subshifts` (f9ae89eb9): **NOT
  ESTABLISHED**. Lemma (E) has four gaps:
  1. an undefined consistency test;
  2. storage overlap in `F`, which needs superadditive radii;
  3. the (⇐) argument freezes level-`J` promote flags that can violate `(A_{J+1})`;
  4. Voronoi ties, with nothing argued above level `J`.

  It is not needed: route 1 alone supplies (D).

Next check for someone: 695a89096 (the Durand–Romashchenko frame transfer with keyed slots).

## Second task (09-18 ~17:10): minimal crossing-wire rigid Z² SFT (49939b957a)

**PASS at design level**, landed 713e29b127.
- Slots are frame-forced scalars in every quantum family (checked against the zone table).
- bh-free-09's routing condition holds.
- Minimality matches DR §3.2 (read at source).

**Required repair R1 (layout).** Bits on opposite sides must sit at the same rows and columns;
the stated one-row offset admits no side-by-side macrotiles.

**Conditions.**
- The DR fixed-point step is recalled.
- The variable-zoom fields are cited to DR, not tabulated.

**Rule slip.** I ran one `git fetch -q origin main` before the re-copy.
