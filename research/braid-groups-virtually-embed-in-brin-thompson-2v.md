---
rg: 2
id: braid-groups-virtually-embed-in-brin-thompson-2v
kind: claim
title: For every m, some finite-index subgroup of the braid group B_m embeds in the Brin--Thompson group 2V
distinct_from:
  closed-mcg-in-nv-forces-braid-groups-in-nv: that shows a Brin--Thompson host for closed-surface mapping class groups forces braid groups into the same host; this asks whether braid groups get there at all.
  every-raag-embeds-in-brin-thompson-group-2v: that is the right-angled Artin case, which this would contain for pure braid groups only if they embed in right-angled Artin groups.
  closed-mcg-finite-index-subgroups-do-not-embed-in-v: that shows the host V fails, through Z^2 * Z, which also lies in braid groups on at least five strands; this asks about 2V, where Z^2 * Z does embed.
---

**OPEN.** For every `m ≥ 1` there is a finite-index subgroup of `B_m` isomorphic to
a subgroup of `2V`. Through `brin-thompson-nv-embeds-in-mv`, a "no" for some `m`
excludes every `nV`. With `closed-mcg-in-nv-forces-braid-groups-in-nv`, it would
then exclude every `nV` as a host for `Mod(S_g)` when `2g − 1 ≥ m`.

## What is known

- `m ≤ 3`: yes. `PB_3 ≅ F_2 × Z` is a right-angled Artin group, so it lies in `2V`
  (`every-raag-embeds-in-brin-thompson-group-2v`).
- `V` itself fails for `m ≥ 5`. Finite-index subgroups contain `Z² ∗ Z`, from
  large powers of twists about a chain of three curves (Koberda), and `V` has no
  such subgroup. So the question is genuinely about `n ≥ 2`.
- **No distortion obstruction.** The route into `2V` through the topological full
  group of the full shift gives only subgroups without distorted elements
  (`subshift-crossed-product-gl-has-no-distorted-elements`). Braid groups have
  none either, since every infinite-order element of a mapping class group is
  undistorted (Farb--Lubotzky--Minsky 2001; not re-read here).

## Attempts

1. **Through right-angled Artin groups** (lane bh-mcg, 2026-09-18). Route
   `braid-groups-in-2v-via-pure-braid-raag-embedding`, with open premise
   `pure-braid-groups-embed-in-raags`. This premise sits next to a recognized open
   problem. Wu--Ye, arXiv:2608.13978v1 (2026-08-14), abstract read via the arXiv
   API: "Agol in his 2014 ICM proceedings article asks whether braid groups are
   (virtually) RFRS. We answer this positively by showing that pure braid groups
   are RFRS. ... Our results also provide evidence toward the problem of whether
   braid groups, and more generally Artin groups, are virtually special."
   Neither Agol's article nor the body of Wu--Ye was read.
