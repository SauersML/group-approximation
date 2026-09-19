---
rg: 2
id: free-group-houghton-group-acts-with-type-a
kind: claim
title: The free-group Houghton group T0 has a finitely generated seed stabilizer and acts on the vertices of the Cayley tree with type (A); so it passes the whole finiteness half of the hard-actor row, and every subgroup of T0 lies in a finitely presented simple group
distinct_from:
  free-group-houghton-group-is-of-type-f-infinity: that proves T0 is F_∞; this adds the seed stabilizer and the type (A) consequence, which that node and its review left unchecked.
  fp-finitary-permutation-overgroups-are-type-a-actors: that is the general theorem used here; this applies it to T0.
---

**ESTABLISHED** (lane bh-invent-03, 2026-09-19; a direct corollary; not reviewed). This answers the check the
referee asked for in `free-group-houghton-group-f-infinity-review` §7: "finite generation of the seed stabilizer is
not addressed".

## Statement

Let `F` be the full group of the free-group tree seed (T0), acting on `X = T^0 = F_2`, with seed `o`.
1. `Stab_F(o)` is finitely generated.
2. `F ↷ T^0` is faithful and highly transitive, and it is of **type (A)**.
3. Every subgroup of `F` embeds in the finitely presented simple group `SV_F`, and satisfies permutational
   Boone–Higman.

## Proof

- **The inputs.**
  - `F` contains `FSym(T^0)` (`seed-full-groups-act-oligomorphically-on-the-seed-orbit`), hence
    `Alt_fin(T^0)`.
  - `F` is finitely generated, indeed of type `F_∞` (`free-group-houghton-group-is-of-type-f-infinity`,
    refereed).
- **Items 1 and 2.** By `fp-finitary-permutation-overgroups-are-type-a-actors`, items 1–2, every point stabilizer
  is finitely generated and the action is highly transitive. By its item 3, the action is of type (A) exactly when
  `F` is finitely presented, which it is.
- **Item 3** is `type-a-action-gives-boone-higman-for-subgroups`. ∎

## What this settles and what it does not

- **Settled.** T0 passes the whole finiteness half of the hard-actor row (SYNTHESIS row 1,
  `hard-evaluation-seeds-with-finitely-presented-full-groups`): a finitely presented full group and a finitely
  generated seed stabilizer, for a non-split seed.
- **Not settled.** Hardness. T0's seed is finite-state, and `SV_F` has an easy word problem. The subgroups reached,
  such as `F_2` and the lampshuffler over `F_2`, were already known to lie in finitely presented simple groups (for
  instance through `V`).
- **Where condition 1 stands.** By `finite-type-farley-hughes-groups-are-exponentially-capped`, in its refereed
  scope, a hard seed certified by this kind of engine on its own orbit must hide its hardness in the address of a
  non-isolated seed, or use a non-restriction-closed structure.

## Lesson for general BH

Once a seed full group is finitely presented, the stabilizer condition and type (A) come free: the finitary
permutations do all the work. So the hard-actor route is exactly **finite presentation of a seed full group whose
seed is hard**. T0 shows the first half can be done for non-split multi-type seeds. The second half is the open
problem.
