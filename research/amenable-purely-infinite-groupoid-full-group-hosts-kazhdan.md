---
rg: 2
id: amenable-purely-infinite-groupoid-full-group-hosts-kazhdan
kind: claim
title: Some amenable, minimal, effective, purely infinite ample groupoid has a topological full group containing an infinite Kazhdan group
distinct_from:
  brin-thompson-groups-nv-are-a-t-menable: that asks for the Haagerup property of the specific full groups nV = [[G_2^n]]; this shows that the groupoid-level properties G_2^n shares with many other groupoids do not imply the Haagerup property, or even finiteness of Kazhdan subgroups.
  sft-topological-full-groups-have-the-haagerup-property: that is Matui's positive theorem for one-sided irreducible shifts of finite type, which uses the zipper structure of those groupoids; this is a negative calibration for the general class that contains them.
  input-encoded-sft-groupoid-hosts-are-not-universal: that shows shift-of-finite-type groupoids contain no infinite Kazhdan group; this builds a different purely infinite amenable groupoid whose full group does contain one.
  irs-rigid-kazhdan-groups-avoid-haagerup-orbit-full-groups: that is a measured transfer theorem for orbit full groups of free actions of Haagerup groups; this is a topological example where the acting group has property (T) and the groupoid is still amenable.
---

**ESTABLISHED.**

**Theorem.** Let `Γ = Z^3 ⋊ SL_3(Z)`. There is a second countable, Hausdorff, ample
groupoid `𝒢` on a Cantor set with all of the following properties:

1. `𝒢` is topologically amenable (approximately invariant continuous systems of
   probability measures, uniformly on compacts; Step 0 of the route);
2. `𝒢` is minimal;
3. `𝒢` is essentially principal (effective);
4. `𝒢` is purely infinite in Matui's sense;
5. its topological full group `[[𝒢]]` contains a copy of `Γ`.

`Γ` is infinite and has property (T). So `[[𝒢]]` does not have the Haagerup property,
and it has an infinite Kazhdan subgroup.

**Construction.** `𝒢 = (M ⋊ Γ) × G_2`. Here `M` is a Cantor set with a free, minimal,
topologically amenable `Γ`-action, and `G_2` is the Deaconu–Renault groupoid of the
one-sided full shift on two letters, with `[[G_2]] = V`. The proof is the route
`amenable-purely-infinite-groupoid-kazhdan-host-proof`.

## Why it matters for nV

Brick maps are products of prefix replacements, so `nV ≤ [[G_2^n]]`, and the same
product arguments show `G_2^n` has properties 1–4 (section "Application to nV" of the
route). So any argument of the form

> `𝒢` is ample, amenable, minimal, effective and purely infinite, hence `[[𝒢]]` is
> a-T-menable (or: has only finite Kazhdan subgroups)

is false. A Haagerup proof for `nV` must use structure that `(M ⋊ Γ) × G_2` lacks,
for instance the local similarity or product-of-trees structure of `G_2^n`, or
expansivity or compact generation of the groupoid. This is a class-kill in the sense
of the playbook:

- **Invariant:** property (T) of `Γ = Z^3 ⋊ SL_3(Z)`.
- **Step where every member dies:** the passage from groupoid-level hypotheses to a
  proper conditionally negative definite function on `[[𝒢]]`. Its restriction to
  `Γ ≤ [[𝒢]]` would be proper on an infinite Kazhdan group, which is impossible.

The example is not in `nV`, so it says nothing about the truth of
`brin-thompson-groups-nv-are-a-t-menable`.
