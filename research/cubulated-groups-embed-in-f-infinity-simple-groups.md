---
rg: 2
id: cubulated-groups-embed-in-f-infinity-simple-groups
kind: claim
title: Every group acting properly and cocompactly on a CAT(0) cube complex, torsion allowed, embeds in a simple group of type F_infinity, and so does every group commensurable up to finite index with such a group (strengthens BBCMP Question 1.15)
distinct_from:
  torsion-free-cubulated-groups-embed-in-f-infinity-simple-groups: that treats free actions and reaches virtually torsion-free groups through Krasner-Kaloujnine; this allows finite stabilizers directly, so it needs no torsion-free subgroup of finite index.
  virtually-torsion-free-cubulated-groups-satisfy-boone-higman: that is the question node (BBCMP Q1.15, virtually torsion-free); this drops the virtual torsion-freeness hypothesis.
---

**OPEN — proof claimed 2026-09-19, not independently reviewed.** It builds on the
torsion-free chain `torsion-free-cubulated-groups-embed-in-f-infinity-simple-groups`, which is
ESTABLISHED and internally refereed by bh-ref-q115-a and bh-ref-q115-b. It adds two new lane
steps, which need their own referee pass:
- the orbit category with finite stabilizers as units, in
  `cubulated-groups-with-torsion-host-proof`;
- the finite-unit Cuntz theorem, in `cuntz-garside-coded-actions-host-proof`.

## Statement

1. **Torsion allowed.** Let `G` act properly and cocompactly on a CAT(0) cube complex `X`,
   with finite stabilizers allowed. Then `G` embeds in a simple group of type `F_∞`.
2. **Finite-index overgroups.** If `H ≤ K`, `[K:H] < ∞`, and `H` is as in item 1, then `K`
   embeds in a simple group of type `F_∞`.
   - One route is the induced action on `X^{K/H}`.
   - The other, used here, is `S ≀ Q ≤ S` (item 4 of
     `cuntz-garside-coded-actions-embed-in-f-infinity-simple-groups`).
3. **Subgroups.** Hence every subgroup of such a `K` embeds in a finitely presented simple
   group.

**Relation to Q1.15.** Item 1 contains the positive answer claimed for BBCMP Question 1.15,
and removes its hypothesis "virtually torsion-free". That hypothesis is not known to hold for
cubulated groups in general: it follows from Agol's theorem in the hyperbolic case, and to our
knowledge the general case is open. BBCMP use it for their continuous-automatic embedding
(Theorem 1.13). The flagged coding does not need it.

## The host

1. `G' = G * F_r`, with `r` the number of vertex orbits.
   - `X'` is the tree of copies of `X` over the Bass–Serre tree `T` of the graph of groups
     with one vertex group `G` and `r` loops with trivial edge groups.
   - A `c`-edge joins `g'·v_i` to `g'c_i·v_i`.
2. `P` is the flagged path category of `X'` itself, not a quotient.
3. `𝔠_{G'}` is its orbit category: objects are representatives `r` of `G'`-orbits of pointed
   labels `(w,σ)`, and morphisms are pairs `(m, g)` with `m ∈ P` from `r` and `g·r' = 𝐝(m)`.
   The units are the finite stabilizers `(id_r, k)`, `k ∈ Stab(r)`.
4. The host is `S = F((I_l ⋉ X_∞ × G_2)|_{Y×C})`, where `Y ≅ ∂_R X'` is the base cone.

## Lesson for general BH

Torsion enters the coding only as finite unit groups, and those cost nothing in Li-type
finiteness once types are counted up to units. It enters the dynamics only through
stabilizers, and free exits have trivial stabilizers, so topological freeness survives.

So for this route "torsion-free" was never a hypothesis. It was a convenience of quotienting
by a free action. The same holds for any geometric input with finite stabilizers: replace the
orbit quotient by the orbit category with stabilizers as units.
