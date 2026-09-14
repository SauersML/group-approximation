---
rg: 2
id: ghb7-one-edge-holonomy-absorption
kind: claim
title: Genuine vertex representations of GHB_2(7) agreeing exactly on a and b and almost on c glue flexibly
distinct_from:
  ghb7-flexibly-hs-stable: that is flexible HS stability of GHB_2(7), equivalently edge matching with all three edges almost agreeing; this is the one-edge form, where a and b already agree exactly and only the c-mismatch must be absorbed, which is equivalent to it by the split-abelianization reduction
  triangle-edge-matching-reduces-to-one-edge-holonomy: that is the general reduction of edge matching to one-edge holonomy absorption; this is the open instance for the triangle of GHB_2(7)
---

**OPEN.** Let `G = G_{HB_2}(7)` with vertex groups `X_0 = ⟨a,b⟩` (order 343), `X_1 = ⟨c,b⟩` and
`X_2 = ⟨c,a⟩` (order 2401), and edge groups `⟨a⟩, ⟨b⟩, ⟨c⟩` of order 7
(`cckw-ghb2-kms-group-structure`).

**Claim (HA).** For all `d_n` and genuine representations `ρ_{i,n} : X_i → U(d_n)` with

```text
ρ_{0,n}(b) = ρ_{1,n}(b),   ρ_{0,n}(a) = ρ_{2,n}(a)   exactly,   ||ρ_{1,n}(c) − ρ_{2,n}(c)||_2 → 0,
```

there are genuine representations `π_n : G → U(D_n)`, `D_n ≥ d_n`, `D_n/d_n → 1`, with
`||ρ_{i,n}(x) − P_n π_n(x) P_n*||_2 → 0` for every `i` and every `x ∈ X_i`.

**Equivalent forms.** By `triangle-edge-matching-reduces-to-one-edge-holonomy`, whose hypothesis
(SPLIT) holds by `ghb7-triangle-vertex-groups-split-abelianizations`, (HA) is equivalent to (EM) for
this triangle, hence to `ghb7-flexibly-hs-stable`.

**What (HA) asks, concretely.** After `b` and `a` agree exactly, the remaining freedom is
conjugating `ρ_1` by unitaries in the commutant of `ρ_0(b)`, conjugating `ρ_2` by unitaries in the
commutant of `ρ_0(a)`, and `o(d_n)` flexible padding. The mismatch on `c` has to be removed with
corrections tending to `0` in normalized HS norm. The vertex group data that constrain this are in
`ghb7-triangle-vertex-groups-split-abelianizations`: `a` and `b` have centralizers of order 49 in
every vertex group containing them, while `c` has centralizers of order 343 in `X_1` and `X_2`.

**Stakes.** Through `ghb7-flexibly-hs-stable`, Cairn cascades (HA) to `non-hyperlinear-group`,
`nonsofic-hyperbolic-group` and `non-residually-finite-hyperbolic-group`.

ROUTES
ghb7-stability-via-one-edge-holonomy
