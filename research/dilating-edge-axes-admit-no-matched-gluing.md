---
rg: 2
id: dilating-edge-axes-admit-no-matched-gluing
kind: claim
title: Matched-compactification gluing over cyclic vertex groups with trivial core pieces forces the modular character to be trivial on S; so the stable letter of BS(m,n) with |m| ≠ |n| never gets a relative seed this way, and the Baumslag–Gersten gluing route fails on its dilation side
distinct_from:
  edge-pinned-gluing-reduces-rigidity-to-phantom-determinacy: that gives sufficient matching conditions (DM), (EX), (M) for gluing without full edge stabilizers; this shows that on dilating edges they cannot all hold, for every choice of SFT compactifications of the cyclic vertex groups.
  baumslag-gersten-port-route-fails-at-the-dilation-centralizer: that kills the port route to Baumslag–Gersten on the dilation side, through centralizers of shifts; this kills the seed-gluing route on the same side, through tail periods, an independent mechanism.
---

**ESTABLISHED** by the proof below (lane bh-invent-03, 2026-09-19; elementary lane proof, not reviewed; no priority
claimed). Setting and conditions (DM), (EX), (M) are as in `edge-pinned-gluing-reduces-rigidity-to-phantom-determinacy`.

## Statement

Let `𝔾` be a finite graph of groups with **infinite cyclic vertex groups**. Each edge `ε` embeds `Z` as `m_ε Z` and
`n_ε Z` in its endpoint groups. Put `Λ = π_1(𝔾)`, and let `S ≤ Λ` act on a core `K` with `S\K` finite and **trivial
vertex pieces**.

For `s ∈ S`, let `Δ(s) = Π |n_ε| / |m_ε|` be the product along the core path from `v` to `sv`. This is the modular
character of the generalized Baumslag–Solitar group.

1. **Obstruction.** If (DM) and (M) hold on every core edge, for some choice of SFT compactifications of the vertex
   groups, then `Δ ≡ 1` on `S`.
2. **Baumslag–Solitar.** In `BS(m,n) = ⟨a, t | t^(-1) a^m t = a^n⟩`, take `S = ⟨t⟩`, whose core is the axis of `t`.
   Matched gluing then requires `|m| = |n|`.
   - So `(BS(1,2), ⟨b⟩)` is never produced by matched gluing over the standard splitting.
   - Nor is `(BS(m,n), ⟨t⟩)` for any `|m| ≠ |n|`.
3. **Baumslag–Gersten.** `BG = ⟨a, b, t | b^(-1)ab = a^2, t^(-1)at = b⟩` is an HNN extension of `BS(1,2)` along
   `⟨a⟩ -> ⟨b⟩`. Vertex-marked gluing of BG needs `(BS(1,2), ⟨a⟩)` and `(BS(1,2), ⟨b⟩)`.
   - The first holds, by 5deee0184 item 1 with `C = V_u`.
   - The second is excluded from this route by 2.
   - So the seed-gluing route to `BG ∈ 𝒞` fails exactly on the dilation side. That is also where
     `baumslag-gersten-port-route-fails-at-the-dilation-centralizer` (1887cf483) kills the port route.

## Proof

**The tail invariant.** A core vertex of class `p` carries a relative seed for `(Z, 1)`, i.e. an SFT compactification
`Y` of `Z`.
- Its forced point `y_*` is eventually periodic, since isolated points of `Z`-SFTs are (a standard pumping argument, also recorded by bh-invent-11).
- Let `p_±(Y)` be the minimal periods of its two tails. Then `k.y_*` accumulates, as `k -> ±∞`, on a periodic orbit
  with `p_±` points, and the residue class `r + p_± Z` converges to one of them.

**(DM) forces divisibility.** At a core edge whose group is `mZ` in this vertex, the marked coset is a residue class
`r + mZ`, since the pieces are trivial.
- (DM) needs a clopen set meeting the orbit exactly in `(r + mZ).y_*`. So the limit sets of distinct residue classes
  mod `m` must be disjoint at each end.
- Class `r` accumulates on the tail points indexed by `r + mZ` mod `p_±`. These sets are disjoint for distinct `r`
  iff `m | p_±`.

**(M) transports the invariant.** Under (DM), the induced compactification `O` of the edge group `mZ ≅ Z` has
`p_±/m` limit points at its two ends.
- (M) is an equivariant homeomorphism with the other endpoint's `O'`, carrying the genuine orbit to the genuine
  orbit. So it matches ends: the same ends if `m_ε n_ε > 0`, swapped otherwise.
- Hence `p_±(Y_w) = (|n|/|m|) · p_±(Y_v)` or `p_∓(Y_v)`. In either case the pair `{p_+, p_-}` is multiplied by
  `|n|/|m|` across the edge.

**Around the core.** Vertices `v` and `sv` lie in one class, so they carry the same `Y`. Composing along the path from
`v` to `sv`:
- if the ends are not swapped, `p_+ = Δ(s) p_+`, so `Δ(s) = 1`;
- if they are swapped, `p_+ = Δ(s) p_-` and `p_- = Δ(s) p_+`, so `Δ(s)² = 1` and again `Δ(s) = 1`.

This proves 1. For 2, the axis of `t` has trivial vertex stabilizers in `⟨t⟩`, and `Δ(t) = |n|/|m|`. 3 follows. ∎

## Scope

- **Realized otherwise.** `(BS(1,2), ⟨b⟩)` does have a rigid relative seed, built from the affine order on `Z[1/2]`
  rather than the Bass–Serre splitting (`order-seeds-are-rigid-relative-seeds`, bh-emitter-a; see also `ordered-orbits-give-rigid-relative-seeds`). With it, Baumslag–Gersten lies
  in `𝒞` (`baumslag-gersten-groups-lie-in-class-c`). The obstruction here is to tree gluing only.
- **Unimodular edges.** When `|m| = |n|` (for example `BS(2,2)` and unimodular GBS groups), the counting obstruction
  vanishes. Choosing tail periods divisible by `m` meets (DM), and (M) becomes a finite check on the tail orbits. This
  positive case is not claimed here.

## Lesson for general BH

**Seeds, like ports, must be parabolic.**
- **The mechanism.** Matched gluing carries a numerical invariant, the tail period of the induced edge
  compactification, and it is multiplied by the edge modulus at every step.
- **The consequence.** A finite core therefore forces the modular character to vanish on `S`. Dilating edges, the
  Baumslag–Solitar edges that Higman-type and Baumslag–Gersten constructions rely on, cannot be seeded from cyclic
  vertex seeds.
- **Two routes, one wall.** The port route (bh-invent-02) and the seed-gluing route both fail at the same place.
  Dilations must be carried by a vertex geometry larger than `Z`, not by the tree.
