---
rg: 2
id: digit-group-stable-letters-carry-an-anchored-core-seed
kind: claim
title: In the k-letter digit group Z_J = <x, a_i | a_i^-1 x a_i = x^m>, the stable-letter subgroup F(a) is the stabilizer of a locally forced isolated point (an anchored core seed on the locally finite Bass-Serre tree); (RS1) and (RS2) hold, (RS3) reduces to the derived subshift of tree data plus one sign
requires:
  - kurosh-relative-seeds-and-the-b1-digit-splitting
  - baumslag-gersten-groups-lie-in-class-c
  - locally-finite-splittings-preserve-rigid-sft-compactifications
  - quantum-rigidity-is-decided-on-the-derived-subshift
distinct_from:
  baumslag-gersten-groups-lie-in-class-c: that seeds the cyclic stable-letter subgroup <b> of BS(1,n), whose core is a line; this seeds the free stable-letter subgroup F(a) of the k-letter BS(1,m), whose core is a 2k-regular tree with m-adic phase data.
  kurosh-relative-seeds-and-the-b1-digit-splitting: that reduced (B_1, <t,a_i>) to three stable-letter pairs; this treats the first, (Z_J, F(a)), and through an automorphism also (Z_J, Sigma).
---

**Status.**
- §§1–3 are **ESTABLISHED** (lane proof, bh-invent-14, 2026-09-18; not reviewed): the SFT, (RS1),
  the stabilizer, and the (RS2) classification.
- §4, (RS3), is **reduced, not proved**. The derived subshift is tree data plus one global sign, the
  situation of bh-invent-10's Baumslag–Gersten template. The monotone-chain step is sketched.

## Setting

- `Z_J = ⟨x, a_1, …, a_k | a_i^{-1} x a_i = x^m⟩`, with `m ≥ 2` and `k ≥ 1`.
- **Tree.** Its Bass–Serre tree `T` over `⟨x⟩` is locally finite. At `h⟨x⟩`, for each `i`:
  - one *up* edge to `h a_i ⟨x⟩`, the same for every representative, since `x a_i = a_i x^m`;
  - `m` *down* edges to `h x^j a_i^{-1} ⟨x⟩` (`j ∈ Z/m`), where the index shifts by `−1` when
    `h ↦ hx`.
- **Map to the free group.** Killing `x` maps `T` onto the Cayley tree of `F(a) = F_k` and
  identifies each group of `m` down edges.
- **The core.** `F(a)` acts freely on `T`, since it meets no conjugate of `⟨x⟩`. Its core is
  `T_F = {w⟨x⟩ : w ∈ F(a)}`, a copy of `Cay(F_k)`.
  - At each core vertex, all `k` up edges are core, and for each `i` exactly one down edge is
    core: `w a_i^{-1}`, index `0` from the representative `w`.
  - Two core vertices are never joined by a non-core edge. If `w x^j a_i^{-1}⟨x⟩ = w'⟨x⟩` with
    `w' ∈ F(a)`, then killing `x` gives `w' = w a_i^{-1}`, and `a_i x^j a_i^{-1} ∈ ⟨x⟩` forces
    `m | j`.

## 1. The SFT `Y_F`

**Alphabet.**
- `(core, c)`, with `c ∈ {+, *, −}` a `C_Z` letter along `x`;
- `(ptr, e)`, with `e ∈ {up_i} ∪ {down_{i,j} : j ∈ Z/m}`.

**Rules** (all of bounded radius).
- **(T)** The type is constant along `x`. On core cells, `c` follows `C_Z` along `x` (steps `++`,
  `+*`, `*−`, `−−`). `up_i` is constant along `x`, and `down_{i,j}` at `h` becomes `down_{i,j−1}`
  at `hx`.
- **(E)** For every `h` and `i`, exactly one of the following holds:
  - `h` and `h a_i` are both core;
  - `h` is `(ptr, up_i)`;
  - `h a_i` is `(ptr, down_{i,0})`.
- **(K)** If `h` is core, then every `h a_i` is core, and for each `i` exactly one of
  `h x^j a_i^{-1}` (`j ∈ Z/m`) is core.
- **(Ph)** Coherence of phases.
  - At a core `h`, the index `j` in (K) is the same for all `i`.
  - For two such core down neighbours `h x^j a_{i_1}^{-1}` and `h x^j a_{i_2}^{-1}`, the index of
    their own core down neighbours agrees.
- **(A)** If `c(h) = *`, then `h a_i` and `h a_i^{-1}` are core with `c = *`, for all `i`.
- **(Sg)** If `h` and `h a_i` are core, they carry the same `c`.

**Seed.** `(core, *)` at `1`.

**The point `y_*`.**
- Core cells are exactly `F(a)⟨x⟩`, and `c(w x^r)` is `+`, `*` or `−` according as `r < 0`,
  `r = 0` or `r > 0`.
- Every other cell points toward `T_F`.
- **Checks.** `w x^r a_i = w a_i x^{mr}` gives (Sg) and (A). The phase at `w x^r` is `−r mod m`,
  and one level down it is the next `m`-adic digit of `−r` whatever the branch letter, since
  `x^{ms} a_i^{-1} = a_i^{-1} x^s`. That gives (Ph).

## 2. (RS1) and the stabilizer

**Forcing.** The seed forces `C_Z` on `⟨x⟩` with `*` at `1`. By (A), `*` spreads to all of `F(a)`,
so (T) makes all of `F(a)⟨x⟩` core with `y_*`'s letters.
- By (K), no other down neighbour of a core vertex is core.
- There is at most one core component: on a path between two components some cell would have two
  out-edges, which (E) forbids.
- So every non-core cell is forced by (E) to point toward the core, one tree step at a time.
- Hence the seed cylinder is `{y_*}`.

**Stabilizer.** The `*`-cells of `g·y_*` are `g·F(a)`. So `Stab(y_*) = F(a)`.

## 3. (RS2): `Y_F` is the orbit closure of `y_*`

Points of `Y_F` are of three kinds.
- **(α) Anchored cores.** These are the translates `g·y_*`, by §2 applied at any anchor.
- **(β) Anchorless cores.**
  - By (K) and (Ph), a core is a full `2k`-regular subtree whose down choices are coherent. So it
    is determined by one core vertex and one `m`-adic number `ρ ∈ Z_m`, the phase digits level by
    level.
  - By (Sg) and `C_Z`, all its letters equal one global sign `ε ∈ {+, −}`.
  - Each `(ρ, ε)` is a limit of `x^{r_n}·y_*` with `r_n → ρ` in `Z_m` and `r_n → ∓∞` in `Z`.
- **(γ) No core.** Then (E) makes the configuration an end orientation of `T`, since every cell has
  exactly one out-edge.
  - Every end `ξ` is a limit. Along the ray to `ξ`, infinitely many vertices `v_n` have an
    up-neighbour `c` off the ray, because two valleys are never adjacent.
  - Take a translate whose core contains `c` and does not use the down edge `c → v_n`. Its core then
    lies beyond `v_n`, and the origin points along the ray. Let `n → ∞`.

## 4. (RS3): reduction

- `y_*` is locally forced (§2), so by `quantum-rigidity-is-decided-on-the-derived-subshift`, (RS3)
  is equivalent to rigidity of the derived subshift `Y' = (β) ∪ (γ)`.
- `Y'` is **tree data plus one sign**. The core subtree, with its phases, is a coherent choice of
  down edges in the locally finite tree. End orientations are pointer data. `ε` is propagated along
  core edges by (Sg).
- **Sketch.** The monotone-chain argument of `locally-finite-splittings-rigid-compactification-proof`
  applies to finite pointer labels on a locally finite tree. The sign is handled as in
  `baumslag-gersten-class-c-proof` §3.
- **Not written out.** The phase field, with its `m`-adic digits, needs an atom argument per core
  vertex: the indicator of "this down edge is core". That is the one step left to check.

## 5. Consequences (conditional on (RS3))

- **`(Z_J, F(a)) ∈ 𝓡`.**
- **`(Z_J, Σ) ∈ 𝓡`** for `Σ = ⟨a_i x^{-i}⟩`. The map `θ : x ↦ x`, `a_i ↦ a_i x^{-i}` is an
  automorphism of `Z_J`: it preserves `a_i^{-1} x a_i = x^m`, and `a_i ↦ a_i x^i` inverts it. It
  carries `F(a)` onto `Σ`, and relative seeds transport along automorphisms.
- **`(J, F(a)) ∈ 𝓡`**, by the gluing theorem along `J = HNN(Z_J; t : Σ → Σ)` with edge seeds
  `(Z_J, Σ)`.

So two of the three pairs of `kurosh-relative-seeds-and-the-b1-digit-splitting` §4 reduce to
(RS3) here. What is left is `(J, Q)`, `Q = F(a) * ⟨t⟩`, which mixes a digit core with an HNN
edge, and `(J_Q, F(a))`.

## Relation to core-marked gluing (1c1eb8413)

bh-invent-03's `core-marked-gluing-of-relative-seeds` needs `(FE)`: `S_e = Λ_e` on every core edge.
It **fails for all three stable-letter pairs**, because stable-letter subgroups meet edge groups
trivially:
- `(Z_J, F(a))`: `Λ_e ≅ Z`, a conjugate of `⟨x⟩`, and `S_e = 1`;
- `(J, Q)`: `Λ_e = Σ ≅ F_k` and `S_e = Q ∩ Σ ⊆ F(a) ∩ Σ = 1`;
- `(J_Q, F(a))`: `Λ_e = Y ≅ F_{n+1}` and `S_e = 1`.

The construction above is an **edge-pinned** seed in the locally finite case.
- The `Λ_e/S_e = Z` ambiguity across each core edge is pinned by the `C_Z` anchor on the edge coset
  `w⟨x⟩`, which (A) transports across edges.
- The finite phase data (Ph) says which of the `m` down edges is core.
- For `(J, Q)` and `(J_Q, F(a))` the pin would have to be a seed of the free edge groups `Σ` and
  `Y`, carried on the core's edge cosets and transported across the stable letters. That is the
  edge-pinned gluing still to be proved.

## Lesson for general BH

**The machine's digits are tree data.**
- The digit letters of a Higman tower form a free stable-letter subgroup. It is seeded by marking
  its core in the locally finite tree of the digit group and pinning one anchor per core coset
  with `C_Z`.
- On the boundary, the `m`-adic phases, which look like an odometer, become a choice of down edges
  in the tree: tree data, not a separate equicontinuous factor. With one global sign, that is
  exactly the shape that monotone chains handle.
- So counting in base `m` costs no rigidity beyond what trees already give. The machine's
  complexity cannot hide in its digits and must sit in the halting pair.
