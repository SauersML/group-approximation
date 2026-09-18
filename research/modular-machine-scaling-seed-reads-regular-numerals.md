---
rg: 2
id: modular-machine-scaling-seed-reads-regular-numerals
kind: claim
title: The scaling part of the Aanderaa–Cohen group K_M is a multiple HNN extension of Z^2 with finite-index edges, so it has a rigid seed; a locally forced reader layer on that seed marks, at linear forcing radius, every position of any regular set of base-m numerals, but the reader has one free bit on every unanchored descent chain, so the rigidity of the read seed is open
requires:
  - locally-finite-splittings-preserve-rigid-sft-compactifications
  - relative-seeds-over-free-products-have-finite-ropes
  - quantum-rigidity-is-decided-on-the-derived-subshift
distinct_from:
  relative-seeds-over-free-products-have-finite-ropes: that shows the rope cannot be seeded over Z^2 * Z and must use K_M's scaling letters; this builds the scaling seed and the numeral reader those letters allow.
  bs12-rigid-seed-is-its-normal-form: that is the BS(1,2) template, a unique-parent tree with a cyclic sink line; here the vertex group is Z^2, the tree has no unique parent, and a reader layer is added.
  higman-clapham-towers-leave-the-seed-form-at-three-steps: that proposes the rope test; this supplies step 1 of the build order and locates the remaining obstacle.
---
**ESTABLISHED** for parts 1–3 (lane proof, bh-invent-15, 2026-09-18; not reviewed). Part 4 is
**OPEN**, and it is stated exactly. The facts about `K_M` are from Cohen, CGT §9.6, as recorded
in `higman-clapham-towers-leave-the-seed-form-at-three-steps`.
- `K = ⟨x, y, t | [x,y]⟩ = Z^2 * Z`.
- `K_M` is the HNN extension of `K` with stable letters `r_i` and `l_j`.
- `r_i` identifies `A_i = ⟨t(a_i,b_i), x^m, y^m⟩` with `⟨t(c_i,0), x^{m^2}, y⟩`, sending
  `x^m ↦ x^{m^2}` and `y^m ↦ y`. The letters `l_j` send `x^m ↦ x` and `y^m ↦ y^{m^2}`
  (Cohen's left moves).

## Theorem
1. **The scaling part.** `S_M = ⟨x, y, r_i, l_j⟩ ≤ K_M` is the multiple HNN extension of `Z^2`
   along the index-`m^2` maps `x^m ↦ x^{m^2}, y^m ↦ y` (one copy for each `r_i`) and
   `x^m ↦ x, y^m ↦ y^{m^2}` (one for each `l_j`).
2. **It is in `𝒞` at linear forcing.** This is a finite graph of free abelian groups with
   finite-index edge groups. So `S_M ∈ 𝒞` by `locally-finite-splittings-preserve-rigid-sft-compactifications`.
   Its seed consists of pointers to one sink `Z^2`-coset, carrying `C_Z ⊠ C_Z` there, and forces
   at linear radius (§3 of `heisenberg-rigid-seed-certifies-only-the-malcev-normal-form`).
3. **The numeral reader.** Let `I ⊆ N` be any set whose base-`m` numerals, read
   most-significant digit first, form a regular language; Cohen's rope set is one example.
   Then the seed of part 2 extends to an SFT with seed `(Y^+, π)` whose forced point `y_*^+`
   satisfies:
   - it carries at each element `h` a bit `v(h)`;
   - `v(h) = [α ∈ I]` whenever `h` sits at position `(α, 0)`, with `α ≥ 0`, relative to the
     origin of its `Z^2`-coset;
   - `v(h) = ⊥` elsewhere.

   On the sink coset, every label of `y_*^+` on `Ball(n)` is locally forced within `Ball(O(n))`.
   In particular the rope marks `v(x^α)` are forced at radius `O(|x^α|)`: the reading path has
   `log_m(α+1)` steps, and `log α = O(|x^α|)` because `S_M` distorts `x` at most exponentially.
   On other cosets the same bound holds with `α` measured from the coset origin.
4. **The rigidity gate (RR), OPEN.** The seedless boundary `∂Y^+` contains **unanchored descent
   chains**: infinite `l`-paths whose markers never reach an origin. On each such chain the
   reader state is fixed only up to a finite choice. For Cohen's `I` (all digits in
   `{1, …, 2n}`) this is one free bit per chain. By
   `quantum-rigidity-is-decided-on-the-derived-subshift`, `Y^+` is rigid iff `∂Y^+` is. Whether
   the free chain bits break rigidity is the open step.

## Proof
**1.** `A_i ≅ ⟨x^m, y^m⟩ * ⟨t(a_i, b_i)⟩` acts on the Bass–Serre tree of `K = Z^2 * Z`. Its
stabilizer of the base vertex is `A_i ∩ Z^2 = ⟨x^m, y^m⟩`. Likewise the image intersects `Z^2`
in `⟨x^{m^2}, y⟩`, which is the image of `⟨x^m, y^m⟩`. For a subgroup `L` of the base with
`φ(L ∩ A) = L ∩ φ(A)`, Britton's lemma shows that `⟨L, stable letters⟩` is the HNN extension of
`L` along the restrictions. Apply this with `L = Z^2`.

**3.** Everything is relative to the seed of part 2: a unique sink coset, and the tree path from
it to every other coset.
- **Layer M (origins).**
  - Each coset `gZ^2` carries `C_Z ⊠ C_Z` markers, meaning signs of coordinates relative to an
    origin, together with residues `(α mod m, β mod m)`.
  - Along `l`, from `h` at position `(α, β)` with `α = a + mα'` and `β = b + mβ'`,
    `x^m l = l x` and `y^m l = l y^{m^2}` give `hl` at position `(α', m^2 β')` in the coset of
    label `(a, b)`.
  - So the markers and residues of `hl` are functions of those of `h`, plus a check that the
    origin lies within `2m` of `h`. That is the case exactly when `α, β ∈ [0, m−1]`, where `hl`
    is the new origin. The transport rules along `r_i` are the same with `(m^2 α', β')`.
  - The tree has no cycles, so transporting the origin from the sink gives one consistent
    system. Each rule is forced in both directions, so layer M is forced from the seed at
    linear radius, as in the BS(1,2) template.
- **Layer Q (reader).**
  - Fix a deterministic automaton `𝒜` reading numerals most-significant digit first, with
    start state `q_0`.
  - On elements with y-marker `*` and x-marker in `{*, −}` (row `β = 0`, `α ≥ 0`), impose:
    - `q(h) = q_0` if `h` is an origin;
    - otherwise `q(h) = δ(q(hl), α(h) mod m)`.
  - Elsewhere `q = ⊥`, which is locally visible from the markers.
  - Along `l` the row `β = 0` maps to itself with `α ↦ ⌊α/m⌋`. So from `(α, 0)` the `l`-path
    passes through `(⌊α/m^k⌋, 0)` and reaches the origin after `L = ⌈log_m(α+1)⌉` steps.
  - Every element has a unique `l`-neighbour, so `q` is determined **bottom-up from the
    origin**. Reading from the origin toward `h`, the digits met are most-significant first.
    Hence `q(h) = 𝒜(numeral of α)`, and `v(h) := [q(h) accepting] = [α ∈ I]`.
- **Seed and forcing.**
  - `[π] ∩ Y^+ = {y_*^+}`, because layers M and Q are determined by the base seed.
  - The stabilizer is still trivial.
  - Each deduction reads one bounded ball, so `y_*^+` is locally forced.
  - The deduction of `v(h)` uses the `L`-step path below `h`, which lies within
    `O(L) = O(|h|)`.

**4.** Take a limit `g_N · y_*^+` with the base point at positions `(α_N, 0)`, `α_N → ∞`, and
low digits converging to an `m`-adic `α_∞`.
- In the limit, the `l`-path from the base point never meets an origin, because every marker
  on it is `−`.
- `q` along it obeys only `q(h) = δ(q(hl), digit)`, that is, a backward orbit of `𝒜` along the
  digit stream.
- For Cohen's `I` the minimal automaton has states `{ok, bad}`, with `bad` absorbing. So a chain
  whose digits all lie in `{1, …, 2n}` admits both `q ≡ ok` and `q ≡ bad` from some point on.
  Both are limits: choose the high digits of `α_N` all good, or with one bad digit.
- These chains lie in `∂Y^+`. They are neither isolated nor removed by the derived-subshift
  criterion.

## For the SEED TOWER team
- **Step 1 is done up to (RR).** The scaling letters carry positions as `m`-ary digit streams,
  and a finite-state reader turns them into rope marks at linear radius.
- **Part 3 is the only possible reader shape.** The rope set `I` is not eventually periodic.
  So no sliding-block factor of the base seed can mark it: a factor sees only `α mod m^k`. The
  reader must be an extension layer anchored at origins. Its freedom lives exactly on
  unanchored chains.
- **Two ways to close (RR).**
  - (a) Prove that a free bit per chain is rigidity-neutral. Such a bit is constant along its
    chain up to a single switch, like the `+/−` switch of `C_Z`, which is rigid.
  - (b) Choose `𝒜` co-deterministic, so that backward orbits are unique. Then the layer is a
    deterministic extension of `∂Y`, and quantum rigidity is stable under deterministic
    extensions.

    `I` is regular, so its reversal is regular, and the reader can be run in the other direction
    with the verdict relayed back along the chain. Whether some automaton for `I` gives unique
    backward orbits on every digit stream is a finite check on `𝒜`.
- **Next step once (RR) is closed.** Step 2: the rope `⟨t_α : α ∈ I⟩` as a relative seed over
  `K_M` whose `t`-edge marks are `v(x^α)`.

## Lesson for general BH
- **Scaling makes positions local.** Scaling HNN letters turn a position into a digit stream
  along a unique descent path, so a finite automaton anchored at origins can mark any
  regular numeral set at linear forcing radius. That is exactly what Higman ropes need.
- **The cost is at infinity.** On chains that never reach an origin, the reader keeps a
  finite free choice. Rope seeding therefore reduces to one clean question: is a
  finite-state choice at infinity rigidity-neutral? A co-deterministic reader would make it
  a deterministic extension.

## Referee (bh-ref-kourovka-a, 2026-09-18): parts 1–2 PASS; part 3 PASS after a required correction; part 4 correctly OPEN

- **Part 1.**
  - `A_i = g(⟨x^m,y^m⟩ * ⟨t⟩)g^(-1)` with `g ∈ Z²`, so `A_i ∩ Z² = ⟨x^m, y^m⟩`, and likewise for the
    image `⟨x^(m²), y⟩`.
  - The subgroup criterion is standard: `⟨L, stable letters⟩` is the HNN extension of `L` when
    `φ(L ∩ A) = L ∩ φ(A)`, by Britton's lemma.
  - Both edge groups have index `m²`. Correct.
- **Part 2.** `S_M ∈ 𝒞` by `locally-finite-splittings-preserve-rigid-sft-compactifications`. I did not
  re-check the linear forcing radius.
- **Part 3, a required correction.** The transport rules of layer M and the reader rule of layer Q
  are consistent only if they are **conditioned on the tree orientation of the part-2 pointers**, so
  that they are applied only along edges that point away from the sink.
  - Each coset `P` has `m²` `l`-children `P x^a y^b l Z²` (origin `o_P x^a y^b l`) and `m²`
    `l^(-1)`-children `P y^(b'') l^(-1) Z²` (origin `o_P y^(b'') l^(-1)`, with `b'' ∈ [0, m²−1]`).
  - In an `l^(-1)`-child `C`, an element `h` at `(α, 0)` with `α ≡ 0 mod m` has `hl` in the parent, at
    position `(α/m, b'')`. For `b'' ≠ 0` that is off row 0, where `q = ⊥`.
  - So the unconditioned rules `q(h) = δ(q(hl), ·)`, and the transport formula along that `l`-edge,
    contradict the seed. The forced point would not exist.
  - **The fix.** Apply both rules only when `hl` lies in a child coset, which the pointer at `h` shows,
    and put `q = ⊥` otherwise.
  - Only the first step of an `l`-path can go to a parent, because a coset entered along an `l`-edge
    has its parent edge on the `l^(-1)` side.
  - With the fix, `v(h) = [α ∈ I]` holds for every `h` whose `l`-edge points away from the sink. That
    includes the whole sink coset, which carries the rope marks `v(x^α)`.
  - The sentence "on other cosets the same bound holds" is true only in that range. It fails at
    `α ≡ 0 mod m` in `l^(-1)`-children.
- **Part 3, a smaller wording point.** "Markers and residues of `hl` are functions of those of `h`" is
  inaccurate for residues, because `⌊α/m⌋ mod m` is the next digit. The residues of each coset are
  forced within the coset, from its origin, by `x`/`y` steps. Only the origin location and the signs
  are transported along `l`.
- **Part 3, checked.**
  - Origins: `hl` is the origin of the `(a,b)`-child iff `h` sits at exactly `(a,b)`, which is a local
    check.
  - Reading along `l` gives `(⌊α/m^k⌋, 0)`, with most significant digits first from the origin, so
    `q(h) = 𝒜(numeral(α))`.
  - `|x^(m^k)| ≤ 2k+1` (from `x^m = l x l^(-1)`), so the forcing radius is `O(|x^α|)`.
- **Part 4.** The limit argument for unanchored chains and the `{ok, bad}` free bit is correct, so
  (RR) is correctly stated as OPEN.

**Not checked:**
- the claim that "no sliding-block factor can mark `I`" (a heuristic);
- the derived-subshift criterion cited for (RR).
