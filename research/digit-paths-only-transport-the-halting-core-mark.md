---
rg: 2
id: digit-paths-only-transport-the-halting-core-mark
kind: claim
title: An E-coset of B_1 meets H_1 in at most one P-coset gP, and it is core for A_± iff all syllables of g but the last lie in P_± and the last K_M-syllable lies in ⟨U⟩P; so the digit paths only transport the core mark, and its negative certificate is the single K_M predicate [g ∈ ⟨U⟩P]
distinct_from:
  halting-pair-seeds-need-a-two-sided-core-mark: that shows the core mark needs a terminating negative certificate and proposed running it along digit paths; this proves the digit paths need only carry it, and locates the certificate in one predicate on K_M.
---

**ESTABLISHED for Lemmas 1–3 (lane proof, bh-g1-universal-point, 2026-09-18; elementary, not reviewed).** This is
the digit-path half of the core-mark split. bh-invent-15 keeps the numeral reader on `K_M`. Notation is that of the
two required nodes:
- `E = ⟨t, a_i⟩ ≤ B_1`, with `E ∩ H_1 = P = ⟨t_α : α ∈ I⟩ ⊆ K_M`, by the subgroup lemma;
- `P_± = ⟨U⟩ * ⟨d⟩ * F_±`, with `F_+ = F(b)` and `F_- = ⟨b_j c_j⟩`, inside
  `H_1 = K_M * (C × F(b)) * ⟨d⟩`.

## Lemmas

**Lemma 1 (single trace).** For `h ∈ B_1`, the set `hE ∩ H_1` is empty or a single coset `gP` with `g ∈ H_1`.

*Proof.* If `g, g' ∈ hE ∩ H_1`, then `g⁻¹g' ∈ E ∩ H_1 = P`. ∎

**Lemma 2 (core bit).** `hE ∩ P_± ≠ ∅` iff `hE ∩ H_1 = gP ≠ ∅` and `g ∈ P_± P`. Write the normal form of `g` in the
free product `H_1` as `g = g' g_k`, where `g_k` is the last syllable.
- If `g_k ∈ K_M`: then `g ∈ P_± P` iff `g' ∈ P_±` and `g_k ∈ ⟨U⟩P`.
- Otherwise: `g ∈ P_± P` iff `g ∈ P_±`.

*Proof.*
- `P_± ⊆ H_1` gives the first equivalence, by Lemma 1.
- `P_±` is a free product of subgroups of the free factors. So an element of `H_1` lies in `P_±` iff each of its
  syllables lies in the corresponding subgroup (`⟨U⟩`, `⟨d⟩` or `F_±`).
- Case `g_k ∈ K_M`: for `p ∈ P ⊆ K_M`, `gp = g'·(g_k p)` is reduced, the last syllable disappearing if `g_k p = 1`.
  So `gp ∈ P_±` iff `g' ∈ P_±` and `g_k p ∈ ⟨U⟩`. Some `p ∈ P` works iff `g_k ∈ ⟨U⟩P`.
- Otherwise, for `p ≠ 1`, `gp` has the extra syllable `p`. So `gp ∈ P_±` forces `g ∈ P_±`, and `p = 1` then works. ∎

**Lemma 3 (consistency).** The predicate `𝔠(g_k) = [g_k ∈ ⟨U⟩P]` is constant on right `P`-cosets. So the core bit
read at any point of the trace `gP` is the same, and the mark is well defined on the whole coset `hE`.

## What the digit paths carry

- **Only transport.** The core mark is a single bit per `E`-coset.
  - It moves along the coset by the local rule "`𝔪(x) = 𝔪(xt) = 𝔪(xa_i)`".
  - At the trace `gP` it must equal the syllable condition of Lemma 2 conjoined with `𝔠(g_k)`.
  - The syllable part "`g' ∈ P_±`" says that the `K_M`-piece containing `g` is a core piece of the Kurosh gluing
    for `(H_1, P_±)`. The lead's core-marked Kurosh gluing reads this locally; that step is cited, not re-proved.
- **No computation runs on digit paths.**
  - `E` is free, so an `E`-coset contains no `Z²`, and no space-time diagram fits in it.
  - Independently, bh-invent-15 (27b0124da) shows that a reader which is a deterministic function of the seed
    along the tree is a sliding-block factor, so it marks only residue-periodic predicates. `[h ∈ P_± E]` depends
    on the halting set and is not residue-periodic in general, so every digit-path evaluation fails.
  - The only grid nearby is `K = ⟨x, y⟩ ≅ Z²` inside `K_M`.
  - The negative certificate therefore cannot be laid out along the digit letters. It must be computed on `K_M`'s
    sheet and read at `g_k`.
- **The negative certificate, exactly.** It is the value `0` of `𝔠(g) = [g ∈ ⟨U⟩P]` for `g ∈ K_M`.
  - Equivalently: the rope coset `gP` misses the machine subgroup `⟨U⟩`.
  - For `g = x^{-β}`: `x^{-β} t_α = x^{-β-α} t x^{α}`, so `𝔠` asks whether some rope translate of the point `β`
    halts. It combines the numeral reader (`α ∈ I`) with the halting set (`⟨U⟩ ∩ K`).
  - Since `𝔠` is constant on `gP`, a mortal decider for `⟨U⟩P` evaluated once at `g` certifies the whole coset.
    No search over `I` is needed.

## Remaining items (not proved here)

- **(a) `K_M` side (bh-invent-15, bh-free-56).**
  - A locally forced, mortal evaluation of `𝔠` on `K_M`'s sheet, forced in both directions.
  - Decidability of `⟨U⟩P` is not claimed here. It is the product-set analogue of bh-free-56's decidability of `P`
    and `⟨U⟩` (213e9e339), and it should follow from their normal forms.
- **(b) Cosets with empty trace.**
  - If `hE ∩ H_1 = ∅`, the coset is not core. Its mark must be forced to `0` by locating the trace, i.e. by
    deciding `h ∈ H_1 E`.
  - Britton reduction turns this into `P`-membership of the pieces of `h`. `P` is the regular rope, which
    bh-invent-15's numeral reader marks.
  - That this can be forced at bounded radius is a sketch, not proved. It is the tree half of gate RR.
  - Alternative (bh-invent-15, 1ee36937b): keep one free bit at infinity per `E`-coset, linked by seed-true rules
    (a region bit plus links). This shares their remaining gate `(C_D)`, centrality of one idempotent against far
    base marginals.

## Lesson for general BH

- **Push the negative certificate onto one predicate at the trace.** A two-sided core mark on HNN edge cosets never
  needs a computation inside the edge group.
- **Why this works here.**
  - The edge group meets the base in one coset (Lemma 1).
  - Kurosh normal form reduces "core" to syllable-wise membership plus one predicate at the last syllable (Lemma 2).
  - That predicate is constant on the trace (Lemma 3).
- **What the edge cosets do.** Free edge groups have no room for space-time diagrams. They serve as transport, and
  all computation belongs to the grid factor of the vertex group.
- **Where the halting pair's CAP content sits.** In one `K_M` predicate, `[g ∈ ⟨U⟩P]`: the machine subgroup
  against the rope.
