---
rg: 2
id: spatial-2v-in-affine-hosts-needs-unbounded-fibres
kind: claim
title: A spatial copy of Brin's 2V inside CT_P(Z), or inside any host of piecewise-affine maps of Z-hat such as G_(2,3) and B, has unboundedly large fibres over every periodic slice; so every contracting design, including all rank-two designs with push slopes exactly 2 and 3, is impossible, and a writer needs Conway-type expanding pieces
requires:
  - two-v-in-ct-p-z-needs-degree-rank-two-r
  - blind-commutants-of-push-families-in-ct-p-z-are-trivial
  - brin-thompson-nv-needs-n-minus-one-primes-in-ct-z
distinct_from:
  two-v-in-ct-p-z-needs-degree-rank-two-r: that is a dimension bound (rank of degrees), which does not apply in hosts with translations; this is a fixed-point bound on fibres, which holds in every piecewise-affine host, translations included.
  blind-commutants-of-push-families-in-ct-p-z-are-trivial: that forces the pushes to read hidden data; this forces the hidden data to be infinite over a dense set, and kills every design whose cylinders stay finitely fragmented.
---

**ESTABLISHED** for items 1–3 (lane proof, elementary; not independently reviewed; no priority
claimed). **OPEN:** does `2V` embed in `CT(Z)`, `B` or `G_(2,3)`? Kourovka 17.58 stays OPEN.

## Setting

- **Host.** Let `H` be a group of homeomorphisms of a clopen `Z ⊆ Ẑ_P`, each of which is affine
  (`y ↦ cy + d`, `c ∈ Q_{>0}`, `d ∈ Q`) on each piece of a finite box partition.
  - This covers `CT_P(Z)` (canonical pieces) and the RCWA hosts `B = V_(2,1)(⟨a⟩)`,
    `B_3 = V_(3,1)(⟨a⟩)` and `G_(2,3) = ⟨B, B_3⟩`.
  - For `h ∈ H`, let `E(h) = Fix(h) ∖ int Fix(h)`.
- **Embedding.** A *spatial* embedding is an injective `ρ : 2V → H` together with a continuous
  surjection `q : Z → C × C` satisfying `q ∘ ρ(g) = g ∘ q`. By Matte Bon's Extension Theorem with
  `r = 1`, every embedding `2V → CT_{3}(Z)` is spatial
  (`brin-thompson-nv-needs-n-minus-one-primes-in-ct-z`, item 3).
- **Periodic slice.** Let `p ∈ C` be eventually periodic. The *slice* is `S_p = {p} × C`.

## Statement

1. **Finite non-interior fixed sets.** For every `h ∈ H`, `E(h)` is finite.
2. **Unbounded fibres.** For a spatial embedding, every `p` and every `N`, all but finitely many
   `x ∈ S_p` have `|q^{-1}(x)| > N`. So all but countably many points of every periodic slice have
   infinite fibres. The same holds for the slices `C × {p}`.
3. **Contracting designs are dead.** Let `s_i, t_j` be the images of the two stacks' pushes.
   Suppose every piece of every `s_i` maps its box onto a sub-box with slope `c`, where `c` is an
   integer with `v_2(c) ≥ 1`. Suppose likewise every piece of every `t_j` has integer slope with
   `v_3(c) ≥ 1` (for `P ⊋ {3}`: every prime of `P'` is contracted along every joint address). Then no
   spatial embedding has these pushes.
   - In particular, all designs `s_i(x) = 2x + f_i(x)` and `t_j(x) = 3x + g_j(x)`, with offsets
     read from any finite residue data, are impossible. That includes the natural mixed-radix grid
     and any finite automaton of offsets.

## Proof

**Item 1.** On a piece, `y ↦ cy + d` either is the identity (interior), or has `c = 1`, `d ≠ 0` and
no fixed point, or has `c ≠ 1` and at most one fixed point.

**Item 2.**
- **The element.** Pick `h_1 ∈ V` with `p` as an isolated attracting fixed point, and let
  `g ∈ 2V` equal `h_1 × id` near `S_p`. Then near `S_p`, `Fix(g^k) = S_p` for every `k ≥ 1`, and
  `g^k` is nontrivial near each point of `S_p`.
- **The power.** Let `x ∈ S_p` with `|q^{-1}(x)| ≤ N`. Then `ρ(g)` permutes the fibre `q^{-1}(x)`,
  so `η = ρ(g^{N!})` fixes it pointwise.
- **Some fibre point is a non-interior fixed point.** If `η = id` on open sets `N_z ∋ z` for every
  `z` in the fibre, then `q^{-1}(O) ⊆ ∪ N_z` for some open `O ∋ x`, since `q` is closed. As `q` is
  onto, every `y ∈ O` is `q(z′)` with `η z′ = z′`, so `g^{N!} y = y`. Hence `O ⊆ Fix(g^{N!})`,
  which is impossible.
- **Counting.** So each such `x` contributes a point of `E(η)`, and distinct `x` contribute
  distinct points. By item 1, only finitely many such `x` exist.

**Item 3.** Let `M*` be the least common multiple of all piece moduli.
- **Bounded fragmentation.** Under the hypotheses, a box whose modulus is divisible by `M*` lies in
  a single piece of every push, and its image is again such a box.
  - Write the joint cylinder in interleaved order,
    `s_{u_n} t_{v_n}(Z) = s_{u_1} t_{v_1} ⋯ s_{u_n} t_{v_n}(Z)`, which is allowed because the
    families commute.
  - Each pair multiplies moduli by a multiple of 6 (a multiple of `∏ P'` in general). So after
    `L = max_q v_q(M*)` pairs every box is that fine, and splitting can happen only during the first
    `L` pairs.
  - Hence each joint cylinder is a union of at most `K = N^{2L}` boxes, where `N` bounds the number
    of pieces.
- **Shrinking.** The moduli gain `2^n 3^n` (every prime of `P'` in general), so the boxes shrink to
  points.
- **Conclusion.** Fibres are nested intersections of such cylinders, so they have at most `K`
  points. This contradicts item 2. `∎`

## What survives, and the connection to Conway's map

A surviving design needs pushes with *expanding* pieces, of slope `3/2`, `3/4`, `4/3`, `9/8`, and so
on. Only then can joint cylinders fragment into unboundedly many boxes and carry Cantor fibres over
the periodic slices.
- These are exactly the slopes of Conway's amusical permutation, whose itinerary coding is the full
  3-shift (`conway-amusical-permutation-is-the-full-three-shift`).
- So the only remaining candidates are writers built from shift-like expanding–contracting pieces.
  Such pieces must also meet the rank bound (`two-v-in-ct-p-z-needs-degree-rank-two-r`) and the
  blind-commutant constraint.
- **Next test.** Find two commuting Cuntz families assembled from pieces of `[[α]]`-type elements,
  with infinite fibres. Alternatively, prove that fragmentation driven by a full shift always
  creates fibres of bounded Cantor–Bendixson type that item 2 can still exclude.

**For bh-invent-02 (`G_(2,3) = ⟨B, B_3⟩`).**
- Items 1–3 hold verbatim in `G_(2,3)` and `B`, because the odometer only adds translation pieces,
  which have no fixed points. So translations do not rescue contracting writers.
- The rank bound fails there, but the fibre bound does not. A `2V` in `G_(2,3)` must likewise use
  expanding pieces and unbounded fragmentation.
- Every element of `B` is, on `Z_2`, a prefix replacement with odometer tails. So `B` does have
  expanding pieces: the pops `x ↦ x/2` on `2Z_2`.

**Lesson for general BH.**
- **A fixed-point budget.** In a host of piecewise-affine maps every element has finitely many
  non-interior fixed points. A product structure, however, needs whole slices of such points. So any
  copy of a product host must blow those slices up into unboundedly large fibres.
- **What that rules out.** Uniformly contracting codings, the natural mixed-radix grids, cannot do
  this.
- **What is left.** Only shift-like pieces that expand one prime while contracting another can
  fragment enough. That points the search for writers, and for intermediate growth in `CT(Z)`, at
  Conway-type dynamics and nowhere else.
