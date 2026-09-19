---
rg: 2
id: kurosh-relative-seeds-and-the-b1-digit-splitting
kind: claim
title: Relative seeds pass to free products of factor subgroups by re-splitting (a corollary of the gluing theorem), so B_1 of the reordered Higman tower is seeded modulo the input; the pair (B_1, <t, a_i>) reduces through new splittings of B_1 to relative seeds for stable-letter subgroups of the digit group
distinct_from:
  relative-seeds-glue-graphs-of-groups-into-class-c: that glues relative seeds for subgroups inside ONE vertex group; this derives, as a corollary, relative seeds for free products of subgroups of SEVERAL free factors, and applies it to the Higman tower.
  relative-seeds-over-free-products-have-finite-ropes: that is bh-invent-15's constraint that seeded subgroups of P * Q meet conjugates of Q in finitely many (C ∩ P)-cosets; the Kurosh-standard subgroups here satisfy it with one coset.
---

**Status.**
- §§1–3 are **ESTABLISHED** (lane proof, bh-invent-14, 2026-09-18; elementary; not reviewed).
  They rest on the gluing theorem `relative-seeds-glue-graphs-of-groups-into-class-c` and on
  `quantum-rigidity-is-product-stable`.
- §4 **reduces** `(B_1, ⟨t, a_i⟩)` to three stable-letter pairs. Those are **OPEN**.
- Tower notation is from `reordered-aanderaa-cohen-tower-has-fg-associated-subgroups`, after D. E.
  Cohen, *Combinatorial Group Theory*, CUP 1989, §§9.4 and 9.6.

## 1. Two closure facts for 𝓡

- **(P) Products.** If `(A_j, C_j) ∈ 𝓡` for `j = 1, 2`, then `(A_1 × A_2, C_1 × C_2) ∈ 𝓡`.
  - Take the product SFT and the product seed pattern. The product point is isolated, with
    stabilizer `C_1 × C_2`.
  - The orbit closure of a product point under the product group is the product of the orbit
    closures.
  - Rigidity is product-stable.
- **(Cj) Conjugation.** `(A, C) ∈ 𝓡` implies `(A, gCg^{-1}) ∈ 𝓡`: use `g·y_*` and the translated
  seed pattern.

## 2. Kurosh corollary

**Theorem K.** Let `Λ = V_1 * ⋯ * V_r` with every `V_u` finitely generated. Let `C_u ≤ V_u` be
finitely generated, and put `C = C_1 * ⋯ * C_r`. Suppose that for every `u`:
- `(V_u, C_u) ∈ 𝓡`;
- `C_u ∈ 𝒞`, where `C_u = 1` is allowed, and then this reads `V_u ∈ 𝒞`.

Then `(Λ, C) ∈ 𝓡`.

*Proof.*
- **Re-split.** `Λ` is the fundamental group of the star-shaped graph of groups with centre vertex
  `C` and leaves `V_u`, the leaf `V_u` attached to the centre along `C_u`. Amalgamating `V_u` onto
  the free factor `C_u` of `C`, one leaf at a time, replaces `C_u` by `V_u`, giving
  `V_1 * ⋯ * V_r`. All vertex groups are finitely generated.
- **Apply item 1 of the gluing theorem with the centre as target** (`C = V_u` for the centre). It
  needs a relative seed for each oriented edge:
  - `(V_u, C_u) ∈ 𝓡`, which is given;
  - `(C, C_u) ∈ 𝓡`. This is item 1 again, for the free product `C = ∗ C_u` with trivial edges and
    target the vertex `C_u`. Its edge conditions are `(C_v, 1) ∈ 𝓡`, i.e. `C_v ∈ 𝒞`, for all `v`.

  No vertex group `V_u` has to lie in `𝒞`. ∎

*Check.* bh-invent-15's constraint (`relative-seeds-over-free-products-have-finite-ropes`) holds
here with a single coset: `G_C ∩ V_u = C_u`.

*Relation to the lead's version.* bh-invent-03 is proving a general core-marked Kurosh gluing, with
`A_j ∈ 𝒞` and `S` of finite core. Theorem K is the Kurosh-standard special case: the core is one
star. It needs `C_u ∈ 𝒞` instead of `V_u ∈ 𝒞`, and it follows from the existing theorem with no new
rigidity argument.

## 3. Applications to the reordered tower

In `K = ⟨x,y⟩ * ⟨t⟩`, `K_M`, `H_1 = K_M * (C × F(b)) * ⟨d⟩` and `B_1`:

1. `(K, ⟨x⟩ * ⟨t⟩) ∈ 𝓡`, by Theorem K, from `(Z^2, ⟨x⟩) ∈ 𝓡` (free abelian case) and
   `⟨x⟩, ⟨t⟩ ∈ 𝒞`.
   - Likewise `(K, ⟨x^m, y^m⟩ * ⟨t⟩)` and `(K, ⟨x^{m^2}, y⟩ * ⟨t⟩)`.
   - By (Cj), this covers every associated subgroup `⟨t(a,b), x^m, y^m⟩`, `⟨t(c,0), x^{m^2}, y⟩`
     of `K_M`. So `K_M ∈ 𝒞`, confirming 0d6bf2845 step 1.
2. `(K_M, ⟨x,t⟩) ∈ 𝓡` and `(K_M, ⟨t_i, x^m⟩) ∈ 𝓡`, by item 1 of the gluing theorem over the HNN
   splitting of `K_M` with vertex `K`. Both subgroups lie in `K`, via 1 and (Cj).
3. **Assuming the input seed `C ∈ 𝒞`:**
   - `(C × F(b), 1 × F(b)) ∈ 𝓡` by (P).
   - `(H_1, A°)` and `(H_1, A_i°) ∈ 𝓡` by Theorem K. Here `A° = ⟨x,t⟩ * F(b) * ⟨d⟩` and
     `A_i° = ⟨t_i,x^m⟩ * F(b) * ⟨d⟩`, and as sets these are free products of factor subgroups.
   - `H_1 ∈ 𝒞`.
   - So **`B_1 ∈ 𝒞`**, and `(B_1, D) ∈ 𝓡` for every `D ≤ H_1` with `(H_1, D) ∈ 𝓡`.
   - **The tower through `B_1` is seeded modulo the input alone.**

## 4. The pair `(B_1, Q)`, `Q = ⟨t, a_1, …, a_k⟩` (`k = 2n`)

**Three new splittings (proved by comparing presentations).** Put `Q_2 = (C × F(b)) * ⟨d⟩` and
`Y = F(b) * ⟨d⟩ ≤ Q_2`.
- **(S1)** `B_1 = J_K *_(F(a)) J_Q`, with:
  - `J_K = HNN(K_M; a_i : ⟨x,t⟩ → ⟨t_i,x^m⟩)`;
  - `J_Q = HNN(Q_2; a_i : Y → Y)`, where `b_j ↦ b_j`, `d ↦ b_i d` is an automorphism of `Y`;
  - `F(a) = ⟨a_1, …, a_k⟩` free in both factors.

  `φ_i` respects `H_1 = K_M * Q_2` factorwise, and the presentations coincide.
- **(S2)** `J_K = K_M *_(F(x,t)) J`, where `J = HNN(F(x,t); a_i : x ↦ x^m, t ↦ x^{-i}tx^i)`. The
  associated subgroups lie in `F(x,t)`.
- **(S3)** `J = HNN(Z_J; t : Σ → Σ, identity)`, where:
  - `Z_J = ⟨x, a_i | a_i^{-1}xa_i = x^m⟩` is the `k`-letter `BS(1,m)` (the digit group);
  - `Σ = ⟨σ_i = a_i x^{-i}⟩`.

  Indeed `a_i^{-1} t a_i = x^{-i} t x^i` is equivalent to `[t, σ_i] = 1`.

**`Q = F(a) * ⟨t⟩` and `F(a) ∩ Σ = 1`.**
- The subgroup lemma (in c9d2e1ece), applied to `P = F(a)` in (S3), gives
  `⟨F(a), t⟩ = HNN(F(a); t centralizing F(a) ∩ Σ)`.
- `Q = ⟨F(a), t⟩` is free, by (R1). So `F(a) ∩ Σ = 1`, since otherwise `Q ⊇ Z^2`.
- Hence `Q = F(a) * ⟨t⟩`, and `Q ∩ Z_J = F(a)`.

**Reduction.** By item 1 of the gluing theorem along (S1) and (S2), with `Q ≤ J ≤ J_K`:
- `(B_1, Q) ∈ 𝓡` ⇐ `(J_K, Q)`, `(J_K, F(a))`, `(J_Q, F(a))`;
- `(J_K, ·)` ⇐ `(J, ·)`, `(J, F(x,t))`, `(K_M, F(x,t))`.

The last two hold: `(J, F(x,t))` by item 1 with target the base (edge seeds `(F_2, F_2)` and
`(F_2, ⟨t_i,x^m⟩)`, free-group corollary (a)), and `(K_M, F(x,t))` by §3.2. So:

`(B_1, Q) ∈ 𝓡` **⇐** `(J, Q)`, `(J, F(a))` and `(J_Q, F(a))`.

**What is open: the stable-letter pairs.** In all three, the subgroup acts on a Bass–Serre tree
with finite quotient and trivial vertex stabilizers. Its core contains all of `F(a)`'s stable
edges.
- **`(Z_J, F(a))`,** hence `(J, F(a))` by gluing with the edge `(Z_J, Σ)`.
  - `Z_J`'s tree is **locally finite**, of valence `k(m+1)`. So the core marks finitely many edges
    at each core vertex.
  - The vertex label needs only a `Z`-seed plus finite marks. This is the natural first case, and
    it is the digit counter of bh-invent-15's build order.
- **`(J, Q)`,** where `Q = F(a) * ⟨t⟩` in the HNN `(S3)`.
  - A core vertex must mark the double coset `F(a)Σ` of `Σ`-edges, which is right
    `Σ`-invariant, with stabilizer `F(a)`.
  - The gluing theorem marks one coset per vertex. Here the vertex needs a union indexed by
    `F(a)`.
- **`(J_Q, F(a))`.** A core vertex marks the identity `Y`-coset for each digit letter, in and
  out. That is a product of relative seeds for `(Q_2, Y)`, which exist by Theorem K given
  `C ∈ 𝒞`, plus a `Q_2`-seed to kill the stabilizer.

The common statement to prove is a **cocompact-core gluing theorem**:
- *Hypothesis:* a subgroup acts on the Bass–Serre tree with finite quotient, and each core vertex
  carries a configuration marking exactly its finitely many orbits of core edges, with the right
  stabilizer.
- *Conclusion:* the subgroup is relatively seeded.

The existing gluing theorem is the case of a one-vertex core, and Theorem K is the star case.

## Lesson for general BH

**Relative seeds follow the subgroup's own splitting.**
- When a subgroup is a free product of factor subgroups, re-splitting the group so that the
  subgroup becomes a vertex turns a new-looking problem into the old gluing theorem. That is
  Theorem K, and it puts the Higman tower through `B_1` into `𝒞` modulo the input.
- The pieces still missing are subgroups generated by **stable letters**: the digit letters of the
  machine. They are not inside any vertex group of any splitting.
- So the seed tower needs one more tool, gluing along a cocompact core, and its first instance is
  the locally finite digit group `(Z_J, F(a))`, the `k`-letter `BS(1,m)`.
- That is where the machine's counting lives. The input seed and the halting pair are the only
  other inputs.
