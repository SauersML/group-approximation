---
rg: 2
id: baumslag-gersten-splits-over-bs12-edges
kind: claim
title: The Baumslag--Gersten group is a non-ascending HNN extension of the height-two Baumslag--Solitar tower over BS(1,2) edges, whose edge can act transitively, so the stable-permutation route reduces BG in B_A to a type (A) actor for the tower with shift-symmetric edges
distinct_from:
  stable-permutation-hnn-of-type-a-actor-is-type-a: that is the general permanence engine; this supplies, for BG, a splitting whose edge group can meet its orbit-finiteness clause, and realizes that clause and the permutation clause explicitly.
  type-a-actors-have-no-proper-power-cyclic-edge-splittings: that kills type (A) actions of BG through its cyclic splitting, whose edge can never be orbit-finite; this uses the other splitting, over BS(1,2), to which that invariant does not apply.
  baumslag-solitar-towers-have-no-faithful-linear-image: that shows the tower K is not linear; this makes K the vertex group of a splitting of BG and isolates K in a symmetric actor as the remaining input.
  baumslag-gersten-group-satisfies-boone-higman: that is the open problem; this is a reduction of its permutational form, not a solution.
---

**ESTABLISHED** (lane proof, elementary; not yet refereed; no priority claimed). Items 1–3 are
proved below. The criterion in item 2 is conditional, and its hypotheses are open.

Write `BG = ⟨a, t | b a b^-1 = a^2⟩`, `b = t a t^-1`, and `a_i = t^i a t^-i`.

## Statement

1. **Splitting.** Let `K = ⟨a_0, a_1, a_2 | a_1 a_0 a_1^-1 = a_0^2, a_2 a_1 a_2^-1 = a_1^2⟩`, the
   height-two tower, so that `K = B_0 *_(⟨a_1⟩) B_1` with `B_0 = ⟨a_0, a_1⟩ ≅ BS(1,2) ≅ ⟨a_1, a_2⟩ = B_1`.
   Let `ψ : B_0 → B_1` be `a_0 ↦ a_1`, `a_1 ↦ a_2`. Then `BG ≅ K*_ψ` via `t ↦ t`, and the
   extension is non-ascending (`B_0 ≠ K ≠ B_1`).
2. **Criterion.** Suppose `Γ` acts on `X` with type (A), and:
   - (R1) `K ≤ Γ` (faithfully);
   - (R2) `B_0` has finitely many orbits on `X`;
   - (R3) some permutation `π` of `X` satisfies `π a_0 π^-1 = a_1` and `π a_1 π^-1 = a_2`;
   - (R4) the map `Γ*_ψ → Sym(X)` extending the action by `t ↦ π` is injective.

   Then `BG` lies in the permutational class `B_A`, so it embeds in a finitely presented simple group.
3. **The edge clauses are realizable.** Let `W = (1/3 + Z[1/2]) ⊔ (−1/3 + Z[1/2]) ⊂ Q`, with
   `a_0 = (r ↦ r + 1)` and `a_1 = (r ↦ 2r)`.
   - `B_0` acts faithfully and transitively on `W`, so (R2) holds.
   - For every bijection `π` of `W` with `π(r + 1) = 2π(r)`, the permutation `a_2 := π a_1 π^-1`
     satisfies `a_2 a_1 a_2^-1 = a_1^2` and (R3). Such `π` exist.
   - This `W` is an orbit of a known type (A) actor containing `B_0`. `2V_τ`
     (`odometer-2v-is-fp-simple-and-contains-bs12`) acts with type (A) on the orbit `S'` of
     `(0^∞, (01)^∞)`, and `S' ≅ W` carries `s = τ × id` to `a_0` and the inverse baker `u` to `a_1`.

## What is left

Only (R1) with this `a_2`, and (R4).
- **`a_2` is not in `2V_τ`.** It would be a homeomorphism of `C × C` conjugating `u` to `u^2`, and
  `h(u) = log 2 ≠ h(u^2)`. So the actor must be larger than `2V_τ`, or different from it, and must
  act on `W` by permutations that are not homeomorphisms of `C × C`.
- **(R1) is a tower problem, not a BG problem.** `K` contains no stable letter. The obstructions
  that need `t`, such as equicontinuity with the smallest-prime argument, or unbounded exponent sums
  (`bg-in-isometric-brick-hosts-needs-unbounded-exponents`), do not apply to `K`. What remains is the
  symmetry: `B_1` must act on `X` as `B_0` does, via the shift.
- **Why the cyclic splitting cannot be used this way.** For `BG = B_0 *_(⟨a_0⟩ → ⟨a_1⟩)`, clause (R2)
  would ask for an orbit-finite `D_1 ⊇ ⟨a_0⟩` with `D_1 ∩ B_0 = ⟨a_0⟩`. `D_1 = ⟨a_0⟩` is impossible by
  the regular-orbit invariant of `type-a-actors-have-no-proper-power-cyclic-edge-splittings`. With
  `BS(1,2)` edges, `D_1 = B_0` itself is transitive.

## Proof

**Item 1.** Substitute `a_1 = t a_0 t^-1` and `a_2 = t a_1 t^-1` in the HNN presentation
`⟨a_0, a_1, a_2, t | a_1 a_0 a_1^-1 = a_0^2, a_2 a_1 a_2^-1 = a_1^2, t a_0 t^-1 = a_1, t a_1 t^-1 = a_2⟩`.
The second relator is the `t`-conjugate of the first, so this is `BG`. Each `B_i` embeds in the
amalgam `K`, and `ψ` is an isomorphism. `a_2 ∉ B_0` and `a_0 ∉ B_1` (normal forms in `K`), so the
extension is non-ascending.

**Item 2.** Apply `stable-permutation-hnn-of-type-a-actor-is-type-a` with `D_i = B_i` and the given
`ψ`. (R3) says that `π d π^-1 = ψ(d)` on generators, hence for all `d ∈ B_0`. By (R2) and (R4) part
(a) applies, so `Γ*_ψ` is of type (A). With `A = K`, `A ∩ D_i = B_i` and `ψ(B_0) = B_1`, so part (b)
gives `⟨K, t⟩ = K*_ψ ≅ BG ≤ Γ*_ψ`. `B_A` is closed under subgroups.

**Item 3.**
- *Transitivity.* `W` is stable under `+1` and `×2`, since `2·(1/3) = 2/3 ≡ −1/3 mod Z[1/2]`. `×2`
  swaps the two cosets and `Z[1/2] = ⟨a_1^k a_0 a_1^-k⟩` acts transitively on each. The stabilizer
  of `1/3` is `⟨a_0^-1 a_1^2⟩`, since `r ↦ 4r − 1` fixes `1/3`, and `2^k/3 + c = 1/3` with
  `c ∈ Z[1/2]` forces `k` even. The action is the affine action of `BS(1,2) ≤ Aff(Q)`, which is
  faithful.
- *The bijection.* `a_0` and `a_1` both act freely on `W`, since `r + 1 ≠ r`, and `2^k r = r` forces
  `r = 0 ∉ W`. Each has countably many orbits, all infinite. Choose one point in each orbit and match
  the orbits by any bijection. Then `π(a_0^n x) = a_1^n π(x)` defines `π` with `π a_0 = a_1 π`.
  Given such `π`, `a_2 a_1 a_2^-1 = π (a_1 a_0 a_1^-1) π^-1 = π a_0^2 π^-1 = a_1^2`, and
  `π a_1 π^-1 = a_2` by definition.
- *The orbit `S'`.* Every point of `S' = 2V_τ·(0^∞, (01)^∞)` is `(x, y)` with `x` eventually constant
  and `y = w(01)^∞`. The tail argument of `odometer-2v-orbit-action-is-type-a` applies unchanged, with
  the second tail `(01)^∞` in place of `0^∞`. So `S' = E × Y'`, where `E ≅ Z` (2-adic integers with
  eventually constant digits) and `Y' = {w(01)^∞}`.
  - Put `r(x, y) = x + Σ_k y_k 2^-(k+1)`. Then `r` is a bijection `S' → W`: `x = ⌊r⌋`, and
    `frac(r) = q/(3·2^j)` with `3 ∤ q` has a unique binary expansion, eventually `(01)^∞` or `(10)^∞`.
  - `s(x, y) = (x + 1, y)` gives `r ↦ r + 1`.
  - `u(x, y_0 y) = (y_0 x, y)` gives `r ↦ y_0 + 2x + 0.y_1y_2… = 2r`.
- *Type (A) on `S'`, following `odometer-2v-orbit-action-is-type-a` step by step.*
  - Pair orbits: `2V` is highly transitive on points of `E × Y'` of one first-coordinate tail type.
    Lengthen prefixes by `c_i` in the first coordinate and by the period `01` in the second, then
    match the complements. This leaves at most three orbits of 2-subsets.
  - Faithfulness: `S'` is dense in `C × C`.
  - Stabilizers: at `p' = (0^∞, (01)^∞)`, germs `(0^a x, w y) ↦ (0^(a') x, w' y)`, with `w, w'` prefixes
    of `(01)^∞` of equal parity, give a homomorphism `Stab(p') → Z^2`,
    `g ↦ (a' − a, (|w'| − |w|)/2)`. Its kernel is the union of the `Γ_(n)` fixing
    `B_n = C(0^n) × C((01)^n)` pointwise. Each `Γ_(n) ≅ 2V_τ` by the complement argument. The element
    `e ∈ 2V` that maps `(0x, 01y) ↦ (00x, 0101y)` on `B_1` and `U_1 → U_2` canonically has
    `e(B_j) = B_(j+1)`. So `Stab(p') = ⟨Γ_(1), e, g_1, g_2⟩` is finitely generated. `∎`
