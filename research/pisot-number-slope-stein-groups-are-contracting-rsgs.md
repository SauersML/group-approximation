---
rg: 2
id: pisot-number-slope-stein-groups-are-contracting-rsgs
kind: claim
title: For every Pisot number β with property (F), unit or not, V(Z[1/β],<β>) is a full contracting RSG on the β-shift, hence finitely presented, with type (A) on breakpoints; for non-units D(V) is a finite-index fp simple group in every degree and every real quadratic field has such slopes; affine codings carry only one slope
requires:
  - pisot-stein-groups-are-contracting-rsgs
  - pisot-unit-slope-stein-groups-are-finitely-presented
  - stein-v-groups-act-with-type-a-on-breakpoints
  - contracting-rsgs-embed-in-fp-simple-groups
distinct_from:
  pisot-stein-groups-are-contracting-rsgs: that is the unit case, Γ = Z[β]; this removes the unit hypothesis (Γ = Z[1/β], slopes S-units), shows the coding exists only under (F), and adds the rank-one obstruction.
  pisot-unit-slope-stein-groups-are-finitely-presented: that gets a finite-index D(V) only when no two conjugates multiply to 1, which fails for norm +1 quadratic units; for non-units this never fails, so D(V) is finite-index fp simple in every degree, including degree 2 in every real quadratic field.
  negative-base-pisot-stein-groups-are-finitely-presented: that reaches norm +1 units through an orientation-reversing coding, with D(V) of infinite index in degree 2; this uses the ordinary positive coding with non-unit slopes.
  integral-slope-stein-v-groups-are-k-graph-full-groups: that handles several commuting integral slopes through k-graphs; item 5 here shows that no affine coding can make several independent slopes contracting.
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

**ESTABLISHED** through `pisot-number-slope-stein-groups-are-contracting-rsgs-proof` (lane proof, not reviewed;
no priority claimed). It adapts `pisot-stein-groups-are-contracting-rsgs-proof` by one integrality step.

**Sources.**
- **Read at source:** the SRS survey arXiv:1312.0386, which gives:
  - the definition `Fin(β) = Z[1/β] ∩ [0,∞)` of (F) for algebraic integers;
  - "(F) can hold only for Pisot numbers" (Frougny–Solomyak);
  - Hollander's criterion (Thm. `srsbeta`, proof included);
  - `D_1^{(0)} = [0,1)` (Prop. `pro:D10`).
- **Read at source:** Molyneux arXiv:2602.08748, citing Winstone's thesis (not read).
- **Read at source:** Tanner arXiv:2312.07375, Lemma `single lambda computation` (Li, Prop. 5.5), which holds
  for every algebraic λ, and the AH sequence.
- **Cited, not read:** Frougny–Solomyak, ETDS 12 (1992), for (F) when `a_1 ≥ … ≥ a_d ≥ 1`.

## Statement

Let `β > 1` be real. Put `Γ_β = Z[β, 1/β]` and `V_β(ℓ) = V(Γ_β, ⟨β⟩, ℓ)` (Tanner's notation), with `V_β = V_β(1)`.

1. **The coding exists exactly under (F).** `V_β` acts on the β-shift `X_β` by homeomorphisms through the
   value map `π` iff `β` has property (F): `Fin(β) = Z[1/β] ∩ [0,∞)`. Then `β` is a Pisot number and
   `Γ_β = Z[1/β]`.
2. **Contracting and finitely presented.** If `β` has (F), unit or not, then for every `ℓ ∈ Z[1/β]_{>0}`:
   - `V_β(ℓ)` is a full contracting RSG on `X_β` (on a clopen subset for general `ℓ`);
   - it is finitely presented, by BBMZ Theorem A;
   - it acts with type (A) on `Z[1/β] ∩ [0,ℓ)`.

   So every subgroup of it satisfies permutational Boone–Higman.
3. **Non-units.** If moreover `β` is not a unit, then `V_β(ℓ)^ab` is finite in every degree. So
   `D(V_β(ℓ))` is a finite-index finitely presented simple group.
   - In degree 2, with `β² = aβ + b`, the order of `V_β^ab` divides `gcd(a+b−1, 2)·(b+1)`.
4. **Quadratic fields.** A quadratic `β > 1` has (F) iff `β² = aβ + b` with integers `1 ≤ b ≤ a` (this is
   Winstone's tree-pair condition `a ≤ b` in Molyneux's `ax² + bx − 1` notation). It is a non-unit iff
   `b ≥ 2`.
   - Every real quadratic field `Q(√D)` contains such a `β`: `β = ⌊m√D⌋ + m√D`, with `m = 1` unless
     `D = t² + 1`, and `m = 2` then.
   - Examples: `1 + √3` (so `Q(√3)`, where the unit route has infinite-index `D(V)`); `2 + 2√2`; `4 + 2√5`.
5. **Affine codings carry one slope.** Let `(X, π)` be any coding of a Cantorized interval by a shift with
   finitely many cone types whose cone charts are affine with slopes in `β^Z`.
   - Suppose a group `G` of homeomorphisms of `X` contains `h` fixing a point `x_0` and affine of slope `γ`
     on a one-sided neighbourhood of `π(x_0)`, with `γ ∉ β^Q`. Then `G` is not a contracting RSG on `X`.
   - In particular `V_{2,3}` (it contains a slope-2 and a slope-3 germ at `0`) is contracting in no affine
     coding. So is any Stein group with two such germs of multiplicatively independent slopes.

## Lesson for general BH

The unit hypothesis was never the point. A finite nucleus needs the translation parts to be bounded at every
place except the coding place:
- at the archimedean conjugates, by Pisot contraction;
- at the primes dividing `β`, automatically, because depth multiplies by powers of `β`, which contract there.

So contracting affine codings carry exactly "Pisot S-arithmetic": one S-unit slope that is a Pisot number,
translations in `O[1/β]`, and (F). The cases outside this are exactly where the coding fails:
- non-Pisot slopes (Winstone's `a > b` quadratics, Salem numbers, rational bases such as `3/2`);
- several independent slopes (item 5).

The first also lose tree pairs. The second need commuting renormalizations, i.e. k-graphs
(`integral-slope-stein-v-groups-are-k-graph-full-groups`). A single contracting coding therefore carries a
rank-one, finite-S arithmetic, which is again the prime-locality wall for `GL_n(Q)`. Infinitely many
independent scalings must be carried by the host's acting group, not by one coding.
