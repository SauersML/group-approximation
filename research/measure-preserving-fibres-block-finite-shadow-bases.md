---
rg: 2
id: measure-preserving-fibres-block-finite-shadow-bases
kind: claim
title: A group action on B x X by a cocycle into measure-preserving homeomorphisms of the fibre admits no finite shadow basis when the fibre measure is atomless with full support; so ABHT folds and Busemann transplants of minimal free fibres are never Thumann-operad instances, and base compression never certifies the fibre
distinct_from:
  one-scale-filling-decides-fp-of-v-times-subshift-hosts: that notes that over an amenable acting group an invariant measure excludes finite shadow bases; this excludes them over non-amenable acting groups too, whenever the action is a skew product over a measure-preserving fibre, using only the fibre measure.
  v-stabilized-horofunction-hosts-need-upstream-certification: that shows ball-pattern tiles of horofunctions fail upstream certification; this shows that for skew products no tile family whatever can refine the fibre, even though the base (a tree boundary) certifies perfectly.
  fold-transfer-theorem-for-fibres-with-a-determining-half-plane: that transfers freeness, minimality and rigidity along folds; this shows the finite-shadow-basis route to finite presentation does not transfer.
---

**ESTABLISHED** (lane proof by bh-g2-abh, 2026-09-18; elementary; not reviewed; no priority claimed).

## Statement

**Setting.**
- `B` and `X` are compact, zero-dimensional metrizable spaces.
- A group `Λ` acts on `B × X` by `λ·(b, x) = (λb, α(λ, b) x)`, where `α` is a continuous cocycle with
  values in `Homeo(X)`.
- `μ` is a probability measure on `X` with:
  - no atoms;
  - full support;
  - invariance under every `α(λ, b)`.

**Theorem.** No finite family of clopen sets `Y_1, …, Y_r ⊆ B × X` has `Λ`-translates forming a basis of the
topology of `B × X`. In particular `Λ ↷ B × X` has no finite shadow basis in the sense of
`one-scale-filling-decides-fp-of-v-times-subshift-hosts`, Part 2.

This holds for every compact `B`, however compressive the base action is.

## Proof

1. **The fibre profile.** For clopen `Y`, put `f_Y(b) = μ(Y_b)`, where `Y_b = {x : (b, x) ∈ Y}`.
   - `Y` is a finite union of clopen rectangles, so `f_Y` is locally constant.
   - Hence `f_Y` takes finitely many values.
2. **Transport.** `(λY)_(λb) = α(λ, b)(Y_b)`, and `α(λ, b)` preserves `μ`. So `f_(λY)(λb) = f_Y(b)`.
   - Hence every translate of `Y_j` has profile values in the finite set `V_j = f_(Y_j)(B)`.
   - Let `v_0 > 0` be the least positive element of `⋃_j V_j`. If there is none, every `Y_j` has
     null fibres; then by full support every `Y_j` is empty, and there is nothing to prove.
3. **Small neighbourhoods.** Fix `(b, x)`. Since `μ` has no atoms, `x` has a clopen neighbourhood `C` with
   `μ(C) < v_0`. Put `U = B × C`.
4. **Contradiction.** Suppose `(b, x) ∈ λY_j ⊆ U`.
   - The fibre `(λY_j)_b` is clopen and contains `x`. By full support, `f_(λY_j)(b) > 0`, so it is at
     least `v_0`.
   - But `(λY_j)_b ⊆ C`, so `f_(λY_j)(b) <= μ(C) < v_0`.
   - So no translate of a tile fits between `(b, x)` and `U`. ∎

## Instances

1. **ABHT folds.** Let `X` be a minimal, infinite `Z^2` SFT and `Z ≅ X̂ × ∂T` its fold over
   `Λ = F_n × Z`.
   - By the cocycle of `fold-transfer-theorem-for-fibres-with-a-determining-half-plane`, `Λ` acts by
     `α(w t^m, ξ) = σ^((m, h_ξ(w)))`, which is a `Z^2`-shift.
   - Take any `Z^2`-invariant probability measure on `X̂`. It exists by amenability, has full support by
     minimality, and is atomless because there are no finite orbits.
   - So `Λ ↷ Z` has no finite shadow basis. The tree direction certifies its own coordinate with one
     edge (`v-stabilized-horofunction-hosts-need-upstream-certification`, item 2), but the fibre
     coordinate is never refined by translates.
2. **Busemann transplants.** `busemann-transplants-give-free-sfts-on-building-lattices` realizes the
   transplant as a Busemann skew product over the skeleton, with `L ≅ Z^r` acting on the fibre `Y` by
   shifts. With `Y` minimal and infinite, there is again no finite shadow basis, over any building
   lattice.
3. **Any amenable fibre cocycle.** The same holds for every skew product whose cocycle takes values in an
   amenable group of homeomorphisms of a minimal, infinite fibre with no finite orbits. The group then has an
   invariant measure, which is atomless and has full support.

## Lesson for general BH

**Base compression never certifies an amenable fibre.** In a skew product the fibre-measure profile
`b ↦ μ(Y_b)` of a tile is carried along unchanged by the group, so finitely many tiles can never refine the
fibre. The non-amenable base can supply finite shadow bases only for its own coordinate.

For the rigidity-transfer constructions of Track A (folds, Busemann transplants, lifts), this has two
consequences:
- quantum rigidity transfers (the fold theorem, `a2-busemann-transplants-preserve-quantum-rigidity`);
- finite presentation (E3′) does **not** come for free. It has to be proved in the fibre direction, as the
  nonlinear one-scale filling that `one-scale-filling-decides-fp-of-v-times-subshift-hosts` (Part 5)
  isolates for amenable hosts.

The amenable difficulty of P2′ survives any skew-product transport.
