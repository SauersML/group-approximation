---
rg: 2
id: subshift-automorphisms-are-outer-over-icc-scaffolds
kind: claim
title: Over a scaffold with trivial FC-centre acting topologically freely, no nontrivial automorphism of the system lies in its topological full group or is implemented by a unit of its crossed-product algebra, so inputs realized by cellular automata never enter fixed-scaffold hosts
distinct_from:
  minimal-system-automorphisms-fix-every-proximal-factor: that constrains which groups can act by automorphisms on a rigid system; this shows that even when they can, automorphisms stay outside the full group and the unit group of the fixed-scaffold host.
---

**ESTABLISHED** (lane bh-invent-16, 2026-09-18; lane proof, elementary, not reviewed).

## Setting

`P` is a countable group whose FC-centre (elements with finite conjugacy class) is trivial. Examples are
non-abelian free groups, products of them, torsion-free non-elementary hyperbolic groups, and infinite finitely generated
simple groups. `P` acts on a compact totally disconnected metric space `X`, topologically freely (points
with trivial stabilizer are dense). `[[P ⋉ X]]` is the topological full group. For a nonzero commutative
ring `k`, `A = LC(X, k) ⋊ P` is the algebraic crossed product, a free left `LC(X, k)`-module on
`{δ_p}` with `δ_p f δ_p^-1 = f ∘ p^-1`. Each `φ ∈ Aut(X, P)` induces the algebra automorphism
`α_φ(f δ_p) = (f ∘ φ^-1) δ_p`.

## Statement

1. **Automorphisms are not in the full group.** `[[P ⋉ X]] ∩ Aut(X, P) = {id}`.
2. **Automorphisms are not inner.** If `u ∈ A^×` satisfies `u f u^-1 = f ∘ φ^-1` for all `f ∈ LC(X, k)`,
   for a homeomorphism `φ` of `X`, then `φ ∈ [[P ⋉ X]]`. In particular, for `φ ∈ Aut(X, P)` the
   automorphism `α_φ` is inner only if `φ = id`. Being inner on `LC(X, k)` alone is already impossible.
3. **Normalizing, not containing.** Every `φ ∈ Aut(X, P)` normalizes `[[P ⋉ X]]`. A group `Γ ≤ Aut(X, P)`
   therefore gives `[[P ⋉ X]] ⋊ Γ` inside `Homeo(X)`. Making `Γ` inner means passing to the joint action
   of `P × Γ`, whose full group and crossed product contain `Γ`. That joint system is a time lift of
   `X` by `Γ` (`deterministic-time-lifts-inherit-quantum-rigidity`).

## Proof

1. Let `τ ∈ [[P ⋉ X]]` commute with `P`, with a continuous (so finitely valued) cocycle `c: X → P` and
   `τ(x) = c(x) x`.
   - From `τ(px) = p τ(x)` we get `p^-1 c(px) p · x = c(x) · x`. At a point `x` with trivial stabilizer
     this gives `c(px) = p c(x) p^-1`.
   - Both sides are locally constant in `x` and agree on a dense set, so they agree everywhere.
   - Hence the finite set `c(X)` is invariant under conjugation by `P`. Each of its elements then has a
     finite conjugacy class, so `c ≡ 1` and `τ = id`.
2. Write `u = Σ_{p ∈ F} a_p δ_p` with `F` finite and `a_p ∈ LC(X, k)`.
   - Then `u f = Σ a_p (f ∘ p^-1) δ_p` and `(f ∘ φ^-1) u = Σ (f ∘ φ^-1) a_p δ_p`. Comparing coefficients
     gives `a_p · (f ∘ p^-1 − f ∘ φ^-1) = 0` for all `f` and `p`.
   - Locally constant functions separate points, so `φ^-1(x) = p^-1 x` on the clopen set `U_p = supp a_p`.
   - The sets `U_p` cover `X`. Take `v = Σ b_q δ_q` with `u v = 1`. The `δ_1`-coefficient of `u v` is
     `Σ_p a_p · (b_{p^-1} ∘ p^-1) = 1`, and it vanishes at any point outside every `U_p`.
   - So `φ^-1` is given locally by elements of `P` on a clopen cover. Refining the cover to a partition
     gives a continuous cocycle, so `φ^-1`, and hence `φ`, lies in `[[P ⋉ X]]`.
   - For `φ ∈ Aut(X, P)`, conclude by 1.
3. `φ τ φ^-1` has cocycle `c ∘ φ^-1`, because `φ` commutes with `P`. The rest is by definition. ∎

## What it changes

This is the gate-U reading of the commutant route. Track B embeds the input in a fixed host built over a
fixed Farrell–Jones scaffold `P`: the full group or unit group of `LC(X) ⋊ P` over a programmable SFT
`X`. Realizing the input by cellular automata of `X` escapes the geometric cap of gate U, since
automorphisms act on symbols, not positions. For instance `Aut(A^Z)` contains `F_2`, although `F_2` has
no coarse embedding in `Z`.

The escape has a price. Items 1 and 2 show that such a realization never lands in the host. Item 3 shows
that internalizing it adds the input to the acting group, which is Track A in time-lift form. That form
is then blocked for Kazhdan simple inputs over every rigid row SFT on main, by
`minimal-system-automorphisms-fix-every-proximal-factor`. So cellular-automaton realizations neither
replace gate U nor open a third track.

## Lesson for general BH

Automorphisms are outer. Over an ICC scaffold, the commutant of a system meets its full group and its
unit group only in the identity. Any construction that realizes the input by cellular automata, reversible
automata or shift automorphisms has therefore only moved the input into the acting group. There the
carrier principle and (★′) apply unchanged. A fixed-scaffold host must contain the input through elements
that move positions: full-group elements, units or Leavitt isometries. Gate U is exactly that requirement.
