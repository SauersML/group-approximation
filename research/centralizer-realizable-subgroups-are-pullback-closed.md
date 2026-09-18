---
rg: 2
id: centralizer-realizable-subgroups-are-pullback-closed
kind: claim
title: Subgroups realizable as centralizers in B_A overgroups are exactly the traces of type (A) point stabilizers, and they are closed under pullback to B_A quotients and under finite-index enlargement
distinct_from:
  pbh-coset-wreaths-iff-identity-edge-hnns: that proves centralizer realization (e) is equivalent to the coset lamplighter and identity-edge HNN conditions (a)-(d), and lists five sufficient cases; this adds a point-stabilizer characterization and three closure operations (pullback, finite-index enlargement, finite-configuration stabilizers) that generate many new cases, including every normal subgroup with a B_A quotient.
  pbh-coset-closure-passes-to-finite-index-overgroups: that changes the AMBIENT group G to a finite-index overgroup; this keeps G fixed and enlarges the SUBGROUP C to a finite-index overgroup C', or pulls C back along a homomorphism.
  pbh-wreath-closure-fails-over-undecidable-stabilizers: that shows Mihailova fiber products over quotients with unsolvable word problem are not realizable; this shows the fiber products over quotients in B_A are realizable, so the Mihailova construction splits exactly along B_A-membership of the quotient.
requires:
  - pbh-coset-wreaths-iff-identity-edge-hnns
---

**ESTABLISHED** by `centralizer-realizable-subgroups-are-pullback-closed-proof` (lane proof,
elementary, not reviewed; no priority claimed).

## Setting

`B_A` is the class of groups embedding in a group with a type (A) action
(`type-a-action-gives-boone-higman-for-subgroups`). For `G ∈ B_A` write `R(G)` for the set of
subgroups `C ≤ G` satisfying the equivalent conditions (a)–(e) of
`pbh-coset-wreaths-iff-identity-edge-hnns`. The model condition is (e): some `L ∈ B_A`
contains `G` and an element `m` with `C_G(m) = C`. Membership in `R(G)` is equivalent to:
- `A ≀_{G/C} G ∈ B_A` for every `A ∈ B_A`;
- `G *_C (C × K) ∈ B_A` for every `K ∈ B_A`, including the identity-edge HNN extension
  `⟨G, t | [t, c] = 1 (c ∈ C)⟩`.

## Statement

Let `G ∈ B_A`.
1. **Point-stabilizer form.** `C ∈ R(G)` iff there are a type (A) actor `E ⊇ G` on a set `S`
   and a point `s ∈ S` with `C = G ∩ Stab_E(s)`. The same holds with "point" replaced by
   "finitely supported colouring `f: S → Z/k`" and `Stab_E(f)`.
2. **Pullback.** If `φ: G → Q` is a homomorphism with `Q ∈ B_A` and `D ∈ R(Q)`, then
   `φ^{-1}(D) ∈ R(G)`.
3. **Finite-index enlargement.** If `C ∈ R(G)` and `C ≤ C' ≤ G` with `[C' : C] < ∞`, then
   `C' ∈ R(G)`.
4. **Finite intersections** (already in `pbh-coset-wreaths-iff-identity-edge-hnns`): `R(G)` is
   closed under finite intersections.

## Consequences

For `G ∈ B_A` (finitely generated where stated):
- **Normal subgroups with `B_A` quotients.** Every `N ⊴ G` with `G/N ∈ B_A` lies in `R(G)`
  (pull back `D = 1`). So `A ≀_{G/N} G ∈ B_A` and `⟨G, t | [t, N] = 1⟩ ∈ B_A`.
- **Everything above the commutator subgroup.** For finitely generated `G`, every subgroup
  `C ⊇ [G, G]` lies in `R(G)`. Pull back along `G → G^ab`. `G^ab` is finitely generated
  abelian, hence in `B_A` (a subgroup of `V`), and every subgroup of it is in `R(G^ab)`
  (virtually abelian case of `pbh-coset-closure-passes-to-finite-index-overgroups`).
  Examples: `⟨F_n, t | [t, [F_n, F_n]] = 1⟩ ∈ B_A`, and the lamplighter over `F_n/[F_n,F_n] = Z^n`
  with `F_n` on top.
- **Relative versions.** If `N ⊴ G`, `G/N ∈ B_A` and `C/N ∈ R(G/N)`, then `C ∈ R(G)`. For
  instance `G/N` virtually abelian and `C ⊇ N` arbitrary; or `G/N` free and `C/N` finitely
  generated (M. Hall).
- **All finite-index subgroups** (pull back along a finite quotient), and every subgroup
  containing a finite-index subgroup of a realized one.
- **Mihailova dichotomy.** For `π: F → Q = F/N` let `P_Q = {(u, v) ∈ F × F : π(u) = π(v)}`.
  - If `Q ∈ B_A` then `P_Q ∈ R(F × F)`: `P_Q = (π × π)^{-1}(Δ_Q)`, and the diagonal `Δ_Q` is a
    retract of `Q × Q` via `(a, b) ↦ (a, a)`.
  - If `Q` has unsolvable word problem then `P_Q ∉ R(F × F)`
    (`pbh-wreath-closure-fails-over-undecidable-stabilizers`).
  - `P_Q ∈ R(F × F)` iff the left-right lamplighter `Z/2 ≀_Q (F × F)`, with `(u, v)·q = π(u) q π(v)^{-1}`,
    lies in `B_A`, because `(F × F)/P_Q ≅ Q` as `F × F`-sets.

## What stays open

Decidable subgroups that are invisible to homomorphisms into `B_A`. The sharpest instances:
- `N ⊴ F_n` the relator subgroup of a finitely presented `Q` with solvable word problem not
  known to be in `B_A` (Higman's group `H4`, Baumslag–Gersten, Deligne-type non-RF groups).
  `N ∈ R(F_n)` iff the "lamplighter shadow" `Z/2 ≀_Q F_n` (`F_n` acting through `Q`) lies in
  `B_A`. This follows from `Q ∈ B_A`; the converse is open.
- `P_Q ≤ F × F` for the same `Q`.

## Lesson for general BH

Centralizer realization, and with it identity-edge HNN permanence and coset-lamplighter
permanence of `B_A`, is functorial. It is pulled back along every homomorphism into `B_A`,
it is stable under finite-index enlargement, and it equals "trace of a type (A) point or
finite-configuration stabilizer". So realization is easy exactly on `B_A`-visible subgroups,
those cut out by finitely many homomorphisms into `B_A` groups and finitely many type (A)
stabilizers. The only obstruction left is decidable subgroups invisible to `B_A`
quotients, and their canonical form is the relator subgroup of a decidable finitely
presented group. There realization is equivalent to `B_A`-membership of the lamplighter
shadow `Z/2 ≀_Q F_n`. This is a formally weaker target than `Q ∈ B_A`, because the shadow
need not contain `Q`. It locates the closure-theoretic crux: HNN permanence of `B_A` over
decidable edges is the lamplighter shadow of PBH itself, matching the reductions
synthesis' verdict that closure theorems alone cannot finish BH.
