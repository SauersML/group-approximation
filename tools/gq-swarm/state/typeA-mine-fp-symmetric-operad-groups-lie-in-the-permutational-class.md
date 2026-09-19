---
rg: 2
id: fp-symmetric-operad-groups-lie-in-the-permutational-class
kind: claim
title: Every symmetric operad group acts on its boundary through a full Cantor group, so a finitely presented one with clopen-transitive leaves is a type (A) actor, and finitely presented simple symmetric operad groups with clopen-transitive leaves satisfy permutational Boone--Higman
requires:
  - fp-clopen-transitive-full-cantor-groups-have-type-a-actions
  - permutational-boone-higman-iff-full-cantor-hosts
distinct_from:
  ore-operad-groups-have-type-a-clopen-actions: that treats finite-type dissection operads with finite transformation groups on a given space and avoids fullness; this treats abstract symmetric operads with transformations, with any number of elementary classes and any transformation groups, and proves the boundary image is full for its own germs, so the existing full-group criterion applies directly.
  fp-clopen-transitive-full-cantor-groups-have-type-a-actions: that is the criterion for a group already known to be full; this proves that every symmetric operad group's boundary image is full and identifies clopen transitivity with a color-monoid condition.
  permutational-boone-higman-iff-full-cantor-hosts: that is the equivalence for full Cantor hosts; this places every symmetric operad host inside it and adds the kernel analysis, so the operadic route and the permutational route certify the same inputs.
  oligomorphic-operads-have-f-infinity-groups: that is the open finiteness conjecture for operads with infinitely many elementary classes; this shows what finiteness can buy, namely membership in B_A and nothing beyond it.
  finite-type-operad-groups-split-over-a-label-kernel: that locates the part of the transformations that never reaches the dynamics in finite-type operads; this shows that a simple operad group has no such part at all, since it acts faithfully on its boundary.
---

**ESTABLISHED** by `symmetric-operad-groups-full-cantor-proof` (lane bh-typeA-universal,
2026-09-18; lane proof, not independently reviewed). No priority claimed. For the classical
examples (Higman--Thompson groups, Brin--Thompson groups, Hughes' local similarity groups,
Röver--Nekrashevych groups) fullness is well known. What is recorded here is the uniform
statement for Thumann's operads with transformations, with no finite-type hypothesis, and what
it implies for Boone--Higman.

## Setting

- `𝒪` is a **symmetric** operad with transformations in Thumann's sense (arXiv:1409.1085), as in
  `thumann-operad-groups-need-only-f-infinity-transformations`. It has finitely many colors,
  countably many operations, and satisfies the cancellative calculus of fractions.
- **No finite type is assumed.** The elementary classes may be infinite, and the transformation
  groups `Aut_ℐ(c)` may be arbitrary.
- **(N)** No operation has arity `0`, and every color is the output of some operation of arity
  at least `2`.
- Fix an object `X` (a finite tuple of colors) and let `Γ = π_1(𝒪, X)`.

**The boundary.**
- An *expansion* is a morphism `b : x → X` of Thumann's category of operations. Its *leaves* are
  the entries of `x`.
- The boundary `∂X` is the inverse limit of the leaf sets over refinements `b ∘ ψ → b`.
- Each leaf `i` of `b` gives a *cylinder* `∂_b(i)`.
- An element `a ∘ b^{-1}` of `Γ` (with `a, b : x → X`) maps `∂_b(i)` onto `∂_a(i)`, and likewise
  at every finer level.
- Write `Γ̄ ≤ Homeo(∂X)` for the image and `N` for the kernel (the *boundary kernel*).

**The color monoid** `M(𝒪)` is the free commutative monoid on the colors modulo
`c = (input colors of θ)` for every operation `θ` with output `c`.

## Statement

1. **Cantor.** `∂X` is a Cantor space. Cylinders form a basis, and every clopen set is a union
   of cylinders of a single expansion.
2. **Full.** `Γ̄` is full: every homeomorphism of `∂X` that agrees locally with elements of `Γ̄`
   lies in `Γ̄`.
3. **Types.** A nonempty clopen `U` has a well-defined class `[U] ∈ M(𝒪)`, namely the color
   multiset of any expansion whose cylinders partition `U`.
   - Local maps preserve classes.
   - If all nonzero elements of `M(𝒪)` are equal, then any two nonempty clopens are joined by a
     `Γ̄`-local map: `Γ̄` is **clopen transitive**.
   - With one color, this holds iff the arities `k` of the operations have `gcd(k − 1) = 1`, for
     example when there is a binary operation.
4. **Type (A).** If `Γ̄` is clopen transitive and finitely presented, then its action on the
   proper nonempty clopen subsets of `∂X` is of type (A).
   - Stabilizers are `Γ̄ × Γ̄`, and there are at most 16 orbits of ordered pairs
     (`fp-clopen-transitive-full-cantor-groups-have-type-a-actions`).
   - Hence every subgroup of `Γ̄` lies in `B_A`, has solvable word problem, and embeds in a
     finitely presented simple group.
5. **Kernel.**
   - `Γ̄ ≠ 1`, so `N ≠ Γ`. If `Γ` is simple, then `N = 1` and `Γ = Γ̄`.
   - In general, a subgroup `G ≤ Γ` with `G ∩ N = 1` embeds in `Γ̄`.

## Corollaries

- **(a) Simple operadic hosts are permutational hosts.**
  - Suppose `Γ` is finitely presented, `N = 1`, and `M(𝒪)` has one nonzero element. Then `Γ`
    and all its subgroups lie in `B_A`.
  - In particular, every finitely presented simple symmetric operad group with clopen-transitive
    leaves satisfies PBH, and so do its subgroups. So are the finitely presented simple subgroups
    of such a `Γ`: `Γ` itself is the actor.
  - This is the operadic case of BFFHZ Question 3.4
    (`bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh`): no host of this form separates BH from
    PBH.
- **(b) Per-input equivalence.** A group `G` lies in `B_A` iff it embeds in a finitely presented
  symmetric operad group whose boundary action is faithful and clopen transitive.
  - `⇐` is (a).
  - `⇒`: for a type (A) actor `Γ_0 ⊇ G` on `S`, the twisted Brin--Thompson group `SV_{Γ_0}` is
    the operad group of the `Γ_0`-twisted cube operad. It has one color, binary splits `θ_s`
    (`s ∈ S`) and transformations `g θ_s = θ_{gs}(g, g)`.
  - Its boundary action on `C^S` is faithful, it is finitely presented
    (`twisted-brin-thompson-finite-presentation-criterion`), and it contains `Γ_0`.
- **(c) What the oligomorphic operad conjecture can give.**
  - Any input certified by a finitely presented, boundary-faithful host of
    `oligomorphic-operads-have-f-infinity-groups` already lies in `B_A`.
  - So the conjecture is a *finiteness criterion for full Cantor groups presented by a move
    system*, not a route beyond PBH.
  - Its constructive value is in producing actors from carriers that are not actors themselves.
    There are two channels:
    - through the transformations, where
      `bounded-refinement-operads-reduce-to-their-carriers` shows this needs unbounded refinement;
    - through the dynamics, where the host is the carrier's full group
      (`symmetric-ore-operads-containing-their-carrier-are-full-groups`).

**Planar and braided operads.**
- A planar operad group acts on `∂X` inside the boundary image of its symmetrization (adjoin all
  permutations), which is full by 2. So its subgroups lie in `B_A` whenever the symmetrized group
  is finitely presented, boundary-faithful and clopen transitive.
- A braided operad group with a symmetric quotient maps onto the symmetric operad group, with the
  pure-braid labels in the kernel. So a simple braided operad group is isomorphic to its
  symmetric image, which is covered by (a).

## Lesson for general BH

**Every move language is a full group in disguise.** Any symmetric host built by composing local
moves with transformations on the leaves is a full Cantor group once it is simple (or
boundary-faithful), whatever the moves are; planar hosts sit inside one. This holds for:
- cube splits, dissections, self-similar restrictions;
- infinitely many oligomorphically permuted moves;
- arbitrary transformation groups.

A finitely presented clopen-transitive full group is its own type (A) actor. So the operadic,
Thompson-like and groupoid-full-group routes all certify exactly `B_A`, and between them they
never touch BFFHZ Question 3.4.

Two consequences follow:
- **Separating BH from PBH.** It would take a finitely presented simple group with *no*
  boundary-faithful full-group model: a lattice-type or Kac--Moody-type simple group, not a
  Thompson-like one.
- **Proving PBH.** The whole content of the actor problem is finite presentation of a full
  clopen-transitive host containing the input. The move system is only a tool for proving that
  finiteness.
