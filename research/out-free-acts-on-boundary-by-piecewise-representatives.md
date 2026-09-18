---
rg: 2
id: out-free-acts-on-boundary-by-piecewise-representatives
kind: claim
title: For every n at least three, some finite-index subgroup of Out(F_n) acts on ∂F_n by homeomorphisms that are piecewise boundary maps of representatives of the acting class
distinct_from:
  out-free-groups-virtually-embed-in-aut-free-groups: that asks for a faithful action of a finite-index subgroup on some free group; this asks only for a compatible action on the boundary Cantor set of F_n itself, with finitely many representative pieces per element, and it is implied by a virtual section.
  out-free-extension-pushed-into-the-boundary-full-group: that proves the splitting criterion and the constraints; this is the open existence statement.
---

**OPEN** (stated by bh-outfn-2, 2026-09-18).

**Claim (PR).** Let `n ≥ 3`. There are a finite-index `Γ ≤ Out(F_n)` and a homomorphism
`q ↦ h_q`, `Γ → Homeo(∂F_n)`, such that for each `q` there are a finite clopen partition
`∂F_n = ⊔ U_i` and representatives `Φ_i ∈ q` with `h_q = Φ̂_i` on `U_i`.

Equivalently, the finitely presented extension `1 → [[F_n ⋉ ∂F_n]] → H → Out(F_n) → 1` of
`out-free-extension-pushed-into-the-boundary-full-group` splits over `Γ`.

**Why it matters.** It is the one Out-specific input of route
`out-fn-bh-via-piecewise-representative-boundary-host`. Given (PR) and a finiteness
statement, Out(F_n) satisfies Boone–Higman.

## What is known

1. **Weaker than a virtual section.** A virtual section of `Aut(F_n) → Out(F_n)` is (PR)
   with one piece. That premise is open, and the class-two computation of
   `fox-rational-section-fails-class-two-virtually` bears on it. That computation passes
   through `F_n/γ_3` and does not apply to (PR).
2. **No commuting-pair obstruction.** Abelian subgroups satisfy (PR) virtually.
3. **Necessary behaviour in rank `2g ≥ 4`.** Every (PR) action moves the periodic point
   `w^∞` of the surface word `w` with infinite orbit under the stabilizer of `[w]`. This is
   the Euler class of the capping extension (item 6 of the parent).
4. **Rank two.** It holds, since `Out(F_2) = GL_2(Z)` is virtually free.

## Reformulation for attacks

(PR) is a locally constant cocycle `r: Γ × ∂F_n → Aut(F_n)` with:
- `r(q, ξ) ∈ q`;
- `r(qq', ξ) = r(q, h_{q'}ξ)·r(q', ξ)`, where `h_q(ξ) = r(q,ξ)^(ξ)`.

In words, a Γ-equivariant, locally constant choice of basepoint data for the band
`F_n → Aut(F_n) → Out(F_n)` over the boundary.

**Suggested attacks.**
- **(i) Induce from a subgroup that already lifts.** Look for such a subgroup with finite
  covolume data. Abelian subgroups lift, and so does `Aut(F_{n−1})`, as the stabilizer of a
  free factor with a fixed complement. The constraint of item 3 says the induced action must
  scale at cusps.
- **(ii) Glued lifts of generators.** Choose, for each generator of a finite presentation
  of `Γ`, a gluing of representatives over a clopen partition, and ask that the relators
  evaluate to the identity. Each relator is then a finite word problem in `H`. The piece
  structure is the only freedom beyond a virtual section.
- **(iii) Refutation.** A negative answer would need an invariant of `Γ`-actions by
  piecewise representatives that detects the band. Item 3 is the only such constraint known,
  and it does not contradict (PR).
