---
rg: 2
id: thompson-t-co-amenable-subgroups-meet-copies-of-f
kind: claim
title: "A co-amenable subgroup meets some conjugate of every nonamenable subgroup nonamenably; in Thompson's T, a co-amenable H whose point stabilizers are amenable would make F amenable, and no subgroup of PSL(2,Z) is co-amenable"
distinct_from:
  thompson-t-orbits-carry-no-invariant-means: that shows point stabilizers such as F are not co-amenable in T; this constrains every co-amenable subgroup through its intersections with copies of F, and reduces the tame case to amenability of F
  thompson-t-co-amenable-subgroup-kills-real-euler-class: that asks for a co-amenable H with vanishing real Euler class; this proves necessary conditions on any co-amenable H, whatever its Euler class
  jones-subgroup-coamenable-iff-thompson-f-amenable: that is a co-amenability criterion inside F; this is about co-amenable subgroups of T and uses F only as a test subgroup
---

**ESTABLISHED.**

**(A) General lemma.** Let `G` be a group, `H ≤ G` co-amenable (a `G`-invariant mean on
`ℓ^∞(G/H)`), and `K ≤ G`. If `K ∩ gHg^{-1}` is amenable for every `g ∈ G`, then `K` is amenable.
Equivalently: a co-amenable subgroup meets some conjugate of every nonamenable subgroup in a
nonamenable subgroup.

For Thompson's group `T` acting on `S^1 = R/Z`, let `H ≤ T` be co-amenable.

**(B1) Arc-supported pieces.** If `F` is not amenable, then `H` contains a nonamenable subgroup
that fixes some nonempty open arc of `S^1` pointwise.

**(B2) Reduction to amenability of F.** If every subgroup of `H` fixing a dyadic point of `S^1`
is amenable, then `F` is amenable. By Brin–Squier, this hypothesis holds whenever every subgroup of
`H` without non-abelian free subgroups is amenable. Examples, by standard theorems not imported
here: `H` linear in characteristic zero (Tits alternative), `H` virtually free, `H` hyperbolic.

So an explicit co-amenable subgroup of `T` from any of these tame classes would prove that `F` is
amenable.

**(B3) No subgroup of PSL(2,Z) is co-amenable.** Let `Λ = φ PSL(2,Z) φ^{-1} ≤ T` be the
Thurston–Imbert copy. No subgroup of `Λ`, and no subgroup of a `T`-conjugate of `Λ`, is
co-amenable in `T`. This holds unconditionally.
- The test subgroup is the double-cover lift `Λ̃ ≤ C_T(r_{1/2})` of `Λ`.
- `Λ̃` meets every `T`-conjugate of `Λ` in an amenable group, because lifts of hyperbolic
  elements have 4 or 0 fixed points and infinite order.

## Role

The node `thompson-t-co-amenable-subgroup-kills-real-euler-class` is the discrete branch of
`lifted-thompson-t-is-a-t-menable`. This claim adds two forced shapes to its witnesses.
- *(D-F), from (B2).* A witness `H` with amenable dyadic-point stabilizers would prove that `F`
  is amenable. If `F` is nonamenable (the majority view), then by (B1) a witness must contain
  nonamenable subgroups of copies of `F` supported on arcs.
- *(D-Λ), from (B3).* This independently refutes the concrete test candidate `H = PSL(2,Z)`.

Proof: `thompson-t-co-amenable-subgroups-meet-copies-of-f-proof`.
