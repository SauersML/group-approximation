---
rg: 2
id: vertex-supported-symplectic-completion-proof
kind: route
title: Kill one radical dimension per private neighbour, then split off the block
target: vertex-supported-symplectic-completion
requires: [minimal-marked-graph-private-neighbour]
artifacts:
  - research/artifacts/kun-thom-private-neighbour-2026-08-18.md
---

## Direct proof

**Item 1.**  Let `V = V_{F''}` be the current finite window with
`Rad(V) ≠ 0`, pick `0 ≠ ξ ∈ Rad(V)`, and let `z` be a private neighbour of
`supp(ξ)` from the prerequisite, so `b(δ_z, ξ) = 1`.  Then `δ_z ∉ V`, since
`ξ` pairs trivially with all of `V`.  Put `V' = V + F_2δ_z` and
`φ = b(δ_z, ·)|_V`.  If `x + αδ_z ∈ Rad(V')` then pairing against `V` gives
`b(x, v) + αφ(v) = 0` for all `v ∈ V`.  With `α = 1` this puts `φ` in the
image of `V → V^*`, `x ↦ b(x,·)|_V`; that image is the annihilator of
`Rad(V)` (its kernel is `Rad(V)`, so the dimensions match), while
`φ(ξ) = 1`.  Hence `α = 0` and

```text
Rad(V') = Rad(V) ∩ ker φ,
```

of dimension exactly `dim Rad(V) − 1` because `φ` is nonzero on `Rad(V)`.
Iterating `dim Rad(b|_{V_F})` times gives `F'`, and
`dim Rad(b|_{V_F}) ≤ dim V_F = |F|`.

**Item 2.**  Enumerate `X = {x₁,x₂,…}` and let `F_n` be the completion of
`F_{n−1} ∪ {x_n}`; then `x_n ∈ F_n`, so `⋃F_n = X`.  A nondegenerate
alternating form over `F_2` has even rank, so `|F_n|` is even and the twisted
group algebra of `(V_{F_n}, b)` at `z ↦ −1` is the full matrix algebra
`M_{2^{|F_n|/2}}(ℂ)` — the standard Clifford/Weyl representation of a
nondegenerate binary symplectic space.  Nondegeneracy of `V_{F_n}` inside
`V_{F_{n+1}}` gives `V_{F_{n+1}} = V_{F_n} ⊕ V_{F_n}^⊥`, and elements of the
two summands commute, so the inclusion of twisted group algebras is the
inclusion of a tensor factor.  An increasing union of full matrix algebras
along unital tensor-factor inclusions is `2^∞`-UHF, and the GNS closure at
the canonical trace is the hyperfinite `II₁` factor.

**Item 3.**  Complete `F` to `F'` by Item 1, take the Clifford representation
of `(V_{F'}, b)` on `D = 2^{|F'|/2} ≤ 2^{|F|}` dimensions, and restrict the
generators to `F`.  The commutation signs are exact because the
representation is a genuine representation of the twisted group, and the
normalized matrix trace of a nontrivial Weyl word vanishes because in a full
matrix algebra the twisted group basis is orthonormal for the normalized
Hilbert--Schmidt inner product with `tr(1) = 1`.

## Scope

Nothing here transports any element of `G`.  The finite blocks are chosen by
a greedy procedure that is blind to the action, and Item 2's exhaustion is
not `G`-equivariant at any stage.
