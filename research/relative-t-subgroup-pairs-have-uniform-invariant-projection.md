---
rg: 2
id: relative-t-subgroup-pairs-have-uniform-invariant-projection
kind: claim
title: "For a countable group and any subgroup, not necessarily normal, relative property (T) gives a uniform bound: almost invariant unit vectors lie close to their projection onto the invariant vectors"
distinct_from:
  wobbling-normal-relative-t-subgroups-are-locally-finite: Step 1 of its proof route proves the same bound only for normal H, by the equivariant projection trick; this covers every subgroup, through the Jolissaint-Cornulier uniform characterization
---

**ESTABLISHED** by `relative-t-uniform-projection-from-cornulier-citation`.

## Statement

Let `Γ` be a countable discrete group and `H ≤ Γ` any subgroup. Suppose `(Γ, H)` has relative
property (T): every unitary representation of `Γ` with almost invariant vectors has a nonzero
`H`-invariant vector.

For a unitary representation `(π, V)` write `P` for the orthogonal projection onto `V^H`. Then for
every `δ > 0` there are a finite `Q ⊂ Γ` and `ε > 0` such that, for every unitary representation
`π` and every unit vector `ξ` with `max_{g ∈ Q} ‖π(g)ξ − ξ‖ ≤ ε`:

- `sup_{h ∈ H} ‖π(h)ξ − ξ‖ < δ`, and
- `‖ξ − Pξ‖ < δ`.

The first bullet also holds, with the same proof, for any subset `X ⊂ Γ` in place of `H`, provided
`(Γ, X)` has relative (T) in Cornulier's sense, meaning every conditionally negative definite
function on `Γ` is bounded on `X`.

## Role

This removes the only use of normality in `wobbling-normal-relative-t-locally-finite-proof`. The
consequence is `wobbling-relative-t-subgroups-are-locally-finite`.
