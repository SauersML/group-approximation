---
rg: 2
id: va-singular-point-germ-groups-are-t-bar-proof
kind: route
title: Extend a periodic germ by a V-map, then conjugate by the dyadic PL map sending +1 to x2
target: va-singular-point-germ-groups-are-t-bar
requires: []
---

Throughout, "locally in `V`" means locally a prefix replacement `βψ ↦ γψ`.

**Reduction to `p = 0̄`.** For `p = α0̄` the prefix replacement `α0ψ ↦ 0ψ` is a `V`-germ
sending `p` to `0̄` and conjugating `L_p` to `L_{0̄}`. Conjugation by a `V`-germ preserves
each condition in item 1. The case `α1̄` is the mirror image (swap the letters 0 and 1).
So take `p = 0̄` and write `L = L_{0̄}`, the germ of `0ψ ↦ ψ`.

**Item 1, ⊆.** Let `f ∈ VA` with `f(0̄) = 0̄`.
- If `0̄ ∉ sing(f)`, the germ is a `V`-germ fixing `0̄`. Such a germ has the form
  `0^aψ ↦ 0^bψ` near `0̄`, i.e. it is `L^(a−b)`. That is order-preserving, commutes with
  `L`, and is locally in `V`.
- If `0̄ ∈ sing(f)`, condition (2) says that near `0̄` the map `f` is order-preserving and
  `L∘f = f∘L`. Since `sing(f)` is finite, `f` is locally in `V` at every point of a small
  cone around `0̄` other than `0̄` itself.

**Item 1, ⊇.** Let `φ: N → φ(N)` be as in item 1, with `N = 0^kC` small enough that
`φ(N) ≠ C`.
- `C∖N` and `C∖φ(N)` are nonempty clopen sets, hence finite disjoint unions of cones.
  After subdividing cones, there is a prefix-replacement homeomorphism
  `g: C∖N → C∖φ(N)`.
- `f = φ ⊔ g` is a homeomorphism of `C` with `sing(f) ⊆ {0̄}`, and it satisfies (2) at
  `0̄`.
- So `f ∈ VA`, and its germ at `0̄` is that of `φ`.

**Item 2.** The first bullet of item 1 shows that the `V`-germs fixing `0̄` are the
powers of `L`. `L` has infinite order. Item 1 makes `L` commute with every element of
`G_{0̄}`.

**Item 3.** Use the binary-value map `C → [0,1]`. Prefix replacements between cones are
the affine maps `x ↦ 2^n x + d` (`n ∈ Z`, `d` dyadic) between dyadic intervals.
Order-preserving locally-`V` homeomorphisms of cone neighbourhoods of `0̄` correspond to
increasing PL homeomorphisms of `(0, ε)` with pieces of this form and dyadic breakpoints,
discrete in `(0, ε)`. The Cantor set splits each dyadic point in two, so a dyadic
breakpoint lifts. `L` corresponds to `x ↦ 2x`. So `G_{0̄}` is the group of germs at `0+`
of such maps `φ` with `φ(2x) = 2φ(x)`.
- By this equivariance each such germ extends uniquely to a homeomorphism of `(0, ∞)`
  commuting with `×2`.
- Put `h: R → (0,∞)`, affine on each `[n, n+1]` onto `[2^n, 2^(n+1)]`:
  `h(y) = 2^n (y − n + 1)`. It is PL with pieces `2^n y + d`, `d` dyadic, and breakpoints
  at the integers, and `h(y+1) = 2h(y)`.
- Conjugation by `h` identifies the group of maps above with the group of increasing
  PL homeomorphisms of `R` with pieces `2^n y + d`, dyadic breakpoints, finitely many on
  each compact set, commuting with `z(y) = y + 1`. That is `T̄` in the definition quoted
  in `research/artifacts/gq-gq-lit-q-embeddings.md` §1.1.
- `L ↦ ×2 ↦ z`, and `T̄ / ⟨z⟩ = T`.

**Consequence paragraph.** Proposition 13 of arXiv:2005.02036v4 applies through the
isomorphism of item 3. The normalizer statement is Lemma C of
`research/artifacts/gq-gq-q-in-germs-anatomy.md`: if `D ≅ (Q,+)` and `D ∩ Z(W) ≠ 1`, then
every `w ∈ N_W(D)` induces multiplication by some `λ ∈ Q^x` fixing a nonzero element of
`D`, so `λ = 1`.
