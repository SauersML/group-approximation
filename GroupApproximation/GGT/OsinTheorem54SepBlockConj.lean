import GroupApproximation.GGT.OsinTheorem54SepFourGon

/-!
# Two end-to-start elements conjugate one block span to the other

The shape a consumer asked for: `x * v_q * x' = v_s`, with `v_q` and `v_s` the
spans of two matched components and `x`, `x'` short.  This module supplies the
identity; the shortness of `x` and `x'` is the innermost end-to-start bound and
comes from elsewhere.

## Why there are two of them, one per orientation

Traversing the quadrilateral `p ++ q ++ r ++ revWord s` runs `q` FORWARD and `s`
BACKWARD.  So in boundary order the `s`-component is entered at its far end `l`
and left at its near end `j`, and there are two end-to-start gaps rather than
one:

* `x' = (listVal p * vertex 1 q k)⁻¹ * vertex 1 s l` --- from the END of the
  `q`-component to the boundary-order START of the `s`-component;
* `x  = (vertex 1 s j)⁻¹ * (listVal p * vertex 1 q i)` --- the same for the
  reversed traversal.

`block_span_conj` is the resulting identity, and the point of it is what it does
NOT do: the deep span `v_q` stays between the two gaps and is never folded into
either.  A statement folding it in would be false, since `v_q` is unbounded
while `x` and `x'` are not --- that is exactly the start-to-start failure
recorded on `exists_named_connector_of_deep`.

The short side `listVal p` cancels, appearing once in `x` and once inverted in
`x'`.

## What supplies each factor

Both `x` and `x'` are end-to-start elements at an innermost pair, so each is
bounded by one application of the innermost cut bound --- one per orientation.
Nothing here asserts that bound; `block_span_conj` is an identity between the
elements however large they are.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The two end-to-start gaps conjugate the `q`-block span to the `s`-block
span**, leaving the span itself untouched between them.

`v_q = (vertex 1 q i)⁻¹ * vertex 1 q k` and `v_s = (vertex 1 s j)⁻¹ *
vertex 1 s l` are the two component spans; the factors on either side are the
two boundary-order gaps.  Pure algebra: the short side cancels and the middle
telescopes. -/
theorem block_span_conj (p q s : List (RelLetter G Λ)) (i k j l : ℕ) :
    ((vertex (1 : G) s j)⁻¹ * (RelLetter.listVal p * vertex (1 : G) q i))
        * ((vertex (1 : G) q i)⁻¹ * vertex (1 : G) q k)
        * ((RelLetter.listVal p * vertex (1 : G) q k)⁻¹ * vertex (1 : G) s l)
      = (vertex (1 : G) s j)⁻¹ * vertex (1 : G) s l := by
  group

/-- **The same, packaged as the consumer's existential.**

Given the two gaps, the block spans are conjugate by them.  A consumer that has
bounded both gaps reads off `x * v_q * x' = v_s` with `x`, `x'` bounded. -/
theorem exists_block_span_conj (p q s : List (RelLetter G Λ)) (i k j l : ℕ) :
    ∃ x x' : G,
      x = (vertex (1 : G) s j)⁻¹ * (RelLetter.listVal p * vertex (1 : G) q i) ∧
      x' = (RelLetter.listVal p * vertex (1 : G) q k)⁻¹ * vertex (1 : G) s l ∧
      x * ((vertex (1 : G) q i)⁻¹ * vertex (1 : G) q k) * x'
        = (vertex (1 : G) s j)⁻¹ * vertex (1 : G) s l :=
  ⟨_, _, rfl, rfl, block_span_conj p q s i k j l⟩

end OsinComponents
end GGT
end GroupApproximation
