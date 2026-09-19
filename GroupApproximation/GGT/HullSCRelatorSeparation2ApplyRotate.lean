import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyComp
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyPair
import GroupApproximation.GGT.OsinTheorem54SepCommIndex

/-!
# A prefix of a rotation, before the wrap

The quadrilateral's long sides are prefixes of rotations of the relator, and the
block-count estimate is about the relator itself.  Below the wrap the two are
the same path up to a left translation, and that is this module:

  `vertex 1 (w.rotate c) x = (listVal (w.take c))⁻¹ * vertex 1 w (c + x)`

for `x` at most `|w| - c`.  Since `wordDist` is left-invariant, every metric
statement about the relator's own vertices transports across the rotation
unchanged on that range --- in particular quasi-geodesicity.

Past the wrap it does not.  The continuation is translated by `listVal w`, which
for the relator is `t⁻¹u` and not `1`: the relator is not a closed word, and two
indices on opposite sides of the seam are `d(v_{c+x}, listVal w · v_{y})` apart,
which no clause about the relator's own vertices controls.  That is the whole
difference from the quadrilateral, whose `listVal` IS `1`.

So the standing block-count hypothesis is taken CYCLICALLY --- quasi-geodesicity
of every prefix of every rotation --- which is how Olshanskii uses it.  This
lemma is what makes the non-wrapping half of that hypothesis free; the wrapping
half is exactly what the cyclic form supplies and the linear form does not.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A vertex of a rotation, below the wrap, is a vertex of the word.**

The rotation is `drop c ++ take c`; a prefix not reaching `|w| - c` stays inside
the `drop`, and reading `w` itself past `c` is reading that same `drop` from the
endpoint of the `take`.  The two differ by the left translation the `take`
spells. -/
theorem vertex_rotate_prefix (v : List (RelLetter G Λ)) {c x : ℕ}
    (hc : c ≤ v.length) (hx : x ≤ v.length - c) :
    vertex (1 : G) (v.rotate c) x
      = (RelLetter.listVal (v.take c))⁻¹ * vertex (1 : G) v (c + x) := by
  have hdlen : (v.drop c).length = v.length - c := by simp
  have htlen : (v.take c).length = c := by
    rw [List.length_take]
    omega
  have h1 : vertex (1 : G) (v.rotate c) x = vertex (1 : G) (v.drop c) x := by
    rw [List.rotate_eq_drop_append_take hc]
    exact vertex_append_of_le (v.drop c) (v.take c) 1 x (by omega)
  have h2 : vertex (1 : G) v (c + x)
      = RelLetter.listVal (v.take c) * vertex (1 : G) (v.drop c) x := by
    have hstep : vertex (1 : G) (v.take c ++ v.drop c) ((v.take c).length + x)
        = vertex ((1 : G) * RelLetter.listVal (v.take c)) (v.drop c) x :=
      vertex_append_add (v.take c) (v.drop c) 1 x
    rw [List.take_append_drop, htlen, one_mul,
      vertex_eq_mul_vertex_one (v.drop c) (RelLetter.listVal (v.take c)) x]
      at hstep
    exact hstep
  rw [h1, h2, inv_mul_cancel_left]

/-! ## A component start in the reversed block -/

/-- **A component start of the quadrilateral in the reversed block names a
component letter of `s`.**

`GGT.OsinComponents.exists_other_component_of_deep_six` returns its cross-side
match as a component START of the quadrilateral, at
`|p| + |q| + |r| + (|s| - j)`; the reversed block is traversed backwards, so
that position is the letter of `s` at `j - 1`, inverted.  Formal inversion does
not change which component a letter belongs to, so the letter of `s` there
carries the index --- and over the alternating relator a letter carrying an
index is a block letter, which is what turns the match into an `IsComp` for the
polygon to consume.

The conclusion is in `getElem?` form on purpose: moving an index inside a
`getElem` would leave the manufactured bound proof behind, and the caller reads
letters by `getElem?` throughout. -/
theorem exists_comp_of_isCompStart_rev (p q r s : List (RelLetter G Bool))
    (lam : Bool) {j : ℕ} (hj0 : 0 < j) (hj : j ≤ s.length)
    (hstart : IsCompStart lam (p ++ q ++ r ++ revWord s)
      (p.length + q.length + r.length + (s.length - j))) :
    ∃ x : G, s[j - 1]? = some (RelLetter.comp lam x) := by
  obtain ⟨k, hcomp⟩ := hstart
  have hmlen : s.length - j < (revWord s).length := by
    rw [length_revWord]
    omega
  have hn : p.length + q.length + r.length + (s.length - j)
      < (p ++ q ++ r ++ revWord s).length := by
    rw [length_fourGon]
    omega
  have hidxlt : s.length - 1 - (s.length - j) < s.length := by omega
  have hc := hcomp.2.2.1 _ le_rfl hcomp.1 hn
  rw [getElem_fourGon_revs p q r s hmlen rfl hn,
    getElem_revWord s hmlen hidxlt, isCompOf_invLetter] at hc
  obtain ⟨x, hx⟩ := HullSC.getElem?_comp_of_isCompOf hidxlt hc
  refine ⟨x, ?_⟩
  rw [show j - 1 = s.length - 1 - (s.length - j) from by omega]
  exact hx

end OsinComponents
end GGT
end GroupApproximation
