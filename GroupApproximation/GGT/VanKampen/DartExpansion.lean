import GroupApproximation.GGT.VanKampen.CombMapSubdivisionWalks

/-!
# Composing actual subdivisions of map darts

Every old dart expands to a nonempty face walk. Disjointness is expressed by
preservation of duplicate-free lists, and edge reversal reverses the entire
expanded walk. The composition is the actual concatenation of these walks.
-/

namespace GroupApproximation.GGT.VanKampen

universe u v w

structure DartExpansion (M : CombMap.{u}) (N : CombMap.{v}) where
  darts : M.Dart → List N.Dart
  nonempty : ∀ d, darts d ≠ []
  nodup : ∀ l : List M.Dart, l.Nodup → (l.flatMap darts).Nodup
  chain : ∀ d, (darts d).IsChain (fun x y => N.facePerm x = y)
  join : ∀ d, N.facePerm ((darts d).getLast (nonempty d)) =
    (darts (M.facePerm d)).head (nonempty _)
  reverse : ∀ d, darts (M.alpha d) = (darts d).reverse.map N.alpha

namespace DartExpansion

variable {M : CombMap.{u}} {N : CombMap.{v}} {P : CombMap.{w}}

def refl (M : CombMap.{u}) : DartExpansion M M where
  darts d := [d]
  nonempty _ := List.cons_ne_nil _ _
  nodup l hl := by simpa only [List.flatMap_singleton'] using hl
  chain _ := List.IsChain.singleton _
  join _ := rfl
  reverse _ := rfl

def trans (E : DartExpansion M N) (F : DartExpansion N P) : DartExpansion M P where
  darts d := (E.darts d).flatMap F.darts
  nonempty d := CyclicListExpansion.nonempty F.darts F.nonempty _ (E.nonempty d)
  nodup l hl := by
    have h := F.nodup (l.flatMap E.darts) (E.nodup l hl)
    simpa only [List.flatMap_assoc] using h
  chain d := CyclicListExpansion.chain F.darts F.nonempty N.facePerm P.facePerm
    F.chain F.join (E.darts d) (E.chain d)
  join d := by
    rw [CyclicListExpansion.getLast F.darts F.nonempty _ (E.nonempty d),
      CyclicListExpansion.head F.darts F.nonempty _ (E.nonempty (M.facePerm d)),
      F.join, E.join]
  reverse d := by
    rw [E.reverse, List.flatMap_map, List.reverse_flatMap, List.map_flatMap]
    simp only [F.reverse]
    rfl

end DartExpansion
end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.DartExpansion.trans
