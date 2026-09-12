import GroupApproximation.GGT.DGOLemma421MinimalityFourGon

/-!
# Connections in the DGO minimality quadrilateral

The source and opposite-side vertices have a common left translation.
Cancelling it gives connections in the original paths, with their actual
basepoints. These identities let the isolation theorem exclude the source
side and the two connectors during the minimal-gap argument.
-/

namespace GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- A segment read from the identity is the translated original path,
independently of that path's chosen basepoint. -/
theorem vertex_segment_one_at (word : List (RelLetter G Lambda)) (v : G)
    (k m i : ℕ) (hi : i ≤ m) :
    vertex (1 : G) ((word.drop k).take m) i =
      (vertex v word k)⁻¹ * vertex v word (k + i) := by
  have hshift := vertex_smul (vertex v word k) (1 : G) ((word.drop k).take m) i
  rw [mul_one] at hshift
  have hsegment := vertex_segment word v k m i hi
  rw [hshift] at hsegment
  rw [← hsegment]
  group

namespace DGO421MinimalityFourGonData

variable {D : RelGenSet G Lambda} {vp vq : G} {P Q : List (RelLetter G Lambda)}
  {lam mu : Lambda} {ip1 ip2 iq1 iq2 : ℕ}
  (F : DGO421MinimalityFourGonData D vp vq P Q lam mu ip1 ip2 iq1 iq2)

def cycleWord : List (RelLetter G Lambda) :=
  F.near ++ (P.drop ip1).take (ip2 - ip1) ++ F.far ++
    revWord ((Q.drop iq1).take (iq2 - iq1))

def sourceIndex (i : ℕ) : ℕ := F.near.length + i

def targetIndex (j : ℕ) : ℕ :=
  F.near.length + ((P.drop ip1).take (ip2 - ip1)).length + F.far.length +
    (((Q.drop iq1).take (iq2 - iq1)).length - j)

/-- Coordinates on the source side retain the source basepoint. -/
theorem source_vertex {i : ℕ} (hi : i ≤ ((P.drop ip1).take (ip2 - ip1)).length) :
    vertex (1 : G) F.cycleWord (F.sourceIndex i) =
      (vertex vq Q iq1)⁻¹ * vertex vp P (ip1 + i) := by
  have him : i ≤ ip2 - ip1 := hi.trans (List.length_take_le _ _)
  change vertex (1 : G)
    (F.near ++ (P.drop ip1).take (ip2 - ip1) ++ F.far ++
      revWord ((Q.drop iq1).take (iq2 - iq1))) (F.near.length + i) = _
  rw [vertex_fourGon_side _ _ _ _ (1 : G) hi,
    vertex_segment_one_at P vp ip1 (ip2 - ip1) i him, F.near_value]
  group

/-- The reversed opposite side returns to the target path's coordinates. -/
theorem target_vertex {j : ℕ} (hj : j ≤ iq2 - iq1) :
    vertex (1 : G) F.cycleWord (F.targetIndex j) =
      (vertex vq Q iq1)⁻¹ * vertex vq Q (iq1 + j) := by
  change vertex (1 : G)
    (F.near ++ (P.drop ip1).take (ip2 - ip1) ++ F.far ++
      revWord ((Q.drop iq1).take (iq2 - iq1)))
    (F.near.length + ((P.drop ip1).take (ip2 - ip1)).length + F.far.length +
      (((Q.drop iq1).take (iq2 - iq1)).length - j)) = _
  rw [vertex_fourGon_opposite_closed _ _ _ _ F.closes j]
  exact vertex_segment_one_at Q vq iq1 (iq2 - iq1) j hj

/-- Source-side connections are precisely connections in the original path. -/
theorem source_connection_iff {nu : Lambda} {i j : ℕ}
    (hi : i ≤ ((P.drop ip1).take (ip2 - ip1)).length)
    (hj : j ≤ ((P.drop ip1).take (ip2 - ip1)).length) :
    Connected D.fam nu (1 : G) F.cycleWord (F.sourceIndex i) (F.sourceIndex j) ↔
      Connected D.fam nu vp P (ip1 + i) (ip1 + j) := by
  unfold Connected
  rw [F.source_vertex hi, F.source_vertex hj]
  group

/-- Cross-side connections retain both original basepoints. -/
theorem cross_connection_iff {nu : Lambda} {i j : ℕ}
    (hi : i ≤ ((P.drop ip1).take (ip2 - ip1)).length) (hj : j ≤ iq2 - iq1) :
    Connected D.fam nu (1 : G) F.cycleWord (F.sourceIndex i) (F.targetIndex j) ↔
      (vertex vp P (ip1 + i))⁻¹ * vertex vq Q (iq1 + j) ∈ D.fam nu := by
  unfold Connected
  rw [F.source_vertex hi, F.target_vertex hj]
  group

/-- A connection to the near connector returns to the near source point. -/
theorem connected_source_of_near {i : ℕ}
    (hi : i ≤ ((P.drop ip1).take (ip2 - ip1)).length)
    (hmatch : (vertex vp P ip1)⁻¹ * vertex vq Q iq1 ∈ D.fam lam)
    (hconn : Connected D.fam lam (1 : G) F.cycleWord (F.sourceIndex i) 0) :
    Connected D.fam lam vp P ip1 (ip1 + i) := by
  have hc : (vertex vp P (ip1 + i))⁻¹ * vertex vq Q iq1 ∈ D.fam lam := by
    change (vertex (1 : G) F.cycleWord (F.sourceIndex i))⁻¹ *
      vertex (1 : G) F.cycleWord 0 ∈ D.fam lam at hconn
    rw [F.source_vertex hi, vertex_zero] at hconn
    convert hconn using 1
    group
  have hm := (D.fam lam).mul_mem hmatch ((D.fam lam).inv_mem hc)
  change (vertex vp P ip1)⁻¹ * vertex vp P (ip1 + i) ∈ D.fam lam
  convert hm using 1
  group

/-- The start of the far connector is the far endpoint of the source side. -/
theorem connected_source_of_far {nu : Lambda} {i : ℕ}
    (hip : ip1 ≤ ip2) (hip2 : ip2 ≤ P.length)
    (hi : i ≤ ((P.drop ip1).take (ip2 - ip1)).length)
    (hconn : Connected D.fam nu (1 : G) F.cycleWord (F.sourceIndex i)
      (F.near.length + ((P.drop ip1).take (ip2 - ip1)).length)) :
    Connected D.fam nu vp P (ip1 + i) ip2 := by
  have hlen : ((P.drop ip1).take (ip2 - ip1)).length = ip2 - ip1 :=
    length_segment P ip1 (ip2 - ip1) (by omega)
  have hc := (F.source_connection_iff hi (le_refl _)).mp hconn
  rwa [hlen, Nat.add_sub_of_le hip] at hc

end DGO421MinimalityFourGonData
end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.DGO421MinimalityFourGonData.source_connection_iff
#audit_axioms GroupApproximation.GGT.OsinComponents.DGO421MinimalityFourGonData.cross_connection_iff
#audit_axioms GroupApproximation.GGT.OsinComponents.DGO421MinimalityFourGonData.connected_source_of_near
#audit_axioms GroupApproximation.GGT.OsinComponents.DGO421MinimalityFourGonData.connected_source_of_far
