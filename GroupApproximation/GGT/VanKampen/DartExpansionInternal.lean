import GroupApproximation.GGT.VanKampen.DartExpansionVertices

/-!
# Fresh and simple internal vertices of a subdivided edge

The forward and reverse expanded walks are disjoint. At an internal vertex,
the vertex rotation swaps exactly the incoming reverse dart and the outgoing
dart. Internal vertices are distinct and avoid every retained old vertex.
-/

namespace GroupApproximation.GGT.VanKampen.DartExpansion

open Equiv
universe u v
variable {M : CombMap.{u}} {N : CombMap.{v}} (E : DartExpansion M N)

theorem block_nodup (a : M.Dart) : (E.darts a).Nodup := by
  simpa only [List.flatMap_singleton] using E.nodup [a] (List.nodup_singleton a)

theorem block_eq_of_mem {a b : M.Dart} {x : N.Dart}
    (ha : x ∈ E.darts a) (hb : x ∈ E.darts b) : a = b := by
  classical
  by_contra hne
  have hnd : (E.darts a ++ E.darts b).Nodup := by
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using
      E.nodup [a, b] (by simp [hne])
  exact (List.nodup_append.mp hnd).2.2 x ha x hb rfl

theorem alpha_mem (a : M.Dart) {x : N.Dart} (hx : x ∈ E.darts a) :
    N.alpha x ∈ E.darts (M.alpha a) := by
  rw [E.reverse]
  exact List.mem_map.mpr ⟨x, List.mem_reverse.mpr hx, rfl⟩

theorem alpha_not_mem (a : M.Dart) {x : N.Dart} (hx : x ∈ E.darts a) :
    N.alpha x ∉ E.darts a := by
  intro h
  exact M.alpha_fixedPointFree a (E.block_eq_of_mem (E.alpha_mem a hx) h)

theorem eq_first_of_vertex (x : N.Dart) (v : M.Vertex)
    (h : N.vertexOf x = E.vertexMap v) : ∃ d : M.Dart, x = E.first d := by
  revert h
  refine Quotient.inductionOn' v ?_
  intro d h
  change N.vertexOf x = N.vertexOf (E.first d) at h
  obtain ⟨n, hn⟩ := ((N.vertexOf_eq_iff _ _).mp h.symm).exists_nat_pow_eq
  exact ⟨(M.sigma ^ n) d, hn.symm.trans (E.first_sigma_pow n d)⟩

theorem internal_ne_first (a d : M.Dart) (i : Fin (E.darts a).length) (hi : 0 < i.val) :
    (E.darts a).get i ≠ E.first d := by
  intro h
  have hdmem : E.first d ∈ E.darts d := List.head_mem (E.nonempty d)
  have had : a = d := E.block_eq_of_mem (List.get_mem _ _)
    (h.symm ▸ hdmem)
  subst d
  have hzero : (E.darts a).get ⟨0, List.length_pos_iff.mpr (E.nonempty a)⟩ = E.first a := by
    simp only [first, List.get_eq_getElem, List.head_eq_getElem]
  have heq := (E.block_nodup a).get_inj_iff.mp (h.trans hzero.symm)
  have hidx : i.val = 0 := congrArg Fin.val heq
  omega

/-- An internal vertex cannot be an old vertex, including either endpoint. -/
theorem internal_fresh (a : M.Dart) (i : Fin (E.darts a).length) (hi : 0 < i.val) :
    N.vertexOf ((E.darts a).get i) ∉ Set.range E.vertexMap := by
  rintro ⟨v, hv⟩
  obtain ⟨d, hd⟩ := E.eq_first_of_vertex _ v hv.symm
  exact E.internal_ne_first a d i hi hd

theorem reverse_chain (a : M.Dart) :
    (E.darts a).IsChain (fun x y => N.sigma y = N.alpha x) := by
  have h := E.chain (M.alpha a)
  rw [E.reverse, List.isChain_map, List.isChain_reverse] at h
  apply h.imp
  intro x y hxy
  change N.sigma (N.alpha (N.alpha y)) = N.alpha x at hxy
  simpa only [N.alpha_involutive y] using hxy

theorem internal_rotation (a : M.Dart) (i : Fin (E.darts a).length) (hi : 0 < i.val) :
    N.sigma ((E.darts a).get i) = N.alpha ((E.darts a)[i.val - 1]) ∧
    N.sigma (N.alpha ((E.darts a)[i.val - 1])) = (E.darts a).get i := by
  have hlt : i.val - 1 + 1 < (E.darts a).length := by omega
  have hnext : i.val - 1 + 1 = i.val := by omega
  have hforward := (List.isChain_iff_getElem.mp (E.chain a)) (i.val - 1) hlt
  have hreverse := (List.isChain_iff_getElem.mp (E.reverse_chain a)) (i.val - 1) hlt
  constructor
  · simpa only [hnext, List.get_eq_getElem] using hreverse
  · simpa only [CombMap.facePerm, Perm.mul_apply, hnext, List.get_eq_getElem] using hforward

/-- The whole fibre of an internal vertex consists of its two path darts. -/
theorem internal_vertex_fibre (a : M.Dart) (i : Fin (E.darts a).length) (hi : 0 < i.val)
    (x : N.Dart) : N.vertexOf x = N.vertexOf ((E.darts a).get i) ↔
      x = (E.darts a).get i ∨ x = N.alpha ((E.darts a)[i.val - 1]) := by
  obtain ⟨hnext, hprev⟩ := E.internal_rotation a i hi
  constructor
  · intro h
    obtain ⟨n, hn⟩ := ((N.vertexOf_eq_iff _ _).mp h.symm).exists_nat_pow_eq
    have hpow : ∀ k : ℕ, (N.sigma ^ k) ((E.darts a).get i) = (E.darts a).get i ∨
        (N.sigma ^ k) ((E.darts a).get i) = N.alpha ((E.darts a)[i.val - 1]) := by
      intro k
      induction k with
      | zero => exact Or.inl rfl
      | succ k ih =>
          rw [pow_succ', Perm.mul_apply]
          rcases ih with h | h
          · exact Or.inr ((congrArg N.sigma h).trans hnext)
          · exact Or.inl ((congrArg N.sigma h).trans hprev)
    simpa only [hn] using hpow n
  · rintro (rfl | rfl)
    · rfl
    · exact (congrArg N.vertexOf hnext).symm.trans (N.vertexOf_sigma _)

theorem internal_vertex_eq_iff (a : M.Dart) (i j : Fin (E.darts a).length)
    (_hi : 0 < i.val) (hj : 0 < j.val) :
    N.vertexOf ((E.darts a).get i) = N.vertexOf ((E.darts a).get j) ↔ i = j := by
  constructor
  · intro h
    rcases (E.internal_vertex_fibre a j hj _).mp h with h | h
    · exact (E.block_nodup a).get_inj_iff.mp h
    · exact (E.alpha_not_mem a (List.getElem_mem (by omega))
        (h ▸ List.get_mem (E.darts a) i)).elim
  · rintro rfl
    rfl

theorem edge_eq_iff (a : M.Dart) (i j : Fin (E.darts a).length) :
    N.edgeOf ((E.darts a).get i) = N.edgeOf ((E.darts a).get j) ↔ i = j := by
  constructor
  · intro h
    rcases (N.edgeOf_eq_iff _ _).mp h with h | h
    · exact (E.block_nodup a).get_inj_iff.mp h
    · exact (E.alpha_not_mem a (List.get_mem _ _) (h.symm ▸ List.get_mem _ _)).elim
  · rintro rfl
    rfl

end GroupApproximation.GGT.VanKampen.DartExpansion

#audit_axioms GroupApproximation.GGT.VanKampen.DartExpansion.internal_fresh
#audit_axioms GroupApproximation.GGT.VanKampen.DartExpansion.internal_vertex_fibre
#audit_axioms GroupApproximation.GGT.VanKampen.DartExpansion.internal_vertex_eq_iff
#audit_axioms GroupApproximation.GGT.VanKampen.DartExpansion.edge_eq_iff
