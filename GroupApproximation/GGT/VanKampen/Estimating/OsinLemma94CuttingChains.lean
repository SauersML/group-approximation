import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonRealization
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryRotation
import GroupApproximation.Meta.AxiomGuard

/-!
# The cutting chains of Lemma 9.4 are quasi-geodesic

Osin (math/0411039v3, §9), Lemma 9.4, Case 2: "This contradicts our assumption that `∑ l(t_i)`
is minimal."  Take an optimal family with the fewest darts
(`GloballyDistinguishedSectionFamily.DartMinimal`).  A cutting chain of an unselected `G`-face
has the face on both sides, and the walk across it runs back along it.  Every such chain is
`(λ, c + 2)`-quasi-geodesic.  `osinLemma94CuttingChainsInput_of_pieces` derives
`OsinLemma94CuttingChainsInput` from three Props.

* `PendantPathRemovalInput`.  If the walk runs from a dart straight back along its reverse, the
  reverse dart ends at a vertex of valence one, and removing that edge takes away two darts
  (`not_leaf_of_dartMinimal`).  So no dart of a chain has its reverse in the chain
  (`alpha_not_mem_of_dartMinimal`): the innermost such pair would be a leaf.
* `QuasiGeodesicRespellInput`: a legal word that is not `(λ, c + 2)`-quasi-geodesic has a subword
  with a strictly shorter nonempty legal spelling.
* `ChainRespellInput`: respelling that subword gives fewer darts and the same unbound sum.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded

namespace GloballyDistinguishedSectionFamily

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- Consecutive entries of a chain are related. -/
theorem chain_rel_getElem {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α}, l.IsChain R → ∀ (j : ℕ) (hj : j + 1 < l.length), R l[j] l[j + 1]
  | [], _, _, hj => by rw [List.length_nil] at hj; omega
  | [_], _, _, hj => by rw [List.length_singleton] at hj; omega
  | _ :: _ :: _, h, 0, _ => (List.isChain_cons_cons.mp h).1
  | _ :: b :: l, h, j + 1, hj =>
    chain_rel_getElem (l := b :: l) (List.isChain_cons_cons.mp h).2 j
      (by simp only [List.length_cons] at hj ⊢; omega)

/-- Consecutive darts of a chain read off a rotated face walk follow the face permutation. -/
theorem facePerm_getElem_of_rotate_eq
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {f : S.diagram.toCombMap.Face} {r : ℕ} {chain rest : List S.diagram.toCombMap.Dart}
    (hwalk : (S.diagram.faceBoundary f).darts.rotate r = chain ++ rest) (j : ℕ)
    (hj : j + 1 < chain.length) : S.diagram.toCombMap.facePerm chain[j] = chain[j + 1] := by
  have hrot := isChain_rotate_of_isChain_closes (S.diagram.faceBoundary f).nonempty
    (S.diagram.faceBoundary f).chain (S.diagram.faceBoundary f).closes r
  rw [hwalk] at hrot
  exact chain_rel_getElem hrot.left_of_append j hj

/-- **No leaf inside a `G`-face.**  If the walk of an unselected `G`-face runs from a dart `d`
straight back along `alpha d`, then `alpha d` ends at a vertex of valence one.  Removing that edge
keeps the unbound sum and takes away two darts, against `DartMinimal`. -/
theorem not_leaf_of_dartMinimal (hpendant : PendantPathRemovalInput.{u, w, v})
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts} (hS : S.DartMinimal)
    {f : S.diagram.toCombMap.Face} (hf : S.UnselectedGFace f) {d : S.diagram.toCombMap.Dart}
    (hd : S.diagram.toCombMap.faceOf d = f)
    (hleaf : S.diagram.toCombMap.facePerm d = S.diagram.toCombMap.alpha d) : False := by
  have hsigma : S.diagram.toCombMap.sigma (S.diagram.toCombMap.alpha d) =
      S.diagram.toCombMap.alpha d := hleaf
  have hfree : ∀ e ∈ [S.diagram.toCombMap.alpha d],
      S.diagram.toCombMap.alpha e ∉ [S.diagram.toCombMap.alpha d] := by
    intro e he
    rw [List.mem_singleton] at he
    subst he
    rw [S.diagram.toCombMap.alpha_involutive d, List.mem_singleton]
    exact fun h => S.diagram.toCombMap.alpha_fixedPointFree d h.symm
  have hfaces : ∀ e ∈ [S.diagram.toCombMap.alpha d], S.diagram.toCombMap.faceOf e = f ∧
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha e) = f := by
    intro e he
    rw [List.mem_singleton] at he
    subst he
    refine ⟨?_, by rw [S.diagram.toCombMap.alpha_involutive d]; exact hd⟩
    rw [← hleaf, S.diagram.toCombMap.faceOf_facePerm]
    exact hd
  have hhead : ∀ e ∈ [S.diagram.toCombMap.alpha d].head?, S.diagram.toCombMap.sigma e = e := by
    intro e he
    simp at he
    subst he
    exact hsigma
  have hjoints : S.DegreeTwoJoints [S.diagram.toCombMap.alpha d] := by
    intro j e e' _ he'
    simp at he'
  obtain ⟨T, hTsum, hTdarts⟩ := hpendant S f [S.diagram.toCombMap.alpha d] hf
    (List.cons_ne_nil _ _) (by simp) hfree hfaces hhead hjoints
  have hle := hS T hTsum
  rw [List.length_singleton] at hTdarts
  omega

/-- **A cutting chain has no dart together with its reverse.**  If `alpha chain[p] = chain[q]`
with `p < q`, the walk across gives `alpha chain[p + 1] = chain[q - 1]`, and the innermost pair
is a leaf (`not_leaf_of_dartMinimal`). -/
theorem alpha_not_mem_of_dartMinimal (hpendant : PendantPathRemovalInput.{u, w, v})
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts} (hS : S.DartMinimal)
    {f : S.diagram.toCombMap.Face} (hf : S.UnselectedGFace f) {r : ℕ}
    {chain rest : List S.diagram.toCombMap.Dart}
    (hwalk : (S.diagram.faceBoundary f).darts.rotate r = chain ++ rest)
    (hjoints : S.RunsBackAcross chain) :
    ∀ d ∈ chain, S.diagram.toCombMap.alpha d ∉ chain := by
  have hface : ∀ (p : ℕ) (hp : p < chain.length), S.diagram.toCombMap.faceOf chain[p] = f := by
    intro p hp
    have hmem : chain[p] ∈ (S.diagram.faceBoundary f).darts.rotate r := by
      rw [hwalk]
      exact List.mem_append_left _ (List.getElem_mem hp)
    exact ((S.diagram.faceBoundary f).mem_iff _).mp (List.mem_rotate.mp hmem)
  have key : ∀ (k p q : ℕ) (hp : p < chain.length) (hq : q < chain.length), q = p + k →
      S.diagram.toCombMap.alpha chain[p] ≠ chain[q] := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro p q hp hq hpq h
      rcases k with _ | _ | k
      · obtain rfl : q = p := by omega
        exact S.diagram.toCombMap.alpha_fixedPointFree _ h
      · obtain rfl : q = p + 1 := by omega
        exact not_leaf_of_dartMinimal hpendant hS hf (hface p hp)
          ((facePerm_getElem_of_rotate_eq hwalk p hq).trans h.symm)
      · obtain rfl : q = p + k + 1 + 1 := by omega
        have hback := hjoints (p + k + 1) _ _ (List.getElem?_eq_getElem (by omega))
          (List.getElem?_eq_getElem hq)
        rw [← h, S.diagram.toCombMap.alpha_involutive chain[p],
          facePerm_getElem_of_rotate_eq hwalk p (by omega)] at hback
        refine ih k (by omega) (p + 1) (p + k + 1) (by omega) (by omega) (by omega) ?_
        rw [hback, S.diagram.toCombMap.alpha_involutive chain[p + k + 1]]
  intro d hd hmem
  obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hd
  obtain ⟨q, hq, hpq⟩ := List.mem_iff_getElem.mp hmem
  rcases Nat.lt_or_ge q p with hlt | hle
  · refine key (p - q) q p hq hp (by omega) ?_
    rw [hpq, S.diagram.toCombMap.alpha_involutive chain[p]]
  · exact key (q - p) p q hp hq (by omega) hpq.symm

end GloballyDistinguishedSectionFamily

/-- **The cutting chains are quasi-geodesic.**  "This contradicts our assumption that `∑ l(t_i)`
is minimal."  A subword of a cutting chain with a strictly shorter legal spelling starts a
rotation of the face walk, and respelling it gives fewer darts. -/
theorem osinLemma94CuttingChainsInput_of_pieces (hrespell : ChainRespellInput.{u, w, v})
    (hpendant : PendantPathRemovalInput.{u, w, v})
    (hword : QuasiGeodesicRespellInput.{u, w}) :
    OsinLemma94CuttingChainsInput.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts S hlambda hc hS f r chain rest hf hwalk hacross
    hjoints
  by_contra hnot
  have hadm : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D)
      (dartWord S.diagram chain) := by
    intro a ha
    simp only [dartWord, List.mem_map] at ha
    obtain ⟨d, -, rfl⟩ := ha
    exact S.label_admissible d
  obtain ⟨i, n, hin, word, hne, hlen, hwordadm, hval⟩ := hword D lambda c hlambda hc _ hadm hnot
  have hin' : i + n ≤ chain.length := by simpa [dartWord] using hin
  have hsub : ((chain.drop i).take n).length = n := by
    rw [List.length_take, List.length_drop, Nat.min_eq_left (show n ≤ chain.length - i by omega)]
  have hmem : ∀ d ∈ (chain.drop i).take n, d ∈ chain := fun d hd =>
    List.mem_of_mem_drop (List.mem_of_mem_take hd)
  have hwalk' : (S.diagram.faceBoundary f).darts.rotate (r + i) =
      (chain.drop i).take n ++ ((chain.drop i).drop n ++ rest ++ chain.take i) := by
    have hi : i ≤ chain.length := by omega
    have hi' : i ≤ (chain ++ rest).length := by
      rw [List.length_append]
      omega
    rw [← List.rotate_rotate, hwalk, List.rotate_eq_drop_append_take hi',
      List.drop_append_of_le_length hi, List.take_append_of_le_length hi,
      ← List.append_assoc (List.take n _), List.take_append_drop, List.append_assoc]
  have hjoints' : S.RunsBackAcross ((chain.drop i).take n) := by
    intro j e e' he he'
    obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.mp he'
    rw [List.getElem?_take_of_lt (show j < n by omega), List.getElem?_drop] at he
    rw [List.getElem?_take_of_lt (show j + 1 < n by omega), List.getElem?_drop,
      ← Nat.add_assoc] at he'
    exact hjoints (i + j) e e' he he'
  obtain ⟨T, hTsum, hTlt⟩ := hrespell S f (r + i) ((chain.drop i).take n) _ word hf hwalk'
    (fun d hd => hacross d (hmem d hd))
    (fun d hd hd' => GloballyDistinguishedSectionFamily.alpha_not_mem_of_dartMinimal hpendant
      hS hf hwalk hjoints d (hmem d hd) (hmem _ hd'))
    hjoints' hne hwordadm
    (by rw [hval]; simp only [dartWord, List.map_take, List.map_drop]) (by omega)
  have hle := hS T hTsum
  omega

#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.chain_rel_getElem
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.facePerm_getElem_of_rotate_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.not_leaf_of_dartMinimal
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.alpha_not_mem_of_dartMinimal
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CuttingChainsInput_of_pieces

end GroupApproximation.GGT.VanKampen
