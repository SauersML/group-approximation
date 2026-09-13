import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.GGT.VanKampen.VertexJoinMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Boundary walks through the collar moves

The strip of the collar surgery (`GeodesicCollar.StripStatement`) is grown one dart at a time: an
edge is doubled (`FaceEdgeDoubling`), and the new digon is pinched into the strip
(`PinchSplit`).  The boundary walk of the face set must stay a simple closed walk through both
moves.

* `sameCycle_of_sameCycle_mul_swap`, `sameCycle_mul_swap_iff_of_not_sameCycle`: composing a
  permutation with the transposition of two points of one cycle refines the cycles, and changes
  nothing away from that cycle.
* `isSimpleClosedWalk_map`: a simple closed walk transports along an embedding of darts that
  commutes with `alpha` and keeps the vertices.
* `edgeInsertion_vertexOf_embed_iff`, `edgeInsertion_sigma_some_none`: inserting an edge keeps the
  vertices of the old darts, and the vertex rotation runs from `some none` to the first corner.
* `isSimpleClosedWalk_pinch`: a pinch at the vertex where the walk enters along the reverse of `x`
  and leaves along `sigma y` keeps the walk simple and closed.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GeodesicCollar

open Equiv

universe u

section Perm

variable {D : Type u} [DecidableEq D] [Finite D]

/-- **Splitting a cycle refines the cycles.**  When `x` and `y` lie on one cycle of `p`, every
cycle of `p * swap x y` lies inside a cycle of `p`. -/
theorem sameCycle_of_sameCycle_mul_swap {p : Perm D} {x y : D} (hxy : p.SameCycle x y)
    {a b : D} (h : (p * Equiv.swap x y).SameCycle a b) : p.SameCycle a b := by
  have hstep : ∀ w, p.SameCycle w ((p * Equiv.swap x y) w) := by
    intro w
    rw [Perm.mul_apply]
    by_cases hwx : w = x
    · rw [hwx, Equiv.swap_apply_left]
      exact hxy.trans Perm.SameCycle.rfl.apply_right
    · by_cases hwy : w = y
      · rw [hwy, Equiv.swap_apply_right]
        exact hxy.symm.trans Perm.SameCycle.rfl.apply_right
      · rw [Equiv.swap_apply_of_ne_of_ne hwx hwy]
        exact Perm.SameCycle.rfl.apply_right
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [← hn]
  clear hn h
  induction n with
  | zero => exact Perm.SameCycle.rfl
  | succ n ih =>
      rw [pow_succ', Perm.mul_apply]
      exact ih.trans (hstep _)

/-- **Away from the split cycle nothing changes.**  When `x` and `y` lie on one cycle of `p` and
`z` does not, the cycle of `z` is the same for `p` and for `p * swap x y`. -/
theorem sameCycle_mul_swap_iff_of_not_sameCycle {p : Perm D} {x y z : D}
    (hxy : p.SameCycle x y) (hz : ¬ p.SameCycle z x) (z' : D) :
    (p * Equiv.swap x y).SameCycle z z' ↔ p.SameCycle z z' := by
  have hpow : ∀ n : ℕ, ((p * Equiv.swap x y) ^ n) z = (p ^ n) z := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero]
    | succ n ih =>
        have hx : (p ^ n) z ≠ x := fun h => hz ⟨(n : ℤ), by rw [zpow_natCast]; exact h⟩
        have hy : (p ^ n) z ≠ y := fun h =>
          hz (Perm.SameCycle.trans ⟨(n : ℤ), by rw [zpow_natCast]; exact h⟩ hxy.symm)
        rw [pow_succ', Perm.mul_apply, ih, Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hx hy,
          pow_succ', Perm.mul_apply]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n : ℤ), by rw [zpow_natCast, ← hpow n, hn]⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n : ℤ), by rw [zpow_natCast, hpow n, hn]⟩

end Perm

/-- **A simple closed walk transports along an embedding of darts** that commutes with `alpha`
and keeps the vertices. -/
theorem isSimpleClosedWalk_map {M M' : CombMap.{u}} (ι : M.Dart → M'.Dart)
    (hι : Function.Injective ι) (halpha : ∀ d, M'.alpha (ι d) = ι (M.alpha d))
    (hvertex : ∀ d e, M'.vertexOf (ι d) = M'.vertexOf (ι e) ↔ M.vertexOf d = M.vertexOf e)
    {w : List M.Dart} (hw : IsSimpleClosedWalk M w) : IsSimpleClosedWalk M' (w.map ι) where
  ne_nil := by simpa only [ne_eq, List.map_eq_nil_iff] using hw.ne_nil
  chain := (List.isChain_map ι).mpr <| hw.chain.imp_of_mem_imp fun d e _ _ h =>
    show M'.vertexOf (M'.alpha (ι d)) = M'.vertexOf (ι e) by
      rw [halpha, hvertex]
      exact h
  closes := by
    rw [List.getLast_map, List.head_map, halpha, hvertex]
    exact hw.closes
  vertex_nodup := by
    rw [List.map_map]
    exact List.Nodup.map_on (fun d hd e he h =>
      List.inj_on_of_nodup_map hw.vertex_nodup hd he ((hvertex d e).mp h))
      (List.Nodup.of_map M.vertexOf hw.vertex_nodup)
  alpha_not_mem d hd := by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    rw [halpha, List.mem_map_of_injective hι]
    exact hw.alpha_not_mem e he

/-- **Inserting an edge keeps the vertices of the old darts.** -/
theorem edgeInsertion_vertexOf_embed_iff (M : CombMap.{u}) (a b d e : M.Dart) :
    (EdgeInsertion.toCombMap M a b).vertexOf (EdgeInsertion.embed M d) =
        (EdgeInsertion.toCombMap M a b).vertexOf (EdgeInsertion.embed M e) ↔
      M.vertexOf d = M.vertexOf e := by
  rw [CombMap.vertexOf_eq_iff, CombMap.vertexOf_eq_iff]
  exact (PermOrbitInsert.sameCycle_some_iff (PermOrbitInsert.insertBefore M.sigma a) (some b)
    (some d) (some e)).trans (PermOrbitInsert.sameCycle_some_iff M.sigma a d e)

/-- **The vertex rotation after the reverse of the new edge** runs to the first corner. -/
theorem edgeInsertion_sigma_some_none {M : CombMap.{u}} {a b : M.Dart} (hab : a ≠ b) :
    (EdgeInsertion.toCombMap M a b).sigma (some none) = EdgeInsertion.embed M a := by
  classical
  change PermOrbitInsert.insertBefore (PermOrbitInsert.insertBefore M.sigma a) (some b)
    (some none) = some (some a)
  simp [PermOrbitInsert.insertBefore_some, hab]

/-- **A pinch keeps a simple closed walk through the pinched corner.**  Let `x` and `y` lie at one
vertex of `M`, and let the walk `p ++ d :: r` enter that vertex along the reverse `alpha x` of `x`
and leave it along `d = sigma y`.  After the pinch at `x` and `y` the walk is still a simple closed
walk. -/
theorem isSimpleClosedWalk_pinch {M : CombMap.{u}} [DecidableEq M.Dart] {x y : M.Dart}
    (hxy : M.sigma.SameCycle x y) {p r : List M.Dart} {d : M.Dart} (hp : p ≠ [])
    (hw : IsSimpleClosedWalk M (p ++ d :: r)) (hx : M.alpha (p.getLast hp) = x)
    (hy : M.sigma y = d) : IsSimpleClosedWalk (VertexJoin.toCombMap M x y) (p ++ d :: r) := by
  have hnodup : (p ++ d :: r).Nodup := List.Nodup.of_map M.vertexOf hw.vertex_nodup
  have hinj := List.inj_on_of_nodup_map hw.vertex_nodup
  have hdisj := (List.nodup_append.mp hnodup).2.2
  have hdmem : d ∈ p ++ d :: r := List.mem_append_right p List.mem_cons_self
  have hxd : M.sigma.SameCycle x d := by
    rw [← hy]
    exact hxy.trans Perm.SameCycle.rfl.apply_right
  have haway : ∀ b ∈ p ++ d :: r, b ≠ d → ∀ z,
      (VertexJoin.toCombMap M x y).vertexOf b = (VertexJoin.toCombMap M x y).vertexOf z ↔
        M.vertexOf b = M.vertexOf z := by
    intro b hb hbd z
    rw [CombMap.vertexOf_eq_iff, CombMap.vertexOf_eq_iff]
    exact sameCycle_mul_swap_iff_of_not_sameCycle hxy
      (fun h => hbd (hinj hb hdmem ((M.vertexOf_eq_iff b d).mpr (h.trans hxd)))) z
  have hstep : ∀ a b, b ∈ p ++ d :: r → b ≠ d → M.vertexOf (M.alpha a) = M.vertexOf b →
      (VertexJoin.toCombMap M x y).vertexOf ((VertexJoin.toCombMap M x y).alpha a) =
        (VertexJoin.toCombMap M x y).vertexOf b :=
    fun a b hb hbd h => ((haway b hb hbd (M.alpha a)).mpr h.symm).symm
  have hσ : (VertexJoin.toCombMap M x y).sigma x = d := by
    rw [VertexJoin.sigma_apply, Equiv.swap_apply_left, hy]
  have hheadmem : p.head hp ∈ p ++ d :: r := List.mem_append_left _ (List.head_mem hp)
  have hheadne : p.head hp ≠ d := hdisj _ (List.head_mem hp) _ List.mem_cons_self
  refine ⟨hw.ne_nil, ?_, ?_, ?_, fun e he => hw.alpha_not_mem e he⟩
  · obtain ⟨h₁, h₂, _⟩ := List.isChain_append.mp hw.chain
    refine List.isChain_append.mpr ⟨?_, ?_, ?_⟩
    · exact h₁.imp_of_mem_imp fun a b _ hb h =>
        hstep a b (List.mem_append_left _ hb) (hdisj _ hb _ List.mem_cons_self) h
    · refine h₂.imp_of_mem_tail_imp fun a b _ hb h =>
        hstep a b (List.mem_append_right p (List.mem_cons_of_mem d hb)) ?_ h
      rintro rfl
      exact (List.nodup_cons.mp (List.nodup_append.mp hnodup).2.1).1 hb
    · intro u hu v hv
      rw [List.getLast?_eq_some_getLast hp, Option.mem_def, Option.some.injEq] at hu
      rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hv
      subst hu hv
      show (VertexJoin.toCombMap M x y).vertexOf (M.alpha (p.getLast hp)) =
        (VertexJoin.toCombMap M x y).vertexOf d
      rw [hx]
      exact ((VertexJoin.toCombMap M x y).vertexOf_sigma x).symm.trans
        (congrArg (VertexJoin.toCombMap M x y).vertexOf hσ)
  · rw [List.head_append_of_ne_nil hp]
    exact ((haway (p.head hp) hheadmem hheadne _).mpr
      (hw.closes.trans (congrArg M.vertexOf (List.head_append_of_ne_nil hp))).symm).symm
  · refine List.Nodup.map_on (fun a ha b hb h => hinj ha hb ?_) hnodup
    rw [CombMap.vertexOf_eq_iff] at h ⊢
    exact sameCycle_of_sameCycle_mul_swap hxy h

end GroupApproximation.GGT.VanKampen.GeodesicCollar

#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.sameCycle_of_sameCycle_mul_swap
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.sameCycle_mul_swap_iff_of_not_sameCycle
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.isSimpleClosedWalk_map
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.edgeInsertion_vertexOf_embed_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.edgeInsertion_sigma_some_none
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.isSimpleClosedWalk_pinch
