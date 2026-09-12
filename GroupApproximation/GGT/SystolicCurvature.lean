import GroupApproximation.GGT.SystolicDisc
import GroupApproximation.Meta.AxiomGuard

/-!
# Boundary curvature of triangulated discs

For a disc `D : TriangulatedDisc X γ` whose boundary is an embedded cycle of length at
least three (`SimpleBoundary`), this module reads the boundary off the outer face and
proves the combinatorial facts behind the projection lemma:

* D3 `adj_of_bdeg_two`: a boundary vertex of degree two spans a triangle with its two
  boundary neighbours, which are then adjacent.
* D4 `exists_arc_walk`, `side_le_one`: along a boundary arc from `a` to `b`, the inner
  parallel walk through the third vertices of the boundary triangles has length
  `2 + ∑_{a<i<b} (deg i - 3)`; so on a geodesic arc `∑_{a<i<b} (4 - deg i) ≤ 1`.
* D2 `gauss_bonnet`: `∑_interior (6 - deg) + ∑_boundary (4 - deg) = 6`.
* `boundary_curvature_ge_six`: if every interior vertex has degree at least six (D1, go-sr1's
  `exists_leastDisc_typedLinks` at the constant bound six), the boundary carries curvature at
  least six.

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the
Kotowski--Ollivier route; certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace Systolic

open GGT.VanKampen

universe u

/-! ## Orbits of a permutation of a finite type -/

section Orbit

variable {D : Type*} [Fintype D] (p : Equiv.Perm D)

theorem orbit_pow_period (d : D) :
    (p ^ CombMap.orbitDegree p (Quotient.mk'' d)) d = d := by
  classical
  by_cases hd : p d = d
  · have hdegree : CombMap.orbitDegree p (Quotient.mk'' d) = 1 := by
      rw [← closedOrbitList.length_eq_orbitDegree p d]
      simp [closedOrbitList, hd]
    rw [hdegree, pow_one, hd]
  · have hdegree : CombMap.orbitDegree p (Quotient.mk'' d) = (p.cycleOf d).support.card := by
      rw [← closedOrbitList.length_eq_orbitDegree p d]
      simp [closedOrbitList, hd, Equiv.Perm.length_toList]
    rw [hdegree]
    have hmod := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply p
      (p.cycleOf d).support.card d
    simpa using hmod.symm

theorem orbit_exists_pow {d e : D} (h : p.SameCycle d e) :
    ∃ i, i < CombMap.orbitDegree p (Quotient.mk'' d) ∧ (p ^ i) d = e := by
  classical
  by_cases hd : p d = d
  · have heq : d = e := h.eq_of_left hd
    have hdegree : CombMap.orbitDegree p (Quotient.mk'' d) = 1 := by
      rw [← closedOrbitList.length_eq_orbitDegree p d]
      simp [closedOrbitList, hd]
    refine ⟨0, by omega, ?_⟩
    rw [pow_zero, Equiv.Perm.one_apply]
    exact heq
  · have hdmem : d ∈ p.support := by
      simpa [Equiv.Perm.mem_support] using hd
    obtain ⟨i, hi, hie⟩ := h.exists_pow_eq_of_mem_support hdmem
    have hdegree : CombMap.orbitDegree p (Quotient.mk'' d) = (p.cycleOf d).support.card := by
      rw [← closedOrbitList.length_eq_orbitDegree p d]
      simp [closedOrbitList, hd, Equiv.Perm.length_toList]
    exact ⟨i, hdegree ▸ hi, hie⟩

theorem orbit_pow_injective (d : D) {i j : ℕ}
    (hi : i < CombMap.orbitDegree p (Quotient.mk'' d))
    (hj : j < CombMap.orbitDegree p (Quotient.mk'' d)) (hij : (p ^ i) d = (p ^ j) d) :
    i = j := by
  classical
  by_cases hd : p d = d
  · have hdegree : CombMap.orbitDegree p (Quotient.mk'' d) = 1 := by
      rw [← closedOrbitList.length_eq_orbitDegree p d]
      simp [closedOrbitList, hd]
    omega
  · let l := p.toList d
    have hlength : l.length = CombMap.orbitDegree p (Quotient.mk'' d) := by
      rw [← closedOrbitList.length_eq_orbitDegree p d]
      simp [l, closedOrbitList, hd]
    have hi' : i < l.length := by rw [hlength]; exact hi
    have hj' : j < l.length := by rw [hlength]; exact hj
    have hget : l[i] = l[j] := by
      change (p.toList d)[i] = (p.toList d)[j]
      rw [Equiv.Perm.getElem_toList p d i hi', Equiv.Perm.getElem_toList p d j hj']
      exact hij
    exact (Equiv.Perm.nodup_toList p d).getElem_inj_iff.mp hget

omit [Fintype D] in
theorem pow_succ_apply' (d : D) (k : ℕ) : (p ^ (k + 1)) d = p ((p ^ k) d) := by
  rw [pow_succ', Equiv.Perm.mul_apply]

end Orbit

variable {V : Type u} {X : TriangleComplex V} {γ : List V}

namespace TriangulatedDisc

variable (D : TriangulatedDisc X γ)

/-! ## The boundary cycle -/

/-- The length of the boundary. -/
noncomputable def blen : ℕ := D.map.faceDegree D.outer

/-- The `k`-th boundary dart. -/
def bdart (k : ℕ) : D.map.Dart := (D.map.facePerm ^ k) D.base

/-- The `k`-th boundary vertex. -/
def bvert (k : ℕ) : D.map.Vertex := D.map.vertexOf (D.bdart k)

/-- The degree of the `k`-th boundary vertex. -/
noncomputable def bdeg (k : ℕ) : ℕ := D.map.vertexDegree (D.bvert k)

theorem bdart_succ (k : ℕ) : D.bdart (k + 1) = D.map.facePerm (D.bdart k) :=
  pow_succ_apply' _ _ _

theorem faceOf_bdart (k : ℕ) : D.map.faceOf (D.bdart k) = D.outer := by
  induction k with
  | zero =>
    change D.map.faceOf ((D.map.facePerm ^ 0) D.base) = D.outer
    rw [pow_zero, Equiv.Perm.one_apply, D.base_outer]
  | succ k ih => rw [D.bdart_succ, D.map.faceOf_facePerm, ih]

theorem blen_eq : D.blen = CombMap.orbitDegree D.map.facePerm (Quotient.mk'' D.base) := by
  unfold blen CombMap.faceDegree
  rw [← D.base_outer]
  rfl

theorem bdart_add_blen (k : ℕ) : D.bdart (k + D.blen) = D.bdart k := by
  unfold bdart
  rw [pow_add, Equiv.Perm.mul_apply, D.blen_eq, orbit_pow_period]

theorem bdart_mod (k : ℕ) : D.bdart k = D.bdart (k % D.blen) := by
  conv_lhs => rw [← Nat.mod_add_div k D.blen]
  induction k / D.blen with
  | zero => rw [mul_zero, add_zero]
  | succ m ih => rw [Nat.mul_succ, ← add_assoc, D.bdart_add_blen, ih]

theorem exists_bdart {d : D.map.Dart} (hd : D.map.faceOf d = D.outer) :
    ∃ k, k < D.blen ∧ D.bdart k = d := by
  have hcyc : D.map.facePerm.SameCycle D.base d := by
    rw [← D.map.faceOf_eq_iff]
    exact D.base_outer.trans hd.symm
  obtain ⟨i, hi, hie⟩ := orbit_exists_pow D.map.facePerm hcyc
  exact ⟨i, D.blen_eq ▸ hi, hie⟩

theorem bdart_injective {i j : ℕ} (hi : i < D.blen) (hj : j < D.blen)
    (h : D.bdart i = D.bdart j) : i = j :=
  orbit_pow_injective D.map.facePerm D.base (D.blen_eq ▸ hi) (D.blen_eq ▸ hj) h

theorem vertexOf_alpha_bdart (k : ℕ) :
    D.map.vertexOf (D.map.alpha (D.bdart k)) = D.bvert (k + 1) := by
  unfold bvert
  rw [D.bdart_succ, vertexOf_facePerm]

theorem sigma_alpha_bdart (k : ℕ) : D.map.sigma (D.map.alpha (D.bdart k)) = D.bdart (k + 1) := by
  rw [D.bdart_succ]
  rfl

theorem adj_bvert (k : ℕ) : X.G.Adj (D.vtx (D.bvert k)) (D.vtx (D.bvert (k + 1))) := by
  have h := D.adj (D.bdart k)
  rw [D.vertexOf_alpha_bdart] at h
  exact h

theorem length_eq : γ.length = D.blen + 1 := by
  have h := congrArg List.length D.boundary
  rw [List.length_ofFn] at h
  exact h.symm

theorem getElem?_eq {k : ℕ} (hk : k ≤ D.blen) : γ[k]? = some (D.vtx (D.bvert k)) := by
  have h : (List.ofFn (fun t : Fin (D.map.faceDegree D.outer + 1) =>
      D.vtx (D.map.vertexOf ((D.map.facePerm ^ (t : ℕ)) D.base))))[k]? = γ[k]? :=
    congrArg (fun l : List V => l[k]?) D.boundary
  rw [← h, List.getElem?_ofFn]
  have hk' : k < D.map.faceDegree D.outer + 1 := Nat.lt_succ_of_le hk
  simp only [hk', dite_true]
  rfl

/-- **An embedded boundary cycle of length at least three.** -/
structure SimpleBoundary : Prop where
  three_le : 3 ≤ D.blen
  inj : ∀ i j, i < D.blen → j < D.blen → D.vtx (D.bvert i) = D.vtx (D.bvert j) → i = j

variable {D}

theorem SimpleBoundary.blen_pos (hS : D.SimpleBoundary) : 0 < D.blen := by
  have := hS.three_le
  omega

theorem SimpleBoundary.mod_eq_of_bvert_eq (hS : D.SimpleBoundary) {i j : ℕ}
    (h : D.bvert i = D.bvert j) : i % D.blen = j % D.blen := by
  have hpos := hS.blen_pos
  have hi : D.bvert i = D.bvert (i % D.blen) := by unfold bvert; rw [D.bdart_mod i]
  have hj : D.bvert j = D.bvert (j % D.blen) := by unfold bvert; rw [D.bdart_mod j]
  rw [hi, hj] at h
  exact hS.inj _ _ (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) (congrArg D.vtx h)

theorem SimpleBoundary.bdart_eq_of_bvert_eq (hS : D.SimpleBoundary) {i j : ℕ}
    (h : D.bvert i = D.bvert j) : D.bdart i = D.bdart j := by
  rw [D.bdart_mod i, D.bdart_mod j, hS.mod_eq_of_bvert_eq h]

theorem SimpleBoundary.alpha_bdart_inner (hS : D.SimpleBoundary) (k : ℕ) :
    D.map.faceOf (D.map.alpha (D.bdart k)) ≠ D.outer := by
  intro h
  obtain ⟨j, -, hj⟩ := D.exists_bdart h
  have hv : D.bvert j = D.bvert (k + 1) := by
    unfold bvert
    rw [hj]
    exact D.vertexOf_alpha_bdart k
  have hal : D.map.alpha (D.bdart k) = D.bdart (k + 1) := hj.symm.trans (hS.bdart_eq_of_bvert_eq hv)
  have h2 : D.bvert (k + 2) = D.bvert k := by
    unfold bvert
    rw [show k + 2 = (k + 1) + 1 from rfl, D.bdart_succ, facePerm_apply, ← hal,
      D.map.alpha_involutive, D.map.vertexOf_sigma]
  have hmod := hS.mod_eq_of_bvert_eq h2
  have h3 := hS.three_le
  have hdvd : D.blen ∣ 2 := by
    have := Nat.sub_mod_eq_zero_of_mod_eq hmod
    rw [show k + 2 - k = 2 by omega] at this
    exact Nat.dvd_of_mod_eq_zero this
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-! ## The rotation at a boundary vertex -/

variable (D)

/-- The `j`-th dart around the boundary vertex `k + 1`, starting at the outgoing boundary
dart. -/
def brot (k j : ℕ) : D.map.Dart := (D.map.sigma ^ j) (D.bdart (k + 1))

theorem brot_succ (k j : ℕ) : D.brot k (j + 1) = D.map.sigma (D.brot k j) :=
  pow_succ_apply' _ _ _

theorem vertexOf_brot (k j : ℕ) : D.map.vertexOf (D.brot k j) = D.bvert (k + 1) := by
  induction j with
  | zero =>
    change D.map.vertexOf ((D.map.sigma ^ 0) (D.bdart (k + 1))) = _
    rw [pow_zero, Equiv.Perm.one_apply]
    rfl
  | succ j ih => rw [D.brot_succ, D.map.vertexOf_sigma, ih]

theorem bdeg_eq (k : ℕ) :
    D.bdeg (k + 1) = CombMap.orbitDegree D.map.sigma (Quotient.mk'' (D.bdart (k + 1))) :=
  rfl

theorem bdeg_pos (k : ℕ) : 0 < D.bdeg k := vertexDegree_pos D.map (D.bdart k)

theorem brot_injective (k : ℕ) {i j : ℕ} (hi : i < D.bdeg (k + 1)) (hj : j < D.bdeg (k + 1))
    (h : D.brot k i = D.brot k j) : i = j :=
  orbit_pow_injective D.map.sigma (D.bdart (k + 1)) hi hj h

theorem brot_last (k : ℕ) : D.brot k (D.bdeg (k + 1) - 1) = D.map.alpha (D.bdart k) := by
  have hpos := D.bdeg_pos (k + 1)
  have hvert : (Quotient.mk'' (D.map.alpha (D.bdart k)) : D.map.Vertex) = D.bvert (k + 1) :=
    D.vertexOf_alpha_bdart k
  have hper : (D.map.sigma ^ D.bdeg (k + 1)) (D.map.alpha (D.bdart k)) = D.map.alpha (D.bdart k) := by
    have h := orbit_pow_period D.map.sigma (D.map.alpha (D.bdart k))
    rw [hvert] at h
    exact h
  unfold brot
  rw [← D.sigma_alpha_bdart k, ← Equiv.Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hpos, hper]

theorem vertexOf_alpha_brot_zero (k : ℕ) :
    D.map.vertexOf (D.map.alpha (D.brot k 0)) = D.bvert (k + 2) := by
  change D.map.vertexOf (D.map.alpha ((D.map.sigma ^ 0) (D.bdart (k + 1)))) = _
  rw [pow_zero, Equiv.Perm.one_apply, D.vertexOf_alpha_bdart]

theorem vertexOf_alpha_brot_last (k : ℕ) :
    D.map.vertexOf (D.map.alpha (D.brot k (D.bdeg (k + 1) - 1))) = D.bvert k := by
  rw [D.brot_last, D.map.alpha_involutive]
  rfl

variable {D}

theorem SimpleBoundary.corner_inner (hS : D.SimpleBoundary) (k : ℕ) {j : ℕ}
    (hj : j + 1 < D.bdeg (k + 1)) : D.map.faceOf (D.map.alpha (D.brot k j)) ≠ D.outer := by
  intro h
  obtain ⟨m, -, hm⟩ := D.exists_bdart h
  have hnext : D.bdart (m + 1) = D.brot k (j + 1) := by
    rw [D.bdart_succ, hm, facePerm_alpha, D.brot_succ]
  have hv : D.bvert (m + 1) = D.bvert (k + 1) := by
    unfold bvert
    rw [hnext]
    exact D.vertexOf_brot k (j + 1)
  have heq : D.brot k (j + 1) = D.brot k 0 := by
    rw [← hnext, hS.bdart_eq_of_bvert_eq hv]
    change D.bdart (k + 1) = (D.map.sigma ^ 0) (D.bdart (k + 1))
    rw [pow_zero, Equiv.Perm.one_apply]
  have := D.brot_injective k hj (D.bdeg_pos (k + 1)) heq
  omega

/-- **The link walk at a boundary vertex**: consecutive heads around the vertex span a
triangle with it. -/
theorem SimpleBoundary.tri_brot (hS : D.SimpleBoundary) (k : ℕ) {j : ℕ}
    (hj : j + 1 < D.bdeg (k + 1)) :
    X.Tri (D.vtx (D.bvert (k + 1))) (D.vtx (D.map.vertexOf (D.map.alpha (D.brot k j))))
      (D.vtx (D.map.vertexOf (D.map.alpha (D.brot k (j + 1))))) := by
  have h := (D.tri (D.map.alpha (D.brot k j)) (hS.corner_inner k hj)).2
  rw [facePerm_alpha, ← D.brot_succ, D.vertexOf_brot, perm_pow_two_apply, facePerm_alpha,
    ← D.brot_succ, vertexOf_facePerm] at h
  exact X.tri_swap12 h

theorem SimpleBoundary.two_le_bdeg (hS : D.SimpleBoundary) (k : ℕ) : 2 ≤ D.bdeg (k + 1) := by
  by_contra hlt
  have h1 : D.bdeg (k + 1) = 1 := by have := D.bdeg_pos (k + 1); omega
  have hl := D.brot_last k
  rw [h1] at hl
  change (D.map.sigma ^ 0) (D.bdart (k + 1)) = _ at hl
  rw [pow_zero, Equiv.Perm.one_apply] at hl
  apply hS.alpha_bdart_inner k
  rw [← hl]
  exact D.faceOf_bdart (k + 1)

/-- **D3**: a boundary vertex of degree two makes its boundary neighbours adjacent. -/
theorem SimpleBoundary.adj_of_bdeg_two (hS : D.SimpleBoundary) (k : ℕ)
    (h2 : D.bdeg (k + 1) = 2) : X.G.Adj (D.vtx (D.bvert k)) (D.vtx (D.bvert (k + 2))) := by
  have ht := hS.tri_brot k (j := 0) (by omega)
  rw [D.vertexOf_alpha_brot_zero] at ht
  have hlast : D.map.vertexOf (D.map.alpha (D.brot k 1)) = D.bvert k := by
    have := D.vertexOf_alpha_brot_last k
    rw [h2] at this
    exact this
  rw [hlast] at ht
  exact (X.tri_adj ht).2.1.symm

/-- The triangle of `X` on the boundary edge `k → k+1`. -/
theorem SimpleBoundary.tri_edge (hS : D.SimpleBoundary) (k : ℕ) :
    X.Tri (D.vtx (D.bvert (k + 1))) (D.vtx (D.bvert k))
      (D.vtx (D.map.vertexOf ((D.map.facePerm ^ 2) (D.map.alpha (D.bdart k))))) := by
  have h := (D.tri (D.map.alpha (D.bdart k)) (hS.alpha_bdart_inner k)).2
  rw [D.vertexOf_alpha_bdart, vertexOf_facePerm, D.map.alpha_involutive] at h
  exact h

variable (D)

/-- The third vertex of the inner triangle on the boundary edge `k → k+1`. -/
def tvert (k : ℕ) : D.map.Vertex :=
  D.map.vertexOf ((D.map.facePerm ^ 2) (D.map.alpha (D.bdart k)))

theorem tvert_succ_eq (k : ℕ) :
    D.tvert (k + 1) = D.map.vertexOf (D.map.alpha (D.brot k 1)) := by
  unfold tvert
  rw [perm_pow_two_apply, vertexOf_facePerm, facePerm_alpha]
  show _ = D.map.vertexOf (D.map.alpha ((D.map.sigma ^ 1) (D.bdart (k + 1))))
  rw [pow_one]

variable {D}

theorem SimpleBoundary.tvert_eq (hS : D.SimpleBoundary) (k : ℕ) (h2 : 2 ≤ D.bdeg (k + 1)) :
    D.tvert k = D.map.vertexOf (D.map.alpha (D.brot k (D.bdeg (k + 1) - 2))) := by
  have hj : D.bdeg (k + 1) - 2 + 1 < D.bdeg (k + 1) := by omega
  have h3 := (D.tri (D.map.alpha (D.brot k (D.bdeg (k + 1) - 2))) (hS.corner_inner k hj)).1
  have hstep : D.map.facePerm (D.map.alpha (D.brot k (D.bdeg (k + 1) - 2))) =
      D.map.alpha (D.bdart k) := by
    rw [facePerm_alpha, ← D.brot_succ, show D.bdeg (k + 1) - 2 + 1 = D.bdeg (k + 1) - 1 by omega,
      D.brot_last]
  unfold tvert
  rw [← hstep, ← Equiv.Perm.mul_apply, ← pow_succ, h3]

/-! ## D4: the parallel walk -/

theorem SimpleBoundary.exists_link_walk (hS : D.SimpleBoundary) (k : ℕ) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j < D.bdeg (k + 1)) :
    ∃ p : X.G.Walk (D.vtx (D.map.vertexOf (D.map.alpha (D.brot k 1))))
      (D.vtx (D.map.vertexOf (D.map.alpha (D.brot k j)))), p.length = j - 1 := by
  induction j, hj1 using Nat.le_induction with
  | base => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ j hj1 ih =>
    obtain ⟨p, hp⟩ := ih (by omega)
    have ht := hS.tri_brot k (j := j) hj
    refine ⟨p.concat (X.tri_adj ht).2.1, ?_⟩
    rw [SimpleGraph.Walk.length_concat, hp]
    omega

theorem SimpleBoundary.exists_tvert_walk (hS : D.SimpleBoundary) (k : ℕ)
    (h3 : 3 ≤ D.bdeg (k + 1)) :
    ∃ p : X.G.Walk (D.vtx (D.tvert k)) (D.vtx (D.tvert (k + 1))), p.length = D.bdeg (k + 1) - 3 := by
  obtain ⟨p, hp⟩ := hS.exists_link_walk k (j := D.bdeg (k + 1) - 2) (by omega) (by omega)
  rw [hS.tvert_eq k (by omega), D.tvert_succ_eq]
  exact ⟨p.reverse, by rw [SimpleGraph.Walk.length_reverse, hp]; omega⟩

theorem exists_bdry_walk {a c : ℕ} (hac : a ≤ c) :
    ∃ p : X.G.Walk (D.vtx (D.bvert a)) (D.vtx (D.bvert c)), p.length = c - a := by
  induction c, hac using Nat.le_induction with
  | base => exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | succ c hac ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨p.concat (D.adj_bvert c), ?_⟩
    rw [SimpleGraph.Walk.length_concat, hp]
    omega

theorem SimpleBoundary.exists_parallel_walk (hS : D.SimpleBoundary) {a c : ℕ} (hac : a ≤ c)
    (hdeg : ∀ i, a < i → i ≤ c → 3 ≤ D.bdeg i) :
    ∃ p : X.G.Walk (D.vtx (D.bvert a)) (D.vtx (D.tvert c)),
      p.length = 1 + ∑ i ∈ Finset.Ioc a c, (D.bdeg i - 3) := by
  induction c, hac using Nat.le_induction with
  | base =>
    have ht := hS.tri_edge a
    refine ⟨SimpleGraph.Walk.cons (X.tri_adj ht).2.1 SimpleGraph.Walk.nil, ?_⟩
    have h0 : ∑ i ∈ Finset.Ioc a a, (D.bdeg i - 3) = 0 := by simp
    rw [h0]
    rfl
  | succ c hac ih =>
    obtain ⟨p, hp⟩ := ih fun i hai hic => hdeg i hai (by omega)
    obtain ⟨q, hq⟩ := hS.exists_tvert_walk c (hdeg (c + 1) (by omega) le_rfl)
    refine ⟨p.append q, ?_⟩
    rw [SimpleGraph.Walk.length_append, hp, hq, Finset.sum_Ioc_succ_top (by omega)]
    omega

/-- **D4, walk form**: the boundary arc from `a` to `b` has an inner parallel walk of length
`2 + ∑_{a<i<b} (deg i - 3)`. -/
theorem SimpleBoundary.exists_arc_walk (hS : D.SimpleBoundary) {a b : ℕ} (hab : a < b)
    (hdeg : ∀ i, a < i → i < b → 3 ≤ D.bdeg i) :
    ∃ p : X.G.Walk (D.vtx (D.bvert a)) (D.vtx (D.bvert b)),
      p.length = 2 + ∑ i ∈ Finset.Ioo a b, (D.bdeg i - 3) := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  obtain ⟨p, hp⟩ := hS.exists_parallel_walk (a := a) (c := b') (by omega)
    fun i hai hib => hdeg i hai (by omega)
  have ht := hS.tri_edge b'
  refine ⟨p.concat (X.tri_adj ht).2.2.symm, ?_⟩
  rw [SimpleGraph.Walk.length_concat, hp]
  have hIoo : Finset.Ioo a (b' + 1) = Finset.Ioc a b' := by
    ext i
    simp only [Finset.mem_Ioo, Finset.mem_Ioc]
    omega
  rw [hIoo]
  omega

/-- Interior vertices of a geodesic boundary arc have degree at least three. -/
theorem SimpleBoundary.three_le_bdeg_of_geodesic (hS : D.SimpleBoundary) {a b : ℕ}
    (hgeo : X.G.dist (D.vtx (D.bvert a)) (D.vtx (D.bvert b)) = b - a) {i : ℕ} (hai : a < i)
    (hib : i < b) : 3 ≤ D.bdeg i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have h2 := hS.two_le_bdeg k
  by_contra hlt
  have hadj := hS.adj_of_bdeg_two k (by omega)
  obtain ⟨p, hp⟩ := exists_bdry_walk (D := D) (a := a) (c := k) (by omega)
  obtain ⟨q, hq⟩ := exists_bdry_walk (D := D) (a := k + 2) (c := b) (by omega)
  have hle := SimpleGraph.dist_le ((p.concat hadj).append q)
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_concat, hp, hq, hgeo] at hle
  omega

/-- **D4**: on a geodesic boundary arc, the boundary curvature `∑_{a<i<b} (4 - deg i)` is at
most one. -/
theorem SimpleBoundary.side_le_one (hS : D.SimpleBoundary) {a b : ℕ} (hab : a < b)
    (hgeo : X.G.dist (D.vtx (D.bvert a)) (D.vtx (D.bvert b)) = b - a) :
    ∑ i ∈ Finset.Ioo a b, ((4 : ℤ) - D.bdeg i) ≤ 1 := by
  have hdeg : ∀ i, a < i → i < b → 3 ≤ D.bdeg i :=
    fun i hai hib => hS.three_le_bdeg_of_geodesic hgeo hai hib
  obtain ⟨p, hp⟩ := hS.exists_arc_walk hab hdeg
  have hle := SimpleGraph.dist_le p
  rw [hp, hgeo] at hle
  have hcast : ∑ i ∈ Finset.Ioo a b, ((4 : ℤ) - D.bdeg i) =
      ((Finset.Ioo a b).card : ℤ) - ∑ i ∈ Finset.Ioo a b, ((D.bdeg i - 3 : ℕ) : ℤ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := hdeg i (Finset.mem_Ioo.mp hi).1 (Finset.mem_Ioo.mp hi).2
    push_cast [this]
    ring
  rw [hcast, Nat.card_Ioo]
  have hle' : ((b - a : ℕ) : ℤ) ≤ 2 + ((∑ i ∈ Finset.Ioo a b, (D.bdeg i - 3) : ℕ) : ℤ) := by
    exact_mod_cast hle
  push_cast [Nat.cast_sum] at hle' ⊢
  omega

/-! ## D2: Gauss--Bonnet -/

theorem not_interior_iff (w : D.map.Vertex) :
    ¬ D.Interior w ↔ ∃ k, k < D.blen ∧ D.bvert k = w := by
  constructor
  · intro hw
    unfold Interior at hw
    push Not at hw
    obtain ⟨d, hdw, hdo⟩ := hw
    obtain ⟨k, hk, hkd⟩ := D.exists_bdart hdo
    exact ⟨k, hk, by unfold bvert; rw [hkd]; exact hdw⟩
  · rintro ⟨k, -, rfl⟩ hint
    exact hint (D.bdart k) rfl (D.faceOf_bdart k)

open Classical in
theorem SimpleBoundary.card_boundary (hS : D.SimpleBoundary) :
    (Finset.univ.filter fun w : D.map.Vertex => ¬ D.Interior w).card = D.blen := by
  classical
  rw [← Finset.card_range D.blen]
  refine (Finset.card_bij (fun k _ => D.bvert k) ?_ ?_ ?_).symm
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (not_interior_iff (D := D) _).mpr ⟨k, Finset.mem_range.mp hk, rfl⟩
  · intro i hi j hj hij
    exact hS.inj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (congrArg D.vtx hij)
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨k, hk, rfl⟩ := (not_interior_iff (D := D) w).mp hw
    exact ⟨k, Finset.mem_range.mpr hk, rfl⟩

open Classical in
/-- **D2, combinatorial Gauss--Bonnet** for a disc with embedded boundary. -/
theorem SimpleBoundary.gauss_bonnet (hS : D.SimpleBoundary) :
    ∑ w : D.map.Vertex, ((if D.Interior w then (6 : ℤ) else 4) - D.map.vertexDegree w) = 6 := by
  have hE := D.vertexCount_add_innerFaceCount
  have hF := D.two_mul_edgeCount
  have hdeg := D.map.sum_vertexDegree_eq_two_mul_edgeCount
  have hB := hS.card_boundary
  have hsplit : ∑ w : D.map.Vertex, (if D.Interior w then (6 : ℤ) else 4) =
      6 * D.map.vertexCount - 2 * D.blen := by
    have h1 : ∀ w : D.map.Vertex, (if D.Interior w then (6 : ℤ) else 4) =
        6 - (if ¬ D.Interior w then (2 : ℤ) else 0) := by
      intro w; by_cases hw : D.Interior w <;> simp [hw]
    rw [Finset.sum_congr rfl fun w _ => h1 w, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, hB, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    simp only [nsmul_eq_mul]
    unfold CombMap.vertexCount
    ring
  rw [Finset.sum_sub_distrib, hsplit]
  have hdegZ : ∑ w : D.map.Vertex, (D.map.vertexDegree w : ℤ) = 2 * D.map.edgeCount := by
    exact_mod_cast hdeg
  rw [hdegZ]
  have hEZ : (D.map.vertexCount : ℤ) + D.innerFaceCount = D.map.edgeCount + 1 := by
    exact_mod_cast hE
  have hFZ : 2 * (D.map.edgeCount : ℤ) = 3 * D.innerFaceCount + D.blen := by
    exact_mod_cast hF
  omega

open Classical in
/-- **The boundary carries curvature at least six** when every interior vertex has degree at
least six. -/
theorem SimpleBoundary.boundary_curvature_ge_six (hS : D.SimpleBoundary)
    (hint : ∀ w : D.map.Vertex, D.Interior w → 6 ≤ D.map.vertexDegree w) :
    6 ≤ ∑ k ∈ Finset.range D.blen, ((4 : ℤ) - D.bdeg k) := by
  have hgb := hS.gauss_bonnet
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ D.Interior] at hgb
  have hin : ∑ w ∈ Finset.univ.filter D.Interior,
      ((if D.Interior w then (6 : ℤ) else 4) - D.map.vertexDegree w) ≤ 0 := by
    refine Finset.sum_nonpos fun w hw => ?_
    have hw' := (Finset.mem_filter.mp hw).2
    rw [if_pos hw']
    have := hint w hw'
    omega
  have hbd : ∑ w ∈ Finset.univ.filter (fun w => ¬ D.Interior w),
      ((if D.Interior w then (6 : ℤ) else 4) - D.map.vertexDegree w) =
      ∑ k ∈ Finset.range D.blen, ((4 : ℤ) - D.bdeg k) := by
    refine (Finset.sum_bij (fun k _ => D.bvert k) ?_ ?_ ?_ ?_).symm
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (not_interior_iff (D := D) _).mpr ⟨k, Finset.mem_range.mp hk, rfl⟩
    · intro i hi j hj hij
      exact hS.inj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (congrArg D.vtx hij)
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      obtain ⟨k, hk, rfl⟩ := (not_interior_iff (D := D) w).mp hw
      exact ⟨k, Finset.mem_range.mpr hk, rfl⟩
    · intro k hk
      have hni : ¬ D.Interior (D.bvert k) :=
        (not_interior_iff (D := D) _).mpr ⟨k, Finset.mem_range.mp hk, rfl⟩
      rw [if_neg hni]
      rfl
  rw [hbd] at hgb
  linarith

end TriangulatedDisc

end Systolic
end GroupApproximation

open GroupApproximation.Systolic

#audit_axioms TriangulatedDisc.SimpleBoundary.adj_of_bdeg_two
#audit_axioms TriangulatedDisc.SimpleBoundary.exists_arc_walk
#audit_axioms TriangulatedDisc.SimpleBoundary.side_le_one
#audit_axioms TriangulatedDisc.SimpleBoundary.gauss_bonnet
#audit_axioms TriangulatedDisc.SimpleBoundary.boundary_curvature_ge_six
