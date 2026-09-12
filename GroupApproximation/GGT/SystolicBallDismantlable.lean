import GroupApproximation.GGT.SystolicDismantlable
import GroupApproximation.GGT.SystolicGraphConditions
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sets

/-!
# Breadth-first dismantling of intersections of balls

Let `G` be a connected graph satisfying the four metric conditions of
`GGT/SystolicGraphConditions`: projection cliques, the triangle condition, and no induced four-
or five-cycles.  Let `H` be a finite intersection of balls `B_R(s)`, `s ∈ S`.

* `BFS.dist_le_of_geodesicPredecessor`: balls are closed under geodesic predecessors.  If `o`
  and `x` lie in `B_r(s)` and `c` is a neighbour of `x` one step closer to `o`, then `c` lies
  in `B_r(s)`.  So `H` contains, for every `o ∈ H`, each neighbour of each `x ∈ H` that is one
  step closer to `o`.
* `BFS.exists_isBFSRank`: fix `o ∈ H`.  Then `H` has a breadth-first ranking `ρ`.  It is
  injective, increases with the distance to `o`, and within a level follows the ranks of the
  parents.  The parent of `x` is its least-ranked neighbour in `H` one step closer to `o`.
* `BFS.adj_parent_of_same_level` (Chepoi): the parent of `u` is adjacent to every neighbour of
  `u` on the same level that is ranked before `u`.  A counterexample closes an induced four- or
  five-cycle.
* `exists_dismantlingRank_of_forall_dist_le`: every vertex of `H` that is not ranked first is
  dominated by an earlier vertex (its parent) within the vertices ranked no later than it.  So
  deleting the vertices of `H` from the last-ranked one down dismantles `H` onto one vertex.
* `dismantlable_of_forall_dist_le`: so `H` is `Dismantlable` in the sense of
  `GGT/SystolicDismantlable`.

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the
Kotowski--Ollivier route; certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace Systolic
namespace BFS

variable {V : Type*}

/-- `f` is a parent of `x` for the ranking `ρ`.  It is a neighbour of `x` in `H`, one step
closer to `o`, of least rank among all such neighbours. -/
def IsBFSParent (G : SimpleGraph V) (o : V) (H : Finset V) (ρ : V → ℕ) (x f : V) : Prop :=
  f ∈ H ∧ G.Adj x f ∧ G.dist o f + 1 = G.dist o x ∧
    ∀ c ∈ H, G.Adj x c → G.dist o c + 1 = G.dist o x → ρ f ≤ ρ c

/-- `ρ` is a breadth-first ranking from `o` of the vertices of `H` at distance at most `k` from
`o`.  It is injective, increases with the distance to `o`, and on each level is ordered by the
ranks of the parents. -/
def IsBFSRank (G : SimpleGraph V) (o : V) (H : Finset V) (k : ℕ) (ρ : V → ℕ) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, G.dist o x ≤ k → G.dist o y ≤ k →
    (ρ x = ρ y → x = y) ∧ (G.dist o x < G.dist o y → ρ x < ρ y) ∧
      (G.dist o x = G.dist o y → ρ x < ρ y → ∀ fx fy, IsBFSParent G o H ρ x fx →
        IsBFSParent G o H ρ y fy → ρ fx ≤ ρ fy)

variable {G : SimpleGraph V}

/-- The distances from `o` to two adjacent vertices differ by at most one. -/
theorem adjDist_le_succ (hconn : G.Connected) (o : V) {a b : V} (h : G.Adj a b) :
    G.dist o a ≤ G.dist o b + 1 := by
  have h1 : G.dist o a ≤ G.dist o b + G.dist b a := hconn.dist_triangle
  rwa [SimpleGraph.dist_eq_one_iff_adj.mpr h.symm] at h1

/-- A vertex at positive distance from `o` has a neighbour one step closer to `o`. -/
theorem exists_adj_predecessor (hconn : G.Connected) (o : V) {x : V} (hx : 0 < G.dist o x) :
    ∃ c, G.Adj x c ∧ G.dist o c + 1 = G.dist o x := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x o
  have hxo : G.dist o x = G.dist x o := SimpleGraph.dist_comm
  have hnp : ¬ p.Nil := SimpleGraph.Walk.not_nil_iff_lt_length.mpr (by omega)
  refine ⟨p.snd, p.adj_snd hnp, ?_⟩
  have h1 : G.dist o p.snd ≤ p.tail.length := by
    rw [SimpleGraph.dist_comm]
    exact SimpleGraph.dist_le p.tail
  have h2 : p.tail.length + 1 = p.length := p.length_tail_add_one hnp
  have h3 := adjDist_le_succ hconn o (p.adj_snd hnp)
  omega

/-- **Balls are closed under geodesic predecessors.**  Suppose `o` and `x` lie in the ball of
radius `r` about `s`, and `c` is a neighbour of `x` one step closer to `o`.  Then `c` lies in
the ball as well.  The proof is by induction on the distance from `o` to `c`.  If `c` left the
ball, a predecessor `c'` of `c` would give a contradiction.  Either the projection clique at
`c` makes `x c'` an edge, or the triangle condition on `c c'` gives a second neighbour of `x`
on the level of `c`, to which the induction hypothesis applies. -/
theorem dist_le_of_geodesicPredecessor (hconn : G.Connected) (hF1 : ProjectionClique G)
    (hF2 : TriangleCondition G) (s o : V) :
    ∀ (m : ℕ) (x c : V) (r : ℕ), G.dist o c = m → G.Adj x c →
      G.dist o c + 1 = G.dist o x → G.dist s o ≤ r → G.dist s x ≤ r → G.dist s c ≤ r := by
  intro m
  induction m with
  | zero =>
    intro x c r hm _ _ hso _
    have hoc : o = c := hconn.dist_eq_zero_iff.mp hm
    rw [← hoc]
    exact hso
  | succ m ih =>
    intro x c r hm hxc hcx hso hsx
    by_contra hsc
    have hA := adjDist_le_succ hconn s hxc.symm
    obtain ⟨c', hcc', hc'⟩ := exists_adj_predecessor hconn o (x := c) (by omega)
    have hc'm : G.dist o c' = m := by omega
    have h1 : G.dist s c' ≤ r + 1 := ih c c' (r + 1) hc'm hcc' hc' (by omega) (by omega)
    have h2 := adjDist_le_succ hconn s hcc'
    have hxc' : x ≠ c' := fun h => by
      have := congrArg (G.dist o) h
      omega
    have hnadj : ¬ G.Adj x c' := fun h => by
      have := adjDist_le_succ hconn o h
      omega
    rcases Nat.lt_or_ge (G.dist s c') (r + 1) with hlt | hge
    · exact hnadj (hF1 s c x c' hxc.symm hcc' (by omega) (by omega) hxc')
    · obtain ⟨z, hcz, hc'z, hz⟩ := hF2 s c c' hcc' (by omega) (by omega)
      have hxz : G.Adj x z := by
        by_cases hxz : x = z
        · rw [← hxz] at hc'z
          exact absurd hc'z.symm hnadj
        · exact hF1 s c x z hxc.symm hcz (by omega) hz hxz
      have hoz1 := adjDist_le_succ hconn o hc'z.symm
      have hoz2 := adjDist_le_succ hconn o hxz
      have h3 : G.dist s c' ≤ r := ih z c' r hc'm hc'z.symm (by omega) hso (by omega)
      omega

/-- An intersection of balls contains, for each of its points `o`, every geodesic predecessor
towards `o` of each of its points. -/
theorem lowerClosed_of_forall_dist_le (hconn : G.Connected) (hF1 : ProjectionClique G)
    (hF2 : TriangleCondition G) {S : Finset V} {R : ℕ} {H : Finset V}
    (hH : ∀ x, x ∈ H ↔ ∀ s ∈ S, G.dist s x ≤ R) {o : V} (ho : o ∈ H) :
    ∀ x ∈ H, ∀ c, G.Adj x c → G.dist o c + 1 = G.dist o x → c ∈ H := by
  intro x hx c hxc hc
  have ho' := (hH o).mp ho
  have hx' := (hH x).mp hx
  exact (hH c).mpr fun s hs =>
    dist_le_of_geodesicPredecessor hconn hF1 hF2 s o _ x c R rfl hxc hc (ho' s hs) (hx' s hs)

/-- Every vertex of `H` at positive distance from `o` has a parent, when `H` contains the
geodesic predecessors of its points. -/
theorem exists_isBFSParent (hconn : G.Connected) {o : V} {H : Finset V}
    (hlow : ∀ x ∈ H, ∀ c, G.Adj x c → G.dist o c + 1 = G.dist o x → c ∈ H)
    (ρ : V → ℕ) {x : V} (hx : x ∈ H) (hpos : 0 < G.dist o x) :
    ∃ f, IsBFSParent G o H ρ x f := by
  classical
  obtain ⟨c, hxc, hc⟩ := exists_adj_predecessor hconn o hpos
  have hne : (H.filter fun c => G.Adj x c ∧ G.dist o c + 1 = G.dist o x).Nonempty :=
    ⟨c, Finset.mem_filter.mpr ⟨hlow x hx c hxc hc, hxc, hc⟩⟩
  obtain ⟨f, hf, hmin⟩ := Finset.exists_min_image _ ρ hne
  obtain ⟨hfH, hxf, hfo⟩ := Finset.mem_filter.mp hf
  exact ⟨f, hfH, hxf, hfo, fun c' hc' hxc' hc'o =>
    hmin c' (Finset.mem_filter.mpr ⟨hc', hxc', hc'o⟩)⟩

/-- Parents only see ranks one level down, so two rankings that agree up to level `k` have
the same parents up to level `k + 1`. -/
theorem isBFSParent_of_agree {o : V} {H : Finset V} {ρ₁ ρ₂ : V → ℕ} {k : ℕ}
    (hagree : ∀ y ∈ H, G.dist o y ≤ k → ρ₁ y = ρ₂ y) {x f : V} (hx : G.dist o x ≤ k + 1)
    (hf : IsBFSParent G o H ρ₁ x f) : IsBFSParent G o H ρ₂ x f := by
  obtain ⟨hfH, hxf, hfo, hmin⟩ := hf
  refine ⟨hfH, hxf, hfo, fun c hc hxc hco => ?_⟩
  rw [← hagree f hfH (by omega), ← hagree c hc (by omega)]
  exact hmin c hc hxc hco

theorem natMulAdd_lt {a b p q M : ℕ} (hab : a < b) (hp : p < M) : a * M + p < b * M + q := by
  have h1 : (a + 1) * M ≤ b * M := Nat.mul_le_mul_right M (show a + 1 ≤ b by omega)
  have h2 : (a + 1) * M = a * M + M := by rw [Nat.add_mul, Nat.one_mul]
  omega

theorem natMulAdd_inj {a b p q M : ℕ} (hp : p < M) (hq : q < M) (h : a * M + p = b * M + q) :
    a = b ∧ p = q := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have := natMulAdd_lt (q := q) hab hp
    omega
  · subst hab
    exact ⟨rfl, by omega⟩
  · have := natMulAdd_lt (q := p) hab hq
    omega

/-- **Breadth-first rankings exist.**  Induction on the level `k`.  Level `k + 1` is ranked
after all earlier levels, first by the rank of a parent and then by a fixed injective index. -/
theorem exists_isBFSRank (hconn : G.Connected) {o : V} {H : Finset V}
    (hlow : ∀ x ∈ H, ∀ c, G.Adj x c → G.dist o c + 1 = G.dist o x → c ∈ H) (k : ℕ) :
    ∃ ρ : V → ℕ, IsBFSRank G o H k ρ := by
  classical
  obtain ⟨M, e, he, heinj⟩ : ∃ M : ℕ, ∃ e : V → ℕ, (∀ x ∈ H, e x < M) ∧
      ∀ x ∈ H, ∀ y ∈ H, e x = e y → x = y := by
    refine ⟨Fintype.card H,
      fun x => if hx : x ∈ H then ((Fintype.equivFin H ⟨x, hx⟩ : Fin (Fintype.card H)) : ℕ)
        else 0, fun x hx => ?_, fun x hx y hy hxy => ?_⟩
    · simp only [dif_pos hx]
      exact (Fintype.equivFin H ⟨x, hx⟩).isLt
    · simp only [dif_pos hx, dif_pos hy] at hxy
      exact congrArg Subtype.val ((Fintype.equivFin H).injective (Fin.ext hxy))
  induction k with
  | zero =>
    refine ⟨fun _ => 0, ?_⟩
    intro x _ y _ hxk hyk
    refine ⟨fun _ => ?_, fun _ => by omega, fun _ h => by simp at h⟩
    have hox : o = x := hconn.dist_eq_zero_iff.mp (by omega)
    have hoy : o = y := hconn.dist_eq_zero_iff.mp (by omega)
    rw [← hox, ← hoy]
  | succ k ih =>
    obtain ⟨ρ, hρ⟩ := ih
    have hpar : ∀ x, ∃ f, x ∈ H → 0 < G.dist o x → IsBFSParent G o H ρ x f := by
      intro x
      by_cases hx : x ∈ H
      · by_cases hpos : 0 < G.dist o x
        · obtain ⟨f, hf⟩ := exists_isBFSParent hconn hlow ρ hx hpos
          exact ⟨f, fun _ _ => hf⟩
        · exact ⟨x, fun _ h => absurd h hpos⟩
      · exact ⟨x, fun h _ => absurd h hx⟩
    choose fa hfa using hpar
    obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ y ∈ H, ρ y < B :=
      ⟨H.sup ρ + 1, fun y hy => by
        have := Finset.le_sup (f := ρ) hy
        omega⟩
    obtain ⟨ρ', hlo, hhi⟩ : ∃ ρ' : V → ℕ, (∀ y, G.dist o y ≤ k → ρ' y = ρ y) ∧
        (∀ y, ¬ G.dist o y ≤ k → ρ' y = B + ρ (fa y) * M + e y) :=
      ⟨fun y => if G.dist o y ≤ k then ρ y else B + ρ (fa y) * M + e y,
        fun y hy => if_pos hy, fun y hy => if_neg hy⟩
    refine ⟨ρ', ?_⟩
    intro x hx y hy hxk hyk
    have hagree : ∀ z ∈ H, G.dist o z ≤ k → ρ' z = ρ z := fun z _ hz => hlo z hz
    refine ⟨fun h => ?_, fun h => ?_, fun hxy h fx fy hfx hfy => ?_⟩
    · -- injectivity
      by_cases hxk' : G.dist o x ≤ k <;> by_cases hyk' : G.dist o y ≤ k
      · rw [hlo x hxk', hlo y hyk'] at h
        exact (hρ x hx y hy hxk' hyk').1 h
      · rw [hlo x hxk', hhi y hyk'] at h
        have := hB x hx
        exfalso
        omega
      · rw [hhi x hxk', hlo y hyk'] at h
        have := hB y hy
        exfalso
        omega
      · rw [hhi x hxk', hhi y hyk'] at h
        have h' : ρ (fa x) * M + e x = ρ (fa y) * M + e y := by omega
        exact heinj x hx y hy (natMulAdd_inj (he x hx) (he y hy) h').2
    · -- increasing in the level
      by_cases hxk' : G.dist o x ≤ k <;> by_cases hyk' : G.dist o y ≤ k
      · rw [hlo x hxk', hlo y hyk']
        exact (hρ x hx y hy hxk' hyk').2.1 h
      · rw [hlo x hxk', hhi y hyk']
        have := hB x hx
        omega
      · omega
      · omega
    · -- ordered by the parents on each level
      have hfx' := isBFSParent_of_agree hagree hxk hfx
      have hfy' := isBFSParent_of_agree hagree hyk hfy
      have hfx₀ := hfx'
      have hfy₀ := hfy'
      obtain ⟨hfxH, hxfx, hfxo, hfxmin⟩ := hfx₀
      obtain ⟨hfyH, hyfy, hfyo, -⟩ := hfy₀
      rw [hlo fx (by omega), hlo fy (by omega)]
      by_cases hxk' : G.dist o x ≤ k
      · have hyk' : G.dist o y ≤ k := by omega
        rw [hlo x hxk', hlo y hyk'] at h
        exact (hρ x hx y hy hxk' hyk').2.2 hxy h fx fy hfx' hfy'
      · have hyk' : ¬ G.dist o y ≤ k := by omega
        rw [hhi x hxk', hhi y hyk'] at h
        have hfa_le : ρ (fa x) ≤ ρ (fa y) := by
          by_contra hlt
          have := natMulAdd_lt (q := e x) (by omega : ρ (fa y) < ρ (fa x)) (he y hy)
          omega
        obtain ⟨hfaxH, hxfax, hfaxo, -⟩ := hfa x hx (by omega)
        obtain ⟨-, -, -, hfaymin⟩ := hfa y hy (by omega)
        have h1 := hfxmin (fa x) hfaxH hxfax hfaxo
        have h2 := hfaymin fy hfyH hyfy hfyo
        omega

/-- **Chepoi's lemma.**  The parent of `u` is adjacent to every neighbour of `u` on the same
level ranked before `u`.  The proof is by induction on the level.  Let `w` be a counterexample.
Its parent `f(w)` differs from `f(u)` and is not adjacent to `u` or to `f(u)`.  The triangle
condition gives a common neighbour `c` of `u` and `w` one level down.  The induction hypothesis
at `c` makes `f(c)` adjacent to `f(u)` and `f(w)`, so `u w f(w) f(c) f(u)` is an induced
five-cycle. -/
theorem adj_parent_of_same_level (hconn : G.Connected) (hF1 : ProjectionClique G)
    (hF2 : TriangleCondition G) (hC4 : NoInducedFourCycle G) (hC5 : NoInducedFiveCycle G)
    {o : V} {H : Finset V}
    (hlow : ∀ x ∈ H, ∀ c, G.Adj x c → G.dist o c + 1 = G.dist o x → c ∈ H)
    {K : ℕ} {ρ : V → ℕ} (hρ : IsBFSRank G o H K ρ) (hK : ∀ x ∈ H, G.dist o x ≤ K) :
    ∀ (n : ℕ) (u w fu : V), G.dist o u = n → u ∈ H → w ∈ H → IsBFSParent G o H ρ u fu →
      G.Adj u w → G.dist o w = n → ρ w < ρ u → G.Adj fu w := by
  intro n
  induction n with
  | zero =>
    intro u w fu hun _ _ hfu _ _ _
    obtain ⟨-, -, hfuo, -⟩ := hfu
    exfalso
    omega
  | succ n ih =>
    intro u w fu hun hu hw hfu huw hwn hwu
    by_contra hnot
    have hfu₀ := hfu
    obtain ⟨hfuH, hufu, hfuo, hfumin⟩ := hfu₀
    obtain ⟨fw, hfw⟩ := exists_isBFSParent hconn hlow ρ hw (by omega)
    have hfw₀ := hfw
    obtain ⟨hfwH, hwfw, hfwo, hfwmin⟩ := hfw₀
    have hinj : ∀ a ∈ H, ∀ b ∈ H, ρ a = ρ b → a = b := fun a ha b hb h =>
      (hρ a ha b hb (hK a ha) (hK b hb)).1 h
    -- the parent of `w` is ranked no later than the parent of `u`
    have hfwfu : ρ fw ≤ ρ fu :=
      (hρ w hw u hu (hK w hw) (hK u hu)).2.2 (by omega) hwu fw fu hfw hfu
    have hne : fw ≠ fu := fun h => by
      rw [h] at hwfw
      exact hnot hwfw.symm
    have hnufw : ¬ G.Adj u fw := fun h => by
      have h1 := hfumin fw hfwH h (by omega)
      exact hne (hinj fu hfuH fw hfwH (by omega)).symm
    have hufw : u ≠ fw := fun h => by
      have := congrArg (G.dist o) h
      omega
    have hfuw : fu ≠ w := fun h => by
      have := congrArg (G.dist o) h
      omega
    -- no induced four-cycle `u f(u) f(w) w`
    have hnfufw : ¬ G.Adj fu fw := fun h => by
      rcases hC4 u fu fw w hufu h hwfw.symm huw.symm hufw hfuw with h' | h'
      · exact hnufw h'
      · exact hnot h'
    -- a common neighbour `c` of `u` and `w` one level down
    obtain ⟨c, huc, hwc, hco⟩ := hF2 o u w huw (by omega) (by omega)
    have hcH : c ∈ H := hlow u hu c huc hco
    have hcfu : c ≠ fu := fun h => by
      rw [h] at hwc
      exact hnot hwc.symm
    have hcfw : c ≠ fw := fun h => by
      rw [h] at huc
      exact hnufw huc
    have hρfuc : ρ fu < ρ c := by
      have h1 := hfumin c hcH huc hco
      have h2 : ρ fu ≠ ρ c := fun h => hcfu (hinj fu hfuH c hcH h).symm
      omega
    have hρfwc : ρ fw < ρ c := by
      have h1 := hfwmin c hcH hwc (by omega)
      have h2 : ρ fw ≠ ρ c := fun h => hcfw (hinj fw hfwH c hcH h).symm
      omega
    have hfuc : G.Adj fu c := hF1 o u fu c hufu huc hfuo hco hcfu.symm
    have hfwc : G.Adj fw c := hF1 o w fw c hwfw hwc hfwo (by omega) hcfw.symm
    -- on level one both parents would be `o`
    have hnpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · exfalso
        apply hne
        have h1 : o = fw := hconn.dist_eq_zero_iff.mp (by omega)
        have h2 : o = fu := hconn.dist_eq_zero_iff.mp (by omega)
        rw [← h1, ← h2]
      · exact h0
    obtain ⟨fc, hfc⟩ := exists_isBFSParent hconn hlow ρ hcH (by omega)
    have hfc₀ := hfc
    obtain ⟨-, -, hfco, -⟩ := hfc₀
    have hfcfu : G.Adj fc fu := ih c fu fc (by omega) hcH hfuH hfc hfuc.symm (by omega) hρfuc
    have hfcfw : G.Adj fc fw := ih c fw fc (by omega) hcH hfwH hfc hfwc.symm (by omega) hρfwc
    have hufc : u ≠ fc := fun h => by
      have := congrArg (G.dist o) h
      omega
    have hwfc : w ≠ fc := fun h => by
      have := congrArg (G.dist o) h
      omega
    -- no induced five-cycle `u w f(w) f(c) f(u)`
    rcases hC5 u w fw fc fu huw hwfw hfcfw.symm hfcfu hufu.symm hufw hufc hwfc hfuw.symm hne
      with h | h | h | h | h
    · exact hnufw h
    · have := adjDist_le_succ hconn o h
      omega
    · have := adjDist_le_succ hconn o h
      omega
    · exact hnot h.symm
    · exact hnfufw h.symm

/-- **The parent dominates.**  Among the vertices ranked no later than `u`, every vertex equal
or adjacent to `u` is equal or adjacent to the parent of `u`. -/
theorem dominated_by_parent (hconn : G.Connected) (hF1 : ProjectionClique G)
    (hF2 : TriangleCondition G) (hC4 : NoInducedFourCycle G) (hC5 : NoInducedFiveCycle G)
    {o : V} {H : Finset V}
    (hlow : ∀ x ∈ H, ∀ c, G.Adj x c → G.dist o c + 1 = G.dist o x → c ∈ H)
    {K : ℕ} {ρ : V → ℕ} (hρ : IsBFSRank G o H K ρ) (hK : ∀ x ∈ H, G.dist o x ≤ K)
    {u fu : V} (hu : u ∈ H) (hfu : IsBFSParent G o H ρ u fu) :
    ∀ x ∈ H, ρ x ≤ ρ u → (x = u ∨ G.Adj u x) → x = fu ∨ G.Adj fu x := by
  intro x hx hxu hux
  have hfu₀ := hfu
  obtain ⟨-, hufu, hfuo, -⟩ := hfu₀
  rcases hux with rfl | hux
  · exact Or.inr hufu.symm
  · have hρlt : ρ x < ρ u := by
      have h1 : ρ x ≠ ρ u := fun h => hux.ne' ((hρ x hx u hu (hK x hx) (hK u hu)).1 h)
      omega
    have hlev : ¬ G.dist o u < G.dist o x := fun h => by
      have := (hρ u hu x hx (hK u hu) (hK x hx)).2.1 h
      omega
    have h1 := adjDist_le_succ hconn o hux
    rcases Nat.lt_or_ge (G.dist o x) (G.dist o u) with hlt | hge
    · by_cases hxfu : x = fu
      · exact Or.inl hxfu
      · exact Or.inr (hF1 o u fu x hufu hux hfuo (by omega) (Ne.symm hxfu))
    · exact Or.inr (adj_parent_of_same_level hconn hF1 hF2 hC4 hC5 hlow hρ hK _ u x fu rfl hu
        hx hfu hux (by omega) hρlt)

end BFS

open BFS in
/-- **Intersections of balls admit a dismantling order.**  Let `G` be a connected graph with
projection cliques, the triangle condition, and no induced four- or five-cycles.  Let `H` be a
nonempty finite intersection of balls `B_R(s)`, `s ∈ S`.  Then `H` has an injective ranking `ρ`
in which every vertex `u` that is not ranked first is dominated by an earlier vertex `w`.  Every
`x ∈ H` ranked no later than `u` and equal or adjacent to `u` is equal or adjacent to `w`.  The
ranking is breadth-first from a point of `H`, and `w` is the parent of `u`. -/
theorem exists_dismantlingRank_of_forall_dist_le {V : Type*} {G : SimpleGraph V}
    (hconn : G.Connected) (hF1 : ProjectionClique G) (hF2 : TriangleCondition G)
    (hC4 : NoInducedFourCycle G) (hC5 : NoInducedFiveCycle G)
    {S : Finset V} {R : ℕ} {H : Finset V} (hH : ∀ x, x ∈ H ↔ ∀ s ∈ S, G.dist s x ≤ R)
    (hne : H.Nonempty) :
    ∃ ρ : V → ℕ, (∀ x ∈ H, ∀ y ∈ H, ρ x = ρ y → x = y) ∧
      ∀ u ∈ H, (∃ y ∈ H, ρ y < ρ u) →
        ∃ w ∈ H, ρ w < ρ u ∧ ∀ x ∈ H, ρ x ≤ ρ u → (x = u ∨ G.Adj u x) → x = w ∨ G.Adj w x := by
  obtain ⟨o, ho⟩ := hne
  have hlow := lowerClosed_of_forall_dist_le hconn hF1 hF2 hH ho
  obtain ⟨ρ, hρ⟩ := exists_isBFSRank hconn hlow (H.sup (G.dist o))
  have hK : ∀ x ∈ H, G.dist o x ≤ H.sup (G.dist o) := fun x hx => Finset.le_sup (f := G.dist o) hx
  refine ⟨ρ, fun x hx y hy h => (hρ x hx y hy (hK x hx) (hK y hy)).1 h, fun u hu hlt => ?_⟩
  obtain ⟨y, hy, hyu⟩ := hlt
  have hpos : 0 < G.dist o u := by
    rcases Nat.eq_zero_or_pos (G.dist o u) with h0 | h0
    · exfalso
      have huo : o = u := hconn.dist_eq_zero_iff.mp h0
      by_cases hyo : y = o
      · rw [hyo, huo] at hyu
        omega
      · have hoy : 0 < G.dist o y := hconn.pos_dist_of_ne (Ne.symm hyo)
        have := (hρ u hu y hy (hK u hu) (hK y hy)).2.1 (by omega)
        omega
    · exact h0
  obtain ⟨fu, hfu⟩ := exists_isBFSParent hconn hlow ρ hu hpos
  have hfu₀ := hfu
  obtain ⟨hfuH, -, hfuo, -⟩ := hfu₀
  exact ⟨fu, hfuH, (hρ fu hfuH u hu (hK fu hfuH) (hK u hu)).2.1 (by omega),
    dominated_by_parent hconn hF1 hF2 hC4 hC5 hlow hρ hK hu hfu⟩

/-- **Finite intersections of balls are dismantlable.**  Let `G` be a connected graph with
projection cliques, the triangle condition, and no induced four- or five-cycles.  Then every
nonempty finite intersection `H` of balls `B_R(s)`, `s ∈ S`, is `Dismantlable`.  Delete the
vertices of `H` in decreasing breadth-first rank; each is dominated by its parent among the
vertices that remain. -/
theorem dismantlable_of_forall_dist_le {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hconn : G.Connected) (hF1 : ProjectionClique G) (hF2 : TriangleCondition G)
    (hC4 : NoInducedFourCycle G) (hC5 : NoInducedFiveCycle G)
    {S : Finset V} {R : ℕ} {H : Finset V} (hH : ∀ x, x ∈ H ↔ ∀ s ∈ S, G.dist s x ≤ R)
    (hne : H.Nonempty) : Dismantlable G H := by
  obtain ⟨ρ, hinj, hdom⟩ := exists_dismantlingRank_of_forall_dist_le hconn hF1 hF2 hC4 hC5 hH hne
  -- every nonempty initial segment of the ranking is dismantlable
  have key : ∀ (n : ℕ) (P : Finset V), P.card = n + 1 → P ⊆ H →
      (∀ x ∈ P, ∀ y ∈ H, ρ y ≤ ρ x → y ∈ P) → Dismantlable G P := by
    intro n
    induction n with
    | zero =>
      intro P hP _ _
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (by omega : P.card = 1)
      exact Dismantlable.single v
    | succ n ih =>
      intro P hP hPH hPlow
      obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image P ρ (Finset.card_pos.mp (by omega))
      obtain ⟨y, hy, hyu⟩ := Finset.exists_mem_ne (s := P) (by omega) u
      have hρyu : ρ y < ρ u := by
        have h1 := hmax y hy
        have h2 : ρ y ≠ ρ u := fun h => hyu (hinj y (hPH hy) u (hPH hu) h)
        omega
      obtain ⟨w, hwH, hρwu, hdomw⟩ := hdom u (hPH hu) ⟨y, hPH hy, hρyu⟩
      have hwu : w ≠ u := fun h => by
        rw [h] at hρwu
        omega
      refine Dismantlable.erase hu (hPlow u hu w hwH hρwu.le) hwu
        (fun x hx hxu => hdomw x (hPH hx) (hmax x hx) hxu) ?_
      refine ih (P.erase u) ?_ (Finset.Subset.trans (Finset.erase_subset u P) hPH) ?_
      · rw [Finset.card_erase_of_mem hu]
        omega
      · intro x hx z hz hzx
        have hxP := Finset.mem_of_mem_erase hx
        have hxu : x ≠ u := Finset.ne_of_mem_erase hx
        refine Finset.mem_erase.mpr ⟨fun hzu => ?_, hPlow x hxP z hz hzx⟩
        have h1 := hmax x hxP
        have h2 : ρ x ≠ ρ u := fun h => hxu (hinj x (hPH hxP) u (hPH hu) h)
        rw [hzu] at hzx
        omega
  obtain ⟨n, hn⟩ : ∃ n, H.card = n + 1 :=
    ⟨H.card - 1, by
      have := Finset.card_pos.mpr hne
      omega⟩
  exact key n H hn (Finset.Subset.refl H) fun _ _ _ hy _ => hy

end Systolic
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.Systolic.exists_dismantlingRank_of_forall_dist_le
#audit_axioms GroupApproximation.Systolic.dismantlable_of_forall_dist_le
