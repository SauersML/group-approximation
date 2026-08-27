import GroupApproximation.GGT.BassSerreHNNTree
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The Bass--Serre graph of an HNN extension is a tree

`GGT/BassSerreHNNTree.lean` proves that the graph is connected and that every
vertex other than the base one has a *unique* neighbour of smaller syllable
length (`exists_parent`).  Acyclicity is the only thing separating that from
Bass--Serre's theorem, and this module supplies it.

## The argument

Write `ℓ v` for the distance from the base vertex `Δ`, which is the syllable
length of any name of `v`.  The two inputs are:

* `level_adj` --- `ℓ` changes by exactly one across every edge;
* `eq_of_adj_of_level_succ` --- the neighbour with the smaller `ℓ` is unique.

From them, `level_of_up_walk`: a walk that *starts* by increasing `ℓ` never
comes back down.  At each vertex the walk has just entered from below, so the
vertex it came from is the unique lower neighbour; a trail cannot use that edge
again, so the next step must go up.  Iterating, `ℓ` at the far end is `ℓ` at
the near end plus the length of the walk.

Path uniqueness follows by induction on `ℓ v + ℓ w`.  Assume `ℓ w ≤ ℓ v`.  If
`v = w` both paths are trivial.  Otherwise `ℓ v > 0`, and neither path can
begin by going up --- `level_of_up_walk` would force `ℓ w > ℓ v` --- so both
begin at the unique lower neighbour of `v`, and the induction hypothesis
identifies what remains.  When `ℓ v < ℓ w`, run the same argument on the
reversed paths.  `SimpleGraph.isAcyclic_of_path_unique` converts this to
acyclicity.

`tree_isTree` is the statement `GGT/HyperbolicTreeMetric.lean` consumes: it
turns the vertex set into a `0`-hyperbolic metric space.
-/

namespace GroupApproximation
namespace GGT
namespace BassSerreHNN

open GroupApproximation.HNNBritton

universe u

variable {G : Type u} [Group G] {A B : Subgroup G}

/-! ## The level of a vertex -/

/-- The distance from the base vertex. -/
noncomputable def level (φ : A ≃* B) (v : Vertex φ) : ℕ :=
  (tree φ).dist (vmk φ 1) v

@[simp] theorem level_vmk (φ : A ≃* B) (x : HNNExtension G A B φ) :
    level φ (vmk φ x) = tLen φ x :=
  dist_vmk_one φ x

theorem level_eq_zero_iff (φ : A ≃* B) (v : Vertex φ) :
    level φ v = 0 ↔ v = vmk φ 1 := by
  constructor
  · intro h
    have h1 : (tree φ).dist (vmk φ 1) v = 0 := h
    exact (((tree_connected φ).dist_eq_zero_iff).1 h1).symm
  · rintro rfl
    show (tree φ).dist (vmk φ 1) (vmk φ 1) = 0
    simp [SimpleGraph.dist_self]

/-- The level changes by exactly one across every edge. -/
theorem level_adj (φ : A ≃* B) {v w : Vertex φ} (h : (tree φ).Adj v w) :
    level φ w = level φ v + 1 ∨ level φ w + 1 = level φ v := by
  obtain ⟨x, rfl⟩ := vmk_surjective φ v
  obtain ⟨y, rfl⟩ := vmk_surjective φ w
  simpa using tLen_adj φ h

/-- **The parent vertex, at the level of vertices.** -/
theorem exists_parent_vertex (φ : A ≃* B) {v : Vertex φ}
    (hv : level φ v ≠ 0) :
    ∃ p : Vertex φ, level φ p + 1 = level φ v ∧ (tree φ).Adj v p ∧
      ∀ w : Vertex φ, (tree φ).Adj v w → level φ w + 1 = level φ v → w = p := by
  obtain ⟨x, rfl⟩ := vmk_surjective φ v
  rw [level_vmk] at hv
  obtain ⟨p, h1, h2, h3⟩ := exists_parent φ hv
  refine ⟨vmk φ p, ?_, h2, ?_⟩
  · simpa using h1
  · intro w hadj hwlen
    obtain ⟨z, rfl⟩ := vmk_surjective φ w
    rw [level_vmk, level_vmk] at hwlen
    exact h3 z hadj hwlen

/-- **The lower neighbour is unique.** -/
theorem eq_of_adj_of_level_succ (φ : A ≃* B) {v w w' : Vertex φ}
    (h1 : (tree φ).Adj v w) (h2 : (tree φ).Adj v w')
    (hw : level φ w + 1 = level φ v) (hw' : level φ w' + 1 = level φ v) :
    w = w' := by
  have hv : level φ v ≠ 0 := by omega
  obtain ⟨p, -, -, hu⟩ := exists_parent_vertex φ hv
  rw [hu w h1 hw, hu w' h2 hw']

/-! ## A walk that starts upwards never comes back -/

/-- **No return.**  A trail entering `b` from the unique lower neighbour `u`
must keep climbing: at every later vertex the edge back down is the one just
used, and a trail may not repeat it. -/
theorem level_of_up_walk (φ : A ≃* B) {b c : Vertex φ}
    (q : (tree φ).Walk b c) :
    ∀ (u : Vertex φ) (hub : (tree φ).Adj u b),
      level φ b = level φ u + 1 →
      (SimpleGraph.Walk.cons hub q).IsTrail →
      level φ c = level φ b + q.length := by
  induction q with
  | nil =>
      intro _ _ _ _
      simp
  | @cons a d c' hbd q' ih =>
      intro u hub hlev htrail
      rw [SimpleGraph.Walk.isTrail_cons] at htrail
      obtain ⟨htrail2, hnotmem⟩ := htrail
      have hswap : (s(u, a) : Sym2 (Vertex φ)) = s(a, u) := Sym2.eq_swap
      have hne : d ≠ u := by
        intro hdu
        refine hnotmem ?_
        rw [SimpleGraph.Walk.edges_cons, hdu, hswap]
        exact List.mem_cons_self
      have hd : level φ d = level φ a + 1 := by
        rcases level_adj φ hbd with h | h
        · exact h
        · exact absurd
            (eq_of_adj_of_level_succ φ hbd hub.symm h hlev.symm) hne
      have hIH := ih a hbd hd htrail2
      rw [SimpleGraph.Walk.length_cons]
      omega

/-! ## Unique paths -/

/-- The inductive step of path uniqueness, at the endpoint of larger level. -/
theorem peel (φ : A ≃* B) (n : ℕ)
    (ih : ∀ (v w : Vertex φ), level φ v + level φ w ≤ n →
      ∀ (p q : (tree φ).Walk v w), p.IsPath → q.IsPath → p = q)
    (v w : Vertex φ) (hle : level φ w ≤ level φ v)
    (hn : level φ v + level φ w ≤ n + 1)
    (p q : (tree φ).Walk v w) (hp : p.IsPath) (hq : q.IsPath) : p = q := by
  rcases eq_or_ne v w with rfl | hvw
  · rw [SimpleGraph.Walk.isPath_iff_nil] at hp hq
    rw [hp.eq_nil, hq.eq_nil]
  · have hvpos : level φ v ≠ 0 := by
      intro h0
      have hw0 : level φ w = 0 := by omega
      have h1 : v = vmk φ 1 := (level_eq_zero_iff φ v).1 h0
      have h2 : w = vmk φ 1 := (level_eq_zero_iff φ w).1 hw0
      exact hvw (h1.trans h2.symm)
    cases p with
    | nil => exact absurd rfl hvw
    | @cons _ bp _ hbp p' =>
        cases q with
        | nil => exact absurd rfl hvw
        | @cons _ bq _ hbq q' =>
            have hbplev : level φ bp + 1 = level φ v := by
              rcases level_adj φ hbp with h | h
              · exfalso
                have hup := level_of_up_walk φ p' v hbp h hp.isTrail
                omega
              · exact h
            have hbqlev : level φ bq + 1 = level φ v := by
              rcases level_adj φ hbq with h | h
              · exfalso
                have hup := level_of_up_walk φ q' v hbq h hq.isTrail
                omega
              · exact h
            have hbeq : bp = bq :=
              eq_of_adj_of_level_succ φ hbp hbq hbplev hbqlev
            subst hbeq
            have hpp' : p'.IsPath :=
              ((SimpleGraph.Walk.cons_isPath_iff hbp p').1 hp).1
            have hqq' : q'.IsPath :=
              ((SimpleGraph.Walk.cons_isPath_iff hbq q').1 hq).1
            have hmeas : level φ bp + level φ w ≤ n := by omega
            exact congrArg (SimpleGraph.Walk.cons hbp)
              (ih bp w hmeas p' q' hpp' hqq')

/-- **Between two vertices there is at most one path.** -/
theorem walk_unique (φ : A ≃* B) :
    ∀ (n : ℕ) (v w : Vertex φ), level φ v + level φ w ≤ n →
      ∀ (p q : (tree φ).Walk v w), p.IsPath → q.IsPath → p = q := by
  intro n
  induction n with
  | zero =>
      intro v w hn p q hp hq
      have hv0 : level φ v = 0 := by omega
      have hw0 : level φ w = 0 := by omega
      have h1 : v = vmk φ 1 := (level_eq_zero_iff φ v).1 hv0
      have h2 : w = vmk φ 1 := (level_eq_zero_iff φ w).1 hw0
      have hvw : v = w := h1.trans h2.symm
      subst hvw
      rw [SimpleGraph.Walk.isPath_iff_nil] at hp hq
      rw [hp.eq_nil, hq.eq_nil]
  | succ n ih =>
      intro v w hn p q hp hq
      rcases le_total (level φ w) (level φ v) with hle | hle
      · exact peel φ n ih v w hle hn p q hp hq
      · have h := peel φ n ih w v hle (by omega) p.reverse q.reverse
          hp.reverse hq.reverse
        have h2 := congrArg SimpleGraph.Walk.reverse h
        rwa [SimpleGraph.Walk.reverse_reverse,
          SimpleGraph.Walk.reverse_reverse] at h2

/-- **The Bass--Serre graph is acyclic.** -/
theorem tree_isAcyclic (φ : A ≃* B) : (tree φ).IsAcyclic := by
  refine SimpleGraph.isAcyclic_of_path_unique ?_
  intro v w p q
  refine Subtype.ext ?_
  exact walk_unique φ (level φ v + level φ w) v w le_rfl p.1 q.1 p.2 q.2

/-- **Bass--Serre: the graph of an HNN splitting is a tree.** -/
theorem tree_isTree (φ : A ≃* B) : (tree φ).IsTree :=
  ⟨tree_connected φ, tree_isAcyclic φ⟩

end BassSerreHNN
end GGT
end GroupApproximation
