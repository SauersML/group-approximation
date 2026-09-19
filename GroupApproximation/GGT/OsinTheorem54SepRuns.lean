import GroupApproximation.GGT.OsinTheorem54SepComponents

/-!
# Components exist: every `lam`-letter lies in a maximal run

`OsinComponents.IsComp` is a maximality condition --- `[i,k)` is a run of
`lam`-letters, the letter before `i` is not one, and the letter at `k` is not one
--- and `IsCompStart`, `Connected`, `IsIsolated` and `IsolatedComponentBound` are
all stated in terms of it.  Nothing in the repository ever *inhabits* it.  Until
something does, every counting argument over components is counting a set that
has not been shown to be nonempty, and `IsolatedComponentBound` could be
vacuously true.

`exists_isComp_of_isCompOf` closes that: **every `lam`-letter of a word lies in a
component**, so components exist exactly where the geometry expects them.  The
proof is two maximality searches and nothing else:

* `exists_runStart` --- walk back from `j` while the letters are `lam`-letters.
  Induction on `j`: either the letter before `j` is a `lam`-letter, and the run
  starting at `j - 1`'s start works, or it is not, and `j` starts its own run.
* `exists_runEnd` --- walk forward from `j` to the first letter that is not a
  `lam`-letter, or to the end of the word.  Induction on a budget `d` with
  `w.length ≤ j + d`, which is what makes the forward search terminate.

`exists_isCompStart_connected` is the form the isolation arguments use: a
`lam`-letter is `Connected` to the start of its own component, by
`span_mem_fam`.  That is the step in Osin's Lemma 4.9 and in the isolated
component bound which says that a `lam`-letter met at a vertex of the coset
`a₋H_λ` belongs to a component connected to `a` --- so an *isolated* `a` is met
by none.

## What this does not do

It does not bound anything.  The isolated-component bound
(Osin's Lemma 4.2, Dahmani--Guirardel--Osin's Proposition 4.13) says
`d̂_λ(a₋,a₊) ≤ Cn` for an isolated component of an `n`-gon, and the constant
depends on `n` and the quasi-geodesic constants but **not on the perimeter**.
What the combinatorics above will give, once the complementary path is written
down, is the perimeter bound: the rest of the polygon is a path from `a₊` to `a₋`
which reads no `lam`-letter at a vertex of `a₋H_λ` --- precisely because `a` is
isolated --- so `d̂_λ(a₋,a₊) ≤ perimeter − |a|`.  Replacing the perimeter by `Cn`
is the hyperbolic content, and it needs stability of quasi-geodesics in
`Γ(G, X ⊔ ℋ)`, which this repository does not have.  So the polygon layer is not
closed here; it is made non-vacuous, and the gap is isolated to one inequality.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Walking back to the start of a run -/

omit [Group G] in
/-- **Backward maximality.**  From a `lam`-letter at `j`, there is an `i ≤ j`
with every letter of `[i,j]` a `lam`-letter and the letter before `i` not one. -/
theorem exists_runStart (lam : Λ) (w : List (RelLetter G Λ)) :
    ∀ (j : ℕ) (hj : j < w.length), (w[j]'hj).IsCompOf lam →
      ∃ i : ℕ, i ≤ j ∧
        (∀ m : ℕ, i ≤ m → m ≤ j → ∀ hm : m < w.length,
          (w[m]'hm).IsCompOf lam) ∧
        (∀ m : ℕ, i = m + 1 → ∀ hm : m < w.length,
          ¬ (w[m]'hm).IsCompOf lam) := by
  intro j
  induction j with
  | zero =>
      intro hj hc
      refine ⟨0, le_refl 0, ?_, ?_⟩
      · intro m _ hm2 _
        have hm0 : m = 0 := by omega
        subst hm0
        exact hc
      · intro m hmeq _
        exact absurd hmeq (by omega)
  | succ j ih =>
      intro hj hc
      have hjlt : j < w.length := by omega
      by_cases hprev : (w[j]'hjlt).IsCompOf lam
      · obtain ⟨i, hij, hrange, hpred⟩ := ih hjlt hprev
        refine ⟨i, by omega, ?_, hpred⟩
        intro m hm1 hm2 hm
        rcases Nat.lt_or_ge m (j + 1) with hlt | hge
        · exact hrange m hm1 (by omega) hm
        · have hmj : m = j + 1 := by omega
          subst hmj
          exact hc
      · refine ⟨j + 1, le_refl _, ?_, ?_⟩
        · intro m hm1 hm2 _
          have hmj : m = j + 1 := by omega
          subst hmj
          exact hc
        · intro m hmeq _
          have hmj : m = j := by omega
          subst hmj
          exact hprev

/-! ## Walking forward to the end of a run -/

omit [Group G] in
/-- **Forward maximality.**  From a position `j`, there is a first `k > j` at
which the word stops being a run of `lam`-letters, or the word ends.

The budget `d` with `w.length ≤ j + d` is what makes the forward search
terminate; it is discharged at `d = w.length`. -/
theorem exists_runEnd (lam : Λ) (w : List (RelLetter G Λ)) :
    ∀ (d j : ℕ), w.length ≤ j + d → j < w.length →
      ∃ k : ℕ, j < k ∧ k ≤ w.length ∧
        (∀ m : ℕ, j < m → m < k → ∀ hm : m < w.length,
          (w[m]'hm).IsCompOf lam) ∧
        (∀ hk : k < w.length, ¬ (w[k]'hk).IsCompOf lam) := by
  intro d
  induction d with
  | zero =>
      intro j hd hj
      exact absurd hj (by omega)
  | succ d ih =>
      intro j hd hj
      rcases Nat.lt_or_ge (j + 1) w.length with hlt | hge
      · by_cases hnext : (w[j + 1]'hlt).IsCompOf lam
        · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih (j + 1) (by omega) hlt
          refine ⟨k, by omega, hk2, ?_, hk4⟩
          intro m hm1 hm2 hm
          rcases Nat.lt_or_ge m (j + 2) with hm3 | hm3
          · have hmj : m = j + 1 := by omega
            subst hmj
            exact hnext
          · exact hk3 m (by omega) hm2 hm
        · refine ⟨j + 1, by omega, by omega, ?_, ?_⟩
          · intro m hm1 hm2 _
            exact absurd hm2 (by omega)
          · intro _
            exact hnext
      · refine ⟨w.length, hj, le_refl _, ?_, ?_⟩
        · intro m hm1 hm2 _
          exact absurd hm2 (by omega)
        · intro hk
          exact absurd hk (by omega)

/-! ## Components exist -/

omit [Group G] in
/-- **Every `lam`-letter lies in a component.**

So `IsComp`, `IsCompStart` and `IsIsolated` are not vacuous, and a counting
argument over the components of a word is counting the runs of `lam`-letters it
actually has. -/
theorem exists_isComp_of_isCompOf (lam : Λ) (w : List (RelLetter G Λ)) (j : ℕ)
    (hj : j < w.length) (hc : (w[j]'hj).IsCompOf lam) :
    ∃ i k : ℕ, i ≤ j ∧ j < k ∧ IsComp lam w i k := by
  obtain ⟨i, hij, hrange, hpred⟩ := exists_runStart lam w j hj hc
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ :=
    exists_runEnd lam w w.length j (by omega) hj
  refine ⟨i, k, hij, hk1, ⟨by omega, hk2, ?_, hpred, hk4⟩⟩
  intro m hm1 hm2 hm
  rcases Nat.lt_or_ge j m with hlt | hge
  · exact hk3 m hlt hm2 hm
  · exact hrange m hm1 hge hm

/-- **A `lam`-letter is connected to the start of its component.**

This is the step the isolation arguments turn on: a `lam`-letter met at a vertex
of the coset `a₋H_lam` lies in a component whose start is `Connected` to `a`, so
an *isolated* `a` is met by no such letter, and the rest of the polygon is a path
avoiding `Γ_{H_lam}`. -/
theorem exists_isCompStart_connected (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a) (j : ℕ)
    (hj : j < w.length) (hc : (w[j]'hj).IsCompOf lam) :
    ∃ i : ℕ, IsCompStart lam w i ∧ Connected D.fam lam v w i j := by
  obtain ⟨i, k, hij, hjk, hcomp⟩ := exists_isComp_of_isCompOf lam w j hj hc
  refine ⟨i, ⟨k, hcomp⟩, ?_⟩
  obtain ⟨-, -, hrange, -, -⟩ := hcomp
  exact span_mem_fam D lam v hlet j (by omega) i hij
    (fun m hm1 hm2 hm => hrange m hm1 (by omega) hm)

end OsinComponents
end GGT
end GroupApproximation
