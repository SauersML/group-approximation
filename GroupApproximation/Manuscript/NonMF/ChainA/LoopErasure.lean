import GroupApproximation.Dynamics.TransientClassSaturation
import GroupApproximation.Dynamics.TransientCompactWanderingCover
import GroupApproximation.Meta.AxiomGuard

/-!
# Wandering covers and erasing loops (tex 1489–1497)

`non_mf_groups_exist.tex`, proof of `lem:transient-matrices`:

* tex 1489–1491: "A compact subset $C\subset U$ has a finite cover by wandering clopen sets, say
  $m$ of them, so each orbit meets $C$ in at most $m$ points."
* tex 1496–1497: "Erasing loops shortens any path between related points to at most $m-1$
  steps."

Here `U = X \ Y` with `Y = CR(T)` the chain recurrent set.

Proof route.

* The cover is `exists_wandering_clopen_cover_of_isCompact`. For the orbit bound, send each orbit
  point of `C` to the index of a cover set containing it. Two orbit points `T^d x` and `T^d' x` in
  one wandering set satisfy `d = d'` (`eq_zero_of_isWandering`), so the map is injective.
* A path of `n` steps is `p : ℕ → ℤ` with `p 0 = 0`. Each step `p (i+1) - p i` is a partial-shift
  exponent or its inverse, and every visited point `T^{p i} x` lies in `C`. If two positions
  `i < j` agree, the loop between them is cut out (`eraseLoop`), which is a shorter path with the
  same endpoint visiting a subset of the old points. By strong induction we reach a path whose
  positions are pairwise distinct. The orbit bound then gives at most `m` positions, so at most
  `m - 1` steps.
-/

namespace GroupApproximation.Manuscript.NonMF.ChainA

open GroupApproximation.ChainCore

section Paths

variable {X : Type*} [TopologicalSpace X]

/-- A path of `n` steps from `x`: positions `p 0 = 0, …, p n`. Each step is an exponent from
`stepExponents E` (a partial shift or its inverse), and every visited point `T^{p i} x` lies in
`C`. -/
def IsShiftPath (T : X ≃ₜ X) (C : Set X) (E : Finset ℤ) (x : X) (n : ℕ) (p : ℕ → ℤ) : Prop :=
  p 0 = 0 ∧ (∀ i < n, p (i + 1) - p i ∈ stepExponents E) ∧ ∀ i ≤ n, (T ^ (p i)) x ∈ C

/-- Cut out the loop between positions `i < j`: keep `p 0, …, p i`, then continue with
`p (j+1), …`. -/
def eraseLoop (p : ℕ → ℤ) (i j k : ℕ) : ℤ :=
  if k ≤ i then p k else p (k + (j - i))

variable {T : X ≃ₜ X} {C : Set X} {E : Finset ℤ} {m : ℕ}

/-- **Each orbit meets `C` in at most `m` points** (tex 1491), when `C` is covered by `m`
wandering sets. -/
theorem card_orbit_inter_le_of_wanderingCover {W : Fin m → Set X}
    (hWw : ∀ i, GroupApproximation.Dynamics.IsWandering T.toEquiv (W i)) (hCW : C ⊆ ⋃ i, W i)
    (x : X) (S : Finset X) (hS : ∀ y ∈ S, y ∈ C ∧ ∃ d : ℤ, (T ^ d) x = y) : S.card ≤ m := by
  have hsel : ∀ y ∈ S, ∃ i : ℕ, ∃ hi : i < m, y ∈ W ⟨i, hi⟩ := fun y hy => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hCW (hS y hy).1)
    exact ⟨i, i.2, hi⟩
  choose! ι hι using hsel
  have hinj : Set.InjOn ι (S : Set X) := by
    intro y hy y' hy' heq
    obtain ⟨hlt, h1⟩ := hι y hy
    obtain ⟨hlt', h2⟩ := hι y' hy'
    have hfin : (⟨ι y, hlt⟩ : Fin m) = ⟨ι y', hlt'⟩ := Fin.ext heq
    rw [hfin] at h1
    obtain ⟨d, hd⟩ := (hS y hy).2
    obtain ⟨d', hd'⟩ := (hS y' hy').2
    have e : (T ^ (d - d')) y' = y := by
      rw [← hd', GroupApproximation.Dynamics.zpow_apply_zpow_apply, sub_add_cancel, hd]
    have hmem : (T ^ (d - d')) y' ∈ W ⟨ι y', hlt'⟩ := by
      rw [e]
      exact h1
    have h0 := GroupApproximation.Dynamics.eq_zero_of_isWandering T (hWw _) h2 hmem
    rw [← hd, ← hd', sub_eq_zero.1 h0]
  calc S.card ≤ (Finset.range m).card :=
        Finset.card_le_card_of_injOn ι
          (fun y hy => Finset.mem_coe.2 (Finset.mem_range.2 (hι y hy).1)) hinj
    _ = m := Finset.card_range m

/-- The positions of a path lie in the class generated in as many steps. -/
theorem mem_reachableExponents_of_isShiftPath {x : X} {n : ℕ} {p : ℕ → ℤ}
    (hp : IsShiftPath T C E x n p) : ∀ i ≤ n, p i ∈ reachableExponents T C E i x := by
  intro i
  induction i with
  | zero =>
    intro hi
    have h0 : (T ^ (p 0)) x ∈ C := hp.2.2 0 hi
    rw [hp.1, zpow_zero, Homeomorph.one_apply] at h0
    exact mem_reachableExponents_zero.2 ⟨hp.1, h0⟩
  | succ i ih =>
    intro hi
    exact mem_reachableExponents_succ.2
      ⟨Or.inr ⟨p i, ih (by omega), p (i + 1) - p i, hp.2.1 i (by omega), by ring⟩,
        hp.2.2 (i + 1) hi⟩

/-- Every exponent of the class generated in `r` steps is the endpoint of a path of at most `r`
steps. -/
theorem exists_isShiftPath_of_mem_reachableExponents {x : X} :
    ∀ (r : ℕ) {d : ℤ}, d ∈ reachableExponents T C E r x →
      ∃ (n : ℕ) (p : ℕ → ℤ), n ≤ r ∧ IsShiftPath T C E x n p ∧ p n = d := by
  intro r
  induction r with
  | zero =>
    intro d hd
    obtain ⟨rfl, hx⟩ := mem_reachableExponents_zero.1 hd
    refine ⟨0, fun _ => 0, le_rfl, ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i),
      fun i _ => ?_⟩, rfl⟩
    show (T ^ (0 : ℤ)) x ∈ C
    rwa [zpow_zero, Homeomorph.one_apply]
  | succ r ih =>
    intro d hd
    obtain ⟨hcase, hdC⟩ := mem_reachableExponents_succ.1 hd
    rcases hcase with hd' | ⟨a, ha, e, he, hae⟩
    · obtain ⟨n, p, hn, hp, hpn⟩ := ih hd'
      exact ⟨n, p, by omega, hp, hpn⟩
    · obtain ⟨n, p, hn, hp, hpn⟩ := ih ha
      refine ⟨n + 1, fun i => if i ≤ n then p i else d, by omega, ⟨?_, ?_, ?_⟩, ?_⟩
      · show (if 0 ≤ n then p 0 else d) = 0
        rw [if_pos (Nat.zero_le n)]
        exact hp.1
      · intro i hi
        show (if i + 1 ≤ n then p (i + 1) else d) - (if i ≤ n then p i else d) ∈
          stepExponents E
        by_cases hin : i + 1 ≤ n
        · rw [if_pos hin, if_pos (by omega : i ≤ n)]
          exact hp.2.1 i hin
        · have hi' : i = n := by omega
          rw [if_neg hin, if_pos (by omega : i ≤ n), hi', hpn, show d - a = e by omega]
          exact he
      · intro i _
        show (T ^ (if i ≤ n then p i else d)) x ∈ C
        by_cases hin : i ≤ n
        · rw [if_pos hin]
          exact hp.2.2 i hin
        · rw [if_neg hin]
          exact hdC
      · show (if n + 1 ≤ n then p (n + 1) else d) = d
        rw [if_neg (by omega)]

/-- Erasing a loop gives a path again, with `j - i` fewer steps. -/
theorem isShiftPath_eraseLoop {x : X} {n : ℕ} {p : ℕ → ℤ} (hp : IsShiftPath T C E x n p)
    {i j : ℕ} (hij : i < j) (hjn : j ≤ n) (hpij : p i = p j) :
    IsShiftPath T C E x (n - (j - i)) (eraseLoop p i j) := by
  refine ⟨?_, ?_, ?_⟩
  · show (if 0 ≤ i then p 0 else p (0 + (j - i))) = 0
    rw [if_pos (Nat.zero_le i)]
    exact hp.1
  · intro k hk
    show (if k + 1 ≤ i then p (k + 1) else p (k + 1 + (j - i))) -
      (if k ≤ i then p k else p (k + (j - i))) ∈ stepExponents E
    by_cases hk1 : k + 1 ≤ i
    · rw [if_pos hk1, if_pos (by omega : k ≤ i)]
      exact hp.2.1 k (by omega)
    · by_cases hki : k = i
      · rw [if_neg hk1, if_pos (by omega : k ≤ i), hki, hpij,
          show i + 1 + (j - i) = j + 1 by omega]
        exact hp.2.1 j (by omega)
      · rw [if_neg hk1, if_neg (by omega : ¬ k ≤ i),
          show k + 1 + (j - i) = k + (j - i) + 1 by omega]
        exact hp.2.1 (k + (j - i)) (by omega)
  · intro k hk
    show (T ^ (if k ≤ i then p k else p (k + (j - i)))) x ∈ C
    by_cases hki : k ≤ i
    · rw [if_pos hki]
      exact hp.2.2 k (by omega)
    · rw [if_neg hki]
      exact hp.2.2 _ (by omega)

/-- Erasing a loop keeps the endpoint. -/
theorem eraseLoop_last {n : ℕ} {p : ℕ → ℤ} {i j : ℕ} (hij : i < j) (hjn : j ≤ n)
    (hpij : p i = p j) : eraseLoop p i j (n - (j - i)) = p n := by
  show (if n - (j - i) ≤ i then p (n - (j - i)) else p (n - (j - i) + (j - i))) = p n
  by_cases h : n - (j - i) ≤ i
  · rw [if_pos h, show n - (j - i) = i by omega, hpij, show j = n by omega]
  · rw [if_neg h, show n - (j - i) + (j - i) = n by omega]

/-- Erasing a loop only visits old positions. -/
theorem eraseLoop_mem {n : ℕ} {p : ℕ → ℤ} {i j : ℕ} (hjn : j ≤ n) (k : ℕ)
    (hk : k ≤ n - (j - i)) : ∃ l ≤ n, eraseLoop p i j k = p l := by
  by_cases hki : k ≤ i
  · refine ⟨k, by omega, ?_⟩
    show (if k ≤ i then p k else p (k + (j - i))) = p k
    rw [if_pos hki]
  · refine ⟨k + (j - i), by omega, ?_⟩
    show (if k ≤ i then p k else p (k + (j - i))) = p (k + (j - i))
    rw [if_neg hki]

/-- A path with pairwise distinct positions has at most `m - 1` steps. -/
theorem le_of_isShiftPath_injective (hm : ExponentBound T C m) {x : X} {n : ℕ} {p : ℕ → ℤ}
    (hp : IsShiftPath T C E x n p) (hinj : ∀ k ≤ n, ∀ l ≤ n, p k = p l → k = l) :
    n ≤ m - 1 := by
  have hcard : ((Finset.range (n + 1)).image p).card = n + 1 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro k hk l hl hkl
    have hk' := Finset.mem_range.1 (Finset.mem_coe.1 hk)
    have hl' := Finset.mem_range.1 (Finset.mem_coe.1 hl)
    exact hinj k (by omega) l (by omega) hkl
  have hle := hm x ((Finset.range (n + 1)).image p) fun d hd => by
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hd
    have hk' := Finset.mem_range.1 hk
    exact hp.2.2 k (by omega)
  omega

/-- **Erasing loops** (tex 1496–1497), path form. Under the orbit bound, every path is replaced
by one of at most `m - 1` steps with the same endpoint. The new path visits only old positions,
and its positions are pairwise distinct. -/
theorem exists_short_path (hm : ExponentBound T C m) {x : X} :
    ∀ (n : ℕ) (p : ℕ → ℤ), IsShiftPath T C E x n p →
      ∃ (n' : ℕ) (p' : ℕ → ℤ), n' ≤ m - 1 ∧ IsShiftPath T C E x n' p' ∧ p' n' = p n ∧
        (∀ k ≤ n', ∃ l ≤ n, p' k = p l) ∧ ∀ k ≤ n', ∀ l ≤ n', p' k = p' l → k = l := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hp
  by_cases hinj : ∀ k ≤ n, ∀ l ≤ n, p k = p l → k = l
  · exact ⟨n, p, le_of_isShiftPath_injective hm hp hinj, hp, rfl, fun k hk => ⟨k, hk, rfl⟩,
      hinj⟩
  · push Not at hinj
    obtain ⟨a, ha, b, hb, hab, hne⟩ := hinj
    by_cases hlt : a < b
    · obtain ⟨n', p', hn', hp', hlast, hsub, hinj'⟩ :=
        ih (n - (b - a)) (by omega) (eraseLoop p a b) (isShiftPath_eraseLoop hp hlt hb hab)
      refine ⟨n', p', hn', hp', ?_, fun k hk => ?_, hinj'⟩
      · rw [hlast, eraseLoop_last hlt hb hab]
      · obtain ⟨c, hc, hkc⟩ := hsub k hk
        obtain ⟨l, hl, hcl⟩ := eraseLoop_mem (p := p) (i := a) hb c hc
        exact ⟨l, hl, hkc.trans hcl⟩
    · have hlt' : b < a := by omega
      obtain ⟨n', p', hn', hp', hlast, hsub, hinj'⟩ :=
        ih (n - (a - b)) (by omega) (eraseLoop p b a)
          (isShiftPath_eraseLoop hp hlt' ha hab.symm)
      refine ⟨n', p', hn', hp', ?_, fun k hk => ?_, hinj'⟩
      · rw [hlast, eraseLoop_last hlt' ha hab.symm]
      · obtain ⟨c, hc, hkc⟩ := hsub k hk
        obtain ⟨l, hl, hcl⟩ := eraseLoop_mem (p := p) (i := b) ha c hc
        exact ⟨l, hl, hkc.trans hcl⟩

end Paths

/-- **tex 1489–1491.** "A compact subset $C\subset U$ has a finite cover by wandering clopen
sets, say $m$ of them, so each orbit meets $C$ in at most $m$ points." Here `U` is the
complement of the chain recurrent set `Y = CR(T)` of a homeomorphism of a compact totally
disconnected metric space. -/
theorem manuscriptSentence_compactWanderingClopenCover {X : Type} [MetricSpace X]
    [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X) (C : Set X) (hC : IsCompact C)
    (hCU : C ⊆ (GroupApproximation.Dynamics.chainRecurrentSet ⇑T)ᶜ) :
    ∃ (m : ℕ) (W : Fin m → Set X), (∀ i, IsClopen (W i)) ∧
      (∀ i, GroupApproximation.Dynamics.IsWandering T.toEquiv (W i)) ∧ C ⊆ ⋃ i, W i ∧
      ∀ (x : X) (S : Finset X), (∀ y ∈ S, y ∈ C ∧ ∃ d : ℤ, (T ^ d) x = y) → S.card ≤ m := by
  obtain ⟨m, W, hWc, hWw, hCW, -⟩ :=
    GroupApproximation.ClopenCrossedProduct.exists_wandering_clopen_cover_of_isCompact T hC
      (Set.disjoint_left.2 fun _ hx hxY => hCU hx hxY)
  exact ⟨m, W, hWc, hWw, hCW, card_orbit_inter_le_of_wanderingCover hWw hCW⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainA.manuscriptSentence_compactWanderingClopenCover

/-- **tex 1496–1497.** "Erasing loops shortens any path between related points to at most
$m-1$ steps." `C` is covered by `m` wandering sets. A path from `x` to `T^{p n} x` whose steps
are partial shifts or their inverses, and whose points all lie in `C`, is replaced by a path of
at most `m - 1` steps with the same endpoint. The new path visits only points of the old one,
and it has no loops. -/
theorem manuscriptSentence_erasingLoopsShortensPaths {X : Type*} [TopologicalSpace X]
    (T : X ≃ₜ X) (C : Set X) (E : Finset ℤ) {m : ℕ} (W : Fin m → Set X)
    (hWw : ∀ i, GroupApproximation.Dynamics.IsWandering T.toEquiv (W i)) (hCW : C ⊆ ⋃ i, W i)
    (x : X) (n : ℕ) (p : ℕ → ℤ) (hp : IsShiftPath T C E x n p) :
    ∃ (n' : ℕ) (p' : ℕ → ℤ), n' ≤ m - 1 ∧ IsShiftPath T C E x n' p' ∧ p' n' = p n ∧
      (∀ k ≤ n', ∃ l ≤ n, p' k = p l) ∧ ∀ k ≤ n', ∀ l ≤ n', p' k = p' l → k = l :=
  exists_short_path (exponentBound_of_wanderingCover hWw hCW) n p hp

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainA.manuscriptSentence_erasingLoopsShortensPaths

end GroupApproximation.Manuscript.NonMF.ChainA
