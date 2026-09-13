import GroupApproximation.Pestov91.Subshift

/-!
# Cylinders and minimality of the Toeplitz subshift

Every open set of `X` contains a coordinate cylinder. By uniform recurrence, finitely many
translates of any nonempty open set cover `X`. Hence every forward orbit is dense and every closed
shift-invariant set is empty or everything.
-/

namespace GroupApproximation.Pestov91

/-- The cylinder of points of `X` agreeing with `y` on `s`. -/
def cyl (s : Finset ℤ) (y : X) : Set X := {z | ∀ i ∈ s, z.1 i = y.1 i}

theorem mem_cyl_self (s : Finset ℤ) (y : X) : y ∈ cyl s y := fun _ _ => rfl

theorem isOpen_cyl (s : Finset ℤ) (y : X) : IsOpen (cyl s y) := by
  have hc : Continuous fun (z : X) (i : s) => z.1 i :=
    continuous_pi fun i => (continuous_apply (i : ℤ)).comp continuous_subtype_val
  have := (isOpen_discrete {v : s → Bool | v = fun i : s => y.1 i}).preimage hc
  convert this using 1
  ext z
  simp only [cyl, Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · intro h
    funext i
    exact h i i.2
  · intro h i hi
    exact congrFun h ⟨i, hi⟩

theorem exists_cyl_subset {U : Set X} (hU : IsOpen U) {y : X} (hy : y ∈ U) :
    ∃ s : Finset ℤ, cyl s y ⊆ U := by
  obtain ⟨V, hV, rfl⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hU
  obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.mp hV y.1 hy
  refine ⟨I, fun z hz => ?_⟩
  show z.1 ∈ V
  apply hIu
  simp only [Set.mem_pi, Finset.mem_coe]
  intro i hi
  rw [hz i hi]
  exact (hu i hi).2

/-- Finitely many translates of a nonempty open set cover `X`. -/
theorem exists_nat_cover {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ N : ℕ, ∀ x : X, ∃ r : ℕ, r < N ∧ shiftBy r x ∈ U := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨s, hs⟩ := exists_cyl_subset hU hy
  obtain ⟨R, hR⟩ : ∃ R : ℕ, ∀ i ∈ s, i.natAbs ≤ R :=
    ⟨s.sup Int.natAbs, fun i hi => Finset.le_sup (f := Int.natAbs) hi⟩
  obtain ⟨b, hb⟩ := mem_window y (-R) (2 * R + 1)
  obtain ⟨K, hK⟩ := exists_return b (2 * R + 1)
  refine ⟨2 ^ K, fun x => ?_⟩
  obtain ⟨r, hr, hr'⟩ := hK x (-R)
  refine ⟨r, hr, hs ?_⟩
  show ∀ i ∈ s, (shiftBy r x).1 i = y.1 i
  intro i hi
  have hi' := hR i hi
  have hj := hr' (i + R).toNat (by omega)
  have hj' := hb (i + R).toNat (by omega)
  have e : -(R : ℤ) + ((i + R).toNat : ℕ) = i := by omega
  rw [shiftBy_apply, show (r : ℤ) + i = -(R : ℤ) + r + ((i + R).toNat : ℕ) by omega, hj]
  rw [e] at hj'
  exact hj'.symm

theorem exists_nat_shiftBy_mem (x : X) {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ r : ℕ, shiftBy r x ∈ U := by
  obtain ⟨N, hN⟩ := exists_nat_cover hU hne
  obtain ⟨r, -, hr⟩ := hN x
  exact ⟨r, hr⟩

theorem dense_range_shiftBy (x : X) : Dense (Set.range fun n : ℤ => shiftBy n x) := by
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨r, hr⟩ := exists_nat_shiftBy_mem x hU hne
  exact ⟨shiftBy r x, hr, r, rfl⟩

theorem dense_range_zpow_shiftHomeo (x : X) :
    Dense (Set.range fun j : ℤ => (shiftHomeo ^ j) x) := by
  simpa only [← shiftBy_eq_zpow] using dense_range_shiftBy x

/-- Minimality: a closed forward-invariant set is empty or everything. -/
theorem eq_empty_or_univ_of_isClosed {S : Set X} (hS : IsClosed S)
    (hinv : ∀ y ∈ S, shiftBy 1 y ∈ S) : S = ∅ ∨ S = Set.univ := by
  rcases S.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · exact Or.inl h
  refine Or.inr (Set.eq_univ_of_forall fun z => ?_)
  by_contra hz
  obtain ⟨r, hr⟩ := exists_nat_shiftBy_mem x hS.isOpen_compl ⟨z, hz⟩
  have hmem : ∀ n : ℕ, shiftBy n x ∈ S := by
    intro n
    induction n with
    | zero => simpa only [Nat.cast_zero, shiftBy_zero] using hx
    | succ n ih =>
      rw [Nat.cast_succ, add_comm, shiftBy_add]
      exact hinv _ ih
  exact (Set.mem_compl_iff S _).mp hr (hmem r)

end GroupApproximation.Pestov91
