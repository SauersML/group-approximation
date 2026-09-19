section NilAt

variable (R : Type) [CommRing R] (k N : ℕ)

/-- The kernel of `ev₀ : K₂(N, R[t_0..t_{k-1}]) → K₂(N, R)` is finitely generated.  It is stated for
a general commutative ring, so that its `ℤ[1/m]` instance below is a plain substitution.  Elaborating
`ev₀` directly at `ℤ[1/m]` meets two different semiring structures on `Localization.Away`: one from
its commutative-semiring instance and one from its ring instance. -/
def K2NilFGAt : Prop :=
  Group.FG (K2Map (I := Fin N) (MvPolynomial.constantCoeff : MvPolynomial (Fin k) R →+* R)).ker

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.K2NilFGAt

/-- Every element of `K₂(N, R[t_0..t_{k-1}])` killed by `ev₀` is trivial. -/
def K2NilPosAt : Prop :=
  ∀ u : K2 (Fin N) (MvPolynomial (Fin k) R),
    K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) R →+* R) u = 1 → u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.K2NilPosAt

variable {R k N}

/-- Vanishing of the kernel of `ev₀` gives its finite generation. -/
theorem k2NilFGAt_of_nilPosAt (h : K2NilPosAt R k N) : K2NilFGAt R k N := by
  have hker : (K2Map (I := Fin N)
      (MvPolynomial.constantCoeff : MvPolynomial (Fin k) R →+* R)).ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).mpr ((injective_iff_map_eq_one _).mpr h)
  unfold K2NilFGAt
  rw [Group.fg_iff_subgroup_fg, hker]
  exact Subgroup.FG.bot

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.k2NilFGAt_of_nilPosAt

/-- `K₂(N, R)` is a quotient of `K₂(N, R[∅])` along `ev₀`, split by the constants. -/
theorem k2_fg_of_fg_mvPolynomial_fin_zero
    (h : Group.FG (K2 (Fin N) (MvPolynomial (Fin 0) R))) : Group.FG (K2 (Fin N) R) :=
  Group.fg_of_surjective (hG := h)
    (f := K2Map (I := Fin N) (MvPolynomial.constantCoeff : MvPolynomial (Fin 0) R →+* R))
    fun v ↦ ⟨K2Map (I := Fin N) (MvPolynomial.C : R →+* MvPolynomial (Fin 0) R) v,
      ElemFP.K2Map_constantCoeff_K2Map_C v⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.k2_fg_of_fg_mvPolynomial_fin_zero

end NilAt

/-- **Gap, base part.**  `K₂(N, ℤ[1/m])` is finitely generated for `N ≥ 5`. -/
def CharZeroK2BaseFGStatement : Prop :=
  ∀ m N : ℕ, 5 ≤ N → Group.FG (K2 (Fin N) (Localization.Away (m : ℤ)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.CharZeroK2BaseFGStatement

/-- **Gap, nil part.**  For `k ≥ 1`, `N ≥ k + 4` and `N ≥ 5`, the kernel of
`ev₀ : K₂(N, ℤ[1/m][t_0..t_{k-1}]) → K₂(N, ℤ[1/m])` is finitely generated. -/
def CharZeroK2NilFGPosStatement : Prop :=
  ∀ m k N : ℕ, 0 < k → k + 4 ≤ N → 5 ≤ N → K2NilFGAt (Localization.Away (m : ℤ)) k N

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.CharZeroK2NilFGPosStatement

/-- **The isolated gap** (lane `bh-met-28`): the base part and the nil part. -/
def CharZeroK2SplitGapStatement : Prop :=
  CharZeroK2BaseFGStatement ∧ CharZeroK2NilFGPosStatement

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.CharZeroK2SplitGapStatement

/-- **Endpoint (lane `bh-met-28`).**  The split gap implies `CharZeroStableK2FGStatement`. -/
theorem charZeroStableK2FG_of_splitGap (h : CharZeroK2SplitGapStatement) :
    CharZeroStableK2FGStatement := by
  intro m k N hkN h5N
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact k2_fg_mvPolynomial_of_isEmpty (σ := Fin 0) (R := Localization.Away (m : ℤ))
      (I := Fin N) (h.1 m N h5N)
  · exact k2_fg_of_base_of_nil (σ := Fin k) (R := Localization.Away (m : ℤ)) (I := Fin N)
      (h.1 m N h5N) (h.2 m k N hk hkN h5N)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroStableK2FG_of_splitGap

/-- The base part is logically weaker than the target: it is the case `k = 0`, transported along
the surjection `ev₀ : K₂(N, ℤ[1/m][∅]) → K₂(N, ℤ[1/m])`. -/
theorem charZeroK2BaseFG_of_stableK2FG (h : CharZeroStableK2FGStatement) :
    CharZeroK2BaseFGStatement := fun m N h5N ↦
  k2_fg_of_fg_mvPolynomial_fin_zero (R := Localization.Away (m : ℤ)) (h m 0 N (by omega) h5N)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroK2BaseFG_of_stableK2FG

/-- The vanishing form of the nil part: for `k ≥ 1`, `N ≥ k + 4`, `N ≥ 5`, an element of
`K₂(N, ℤ[1/m][t_0..t_{k-1}])` killed by `ev₀` is trivial.  It is true by injective stability and
homotopy invariance (see the module docstring).  It is not the isolated gap, only a convenient
stronger input. -/
def CharZeroK2NilPosStatement : Prop :=
  ∀ m k N : ℕ, 0 < k → k + 4 ≤ N → 5 ≤ N → K2NilPosAt (Localization.Away (m : ℤ)) k N

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.CharZeroK2NilPosStatement

/-- Vanishing of the nil part gives its finite generation. -/
theorem charZeroK2NilFGPos_of_nilPos (h : CharZeroK2NilPosStatement) :
    CharZeroK2NilFGPosStatement := fun m k N hk hkN h5N ↦
  k2NilFGAt_of_nilPosAt (h m k N hk hkN h5N)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroK2NilFGPos_of_nilPos

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
