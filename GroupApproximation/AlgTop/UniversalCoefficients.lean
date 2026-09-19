import GroupApproximation.AlgTop.Kronecker

/-!
# The universal coefficient theorem for singular cohomology

Over a principal ideal domain the Kronecker map

```text
κ : Hⁿ(X; R) → Hom(Hₙ(X; R), R)
```

is surjective. Given a functional `f` on homology, pull it back to the cycles,
extend it over the chains — possible because the cycles are a direct summand,
which is `exists_extend_off_ker_d`, which in turn rests on the arbitrary-rank
statement "a submodule of a free module over a PID is free" that Mathlib lacks —
and observe that the extension is automatically a cocycle, because a boundary is
a cycle whose homology class is zero.

This is the half of the universal coefficient theorem that **constructs** classes,
and it is the half the counterexample programme needs: it produces a class in
`Hⁿ(Sⁿ; ℤ)` pairing to `1` against the generator of `Hₙ(Sⁿ; ℤ)`, hence a
generator and a normalised top-degree pairing.

The other half is injectivity when `Hₘ(X; R)` is projective, which upgrades this
to an isomorphism `H^{m+1}(X;R) ≅ Hom(H_{m+1}(X;R), R)`. It uses the same
splitting twice: a cocycle killing all cycles factors through the boundaries,
and the resulting functional extends first over the cycles (this is where the
projectivity of `Hₘ` enters) and then over the chains, producing an explicit
primitive.

## Main results

* `kronecker_surjective`
* `exists_cocycle_pairing` — the same statement in cocycle form.
* `kronecker_injective`
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.AlgTop

noncomputable section

variable (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable (X : TopCat.{0}) (n : ℕ)

/-- The short complex whose homology is `Hₙ(X;R)`. -/
abbrev chainSc : ShortComplex (ModuleCat.{0} R) := (chainCx R X).sc n

/-- The cycles of the singular chain complex, concretely as a kernel. -/
theorem chainSc_g : (chainSc R X n).g
    = (chainCx R X).d n ((ComplexShape.down ℕ).next n) := rfl

/-- `iCycles` factors through the concrete kernel description. -/
theorem iCycles_eq_subtype (z : (chainCx R X).cycles n) :
    ((chainCx R X).iCycles n).hom z
      = (((chainSc R X n).moduleCatCyclesIso.hom).hom z : (chainCx R X).X n) := by
  have h := (chainSc R X n).moduleCatCyclesIso_hom_i
  have := ConcreteCategory.congr_hom h z
  simpa using this.symm

/-- The inverse of the cycles isomorphism is determined by its image in the
chain group. -/
theorem cyclesIso_inv_val (y : LinearMap.ker (chainSc R X n).g.hom) :
    ((chainCx R X).iCycles n).hom (((chainSc R X n).moduleCatCyclesIso.inv).hom y)
      = (y : (chainCx R X).X n) := by
  have h := (chainSc R X n).moduleCatCyclesIso_inv_iCycles
  have := ConcreteCategory.congr_hom h y
  simpa using this

/-- **Surjectivity of the Kronecker map.** -/
theorem kronecker_surjective (f : homologyOf R X n →ₗ[R] R) :
    ∃ a : cohomology R X n, (kronecker R X n).hom a = f := by
  classical
  -- the functional pulled back to the cycles, then to the concrete kernel
  set g : (chainCx R X).cycles n →ₗ[R] R :=
    f.comp ((chainCx R X).homologyπ n).hom with hg
  set g' : LinearMap.ker (chainSc R X n).g.hom →ₗ[R] R :=
    g.comp ((chainSc R X n).moduleCatCyclesIso.inv).hom with hg'
  obtain ⟨F, hF⟩ :=
    exists_extend_off_ker_d R X n ((ComplexShape.down ℕ).next n) g'
  -- the extension is a cocycle
  have hmem : ∀ c : (chainCx R X).X (n + 1),
      ((chainCx R X).d (n + 1) n).hom c ∈ LinearMap.ker (chainSc R X n).g.hom := by
    intro c
    rw [LinearMap.mem_ker, chainSc_g, ← ModuleCat.comp_apply, (chainCx R X).d_comp_d]
    rfl
  have hboundary : ∀ c : (chainCx R X).X (n + 1),
      ((chainSc R X n).moduleCatCyclesIso.inv).hom
          ⟨((chainCx R X).d (n + 1) n).hom c, hmem c⟩
        = ((chainCx R X).toCycles (n + 1) n).hom c := by
    intro c
    apply (ModuleCat.mono_iff_injective ((chainCx R X).iCycles n)).1 inferInstance
    rw [cyclesIso_inv_val, ← ModuleCat.comp_apply, (chainCx R X).toCycles_i]
  have hφ : IsCocycle R X n (ModuleCat.ofHom F) := by
    rw [isCocycle_iff]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    show F (((chainCx R X).d (n + 1) n).hom c) = 0
    rw [show (((chainCx R X).d (n + 1) n).hom c)
        = ((⟨((chainCx R X).d (n + 1) n).hom c, hmem c⟩ :
            LinearMap.ker (chainSc R X n).g.hom) : (chainCx R X).X n) from rfl,
      hF, hg', LinearMap.comp_apply, hboundary, hg, LinearMap.comp_apply,
      ← ModuleCat.comp_apply, (chainCx R X).toCycles_comp_homologyπ]
    simp
  -- the class of the extension has the prescribed Kronecker image
  refine ⟨cocycleClass R X n (ModuleCat.ofHom F) hφ, ?_⟩
  rw [kronecker_cocycleClass]
  have hcomp : (chainCx R X).homologyπ n ≫ kronOfCocycle R X n (ModuleCat.ofHom F) hφ
      = (chainCx R X).homologyπ n ≫ ModuleCat.ofHom f := by
    rw [homologyπ_kronOfCocycle]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    show F (((chainCx R X).iCycles n).hom z) = f (((chainCx R X).homologyπ n).hom z)
    rw [iCycles_eq_subtype, hF, hg', LinearMap.comp_apply]
    have hz : ((chainSc R X n).moduleCatCyclesIso.inv).hom
        (((chainSc R X n).moduleCatCyclesIso.hom).hom z) = z := by
      rw [← ModuleCat.comp_apply, (chainSc R X n).moduleCatCyclesIso.hom_inv_id]
      rfl
    rw [hz, hg, LinearMap.comp_apply]
  have := (cancel_epi ((chainCx R X).homologyπ n)).mp hcomp
  exact congrArg ModuleCat.Hom.hom this

/-! ## 2. Injectivity when the homology one degree down is projective -/

/-- In the chain-complex shape the next index of `m + 1` is `m`. -/
theorem down_next (m : ℕ) : (ComplexShape.down ℕ).next (m + 1) = m :=
  (ComplexShape.down ℕ).next_eq (by simp [ComplexShape.down_Rel])

theorem chainSc_f : (chainSc R X n).f
    = (chainCx R X).d ((ComplexShape.down ℕ).prev n) n := rfl

/-- The cycles at `m + 1` are the kernel of `∂ₘ₊₁`. -/
theorem ker_chainSc_g_succ (m : ℕ) :
    LinearMap.ker (chainSc R X (m + 1)).g.hom
      = LinearMap.ker ((chainCx R X).d (m + 1) m).hom := by
  rw [chainSc_g, down_next]

/-- The boundaries inside the cycles, as the range of `moduleCatToCycles`. -/
theorem range_moduleCatToCycles (m : ℕ) :
    LinearMap.range (chainSc R X m).moduleCatToCycles
      = Submodule.comap (LinearMap.ker (chainSc R X m).g.hom).subtype
          (LinearMap.range ((chainCx R X).d (m + 1) m).hom) := by
  show LinearMap.range (LinearMap.codRestrict _ (chainSc R X m).f.hom _) = _
  rw [LinearMap.range_codRestrict]
  congr 1
  rw [chainSc_f, down_prev]

/-- `Zₘ / Bₘ` is projective as soon as `Hₘ` is. -/
theorem projective_quot_comap (m : ℕ) (hproj : Module.Projective R (homologyOf R X m)) :
    Module.Projective R
      (↥(LinearMap.ker (chainSc R X m).g.hom) ⧸
        Submodule.comap (LinearMap.ker (chainSc R X m).g.hom).subtype
          (LinearMap.range ((chainCx R X).d (m + 1) m).hom)) := by
  haveI := hproj
  haveI : Module.Projective R (↥(LinearMap.ker (chainSc R X m).g.hom) ⧸
      LinearMap.range (chainSc R X m).moduleCatToCycles) :=
    Module.Projective.of_equiv' ((chainSc R X m).moduleCatHomologyIso).toLinearEquiv
  exact Module.Projective.of_equiv'
    (Submodule.quotEquivOfEq _ _ (range_moduleCatToCycles R X m))

/-- **Injectivity of the Kronecker map** when `Hₘ(X; R)` is projective. -/
theorem kronecker_injective (m : ℕ) (hproj : Module.Projective R (homologyOf R X m))
    (a : cohomology R X (m + 1)) (ha : (kronecker R X (m + 1)).hom a = 0) : a = 0 := by
  classical
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective R X (m + 1) a
  -- (1) the cocycle vanishes on every cycle
  have h0 : kronOfCocycle R X (m + 1) φ hφ = 0 := by
    apply ModuleCat.hom_ext
    rw [← kronecker_cocycleClass R X (m + 1) φ hφ, ha]
    rfl
  have hvan : (chainCx R X).iCycles (m + 1) ≫ φ = 0 := by
    rw [← homologyπ_kronOfCocycle R X (m + 1) φ hφ, h0, comp_zero]
  have hvanish : ∀ x : (chainCx R X).X (m + 1),
      x ∈ LinearMap.ker ((chainCx R X).d (m + 1) m).hom → φ.hom x = 0 := by
    intro x hx
    have hx' : x ∈ LinearMap.ker (chainSc R X (m + 1)).g.hom := by
      rw [ker_chainSc_g_succ]; exact hx
    have h := ConcreteCategory.congr_hom hvan
      (((chainSc R X (m + 1)).moduleCatCyclesIso.inv).hom ⟨x, hx'⟩)
    rw [ModuleCat.comp_apply, cyclesIso_inv_val] at h
    simpa using h
  -- (2) it therefore factors through the boundaries
  have hle : LinearMap.ker ((chainCx R X).d (m + 1) m).hom ≤ LinearMap.ker φ.hom :=
    fun x hx => LinearMap.mem_ker.mpr (hvanish x hx)
  set gbar : ↥(LinearMap.range ((chainCx R X).d (m + 1) m).hom) →ₗ[R] R :=
    (Submodule.liftQ (LinearMap.ker ((chainCx R X).d (m + 1) m).hom) φ.hom hle).comp
      (LinearMap.quotKerEquivRange ((chainCx R X).d (m + 1) m).hom).symm.toLinearMap
    with hgbar
  have hgbar_apply : ∀ c : (chainCx R X).X (m + 1),
      gbar ⟨((chainCx R X).d (m + 1) m).hom c,
        LinearMap.mem_range_self ((chainCx R X).d (m + 1) m).hom c⟩ = φ.hom c := by
    intro c
    rw [hgbar, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.liftQ_apply]
  -- (3) extend it over the cycles, then over the chains
  haveI := projective_quot_comap R X m hproj
  obtain ⟨G, hG⟩ := PID.exists_extend_of_projective_quotient
    (Submodule.comap (LinearMap.ker (chainSc R X m).g.hom).subtype
      (LinearMap.range ((chainCx R X).d (m + 1) m).hom))
    (gbar.comp (((LinearMap.ker (chainSc R X m).g.hom).subtype.comp
      (Submodule.comap (LinearMap.ker (chainSc R X m).g.hom).subtype
        (LinearMap.range ((chainCx R X).d (m + 1) m).hom)).subtype).codRestrict
      (LinearMap.range ((chainCx R X).d (m + 1) m).hom) (fun y => y.2)))
  obtain ⟨Psi, hPsi⟩ :=
    exists_extend_off_ker_d R X m ((ComplexShape.down ℕ).next m) G
  -- (4) the extension is a primitive for the cocycle
  have hprim : cochainCoboundary R X m (ModuleCat.ofHom Psi) = φ := by
    rw [cochainCoboundary_eq_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    have hz : ((chainCx R X).d (m + 1) m).hom c ∈ LinearMap.ker (chainSc R X m).g.hom := by
      rw [chainSc_g, LinearMap.mem_ker, ← ModuleCat.comp_apply, (chainCx R X).d_comp_d]
      rfl
    have hb : (⟨((chainCx R X).d (m + 1) m).hom c, hz⟩ :
        ↥(LinearMap.ker (chainSc R X m).g.hom))
        ∈ Submodule.comap (LinearMap.ker (chainSc R X m).g.hom).subtype
            (LinearMap.range ((chainCx R X).d (m + 1) m).hom) :=
      LinearMap.mem_range_self ((chainCx R X).d (m + 1) m).hom c
    show Psi (((chainCx R X).d (m + 1) m).hom c) = φ.hom c
    rw [show (((chainCx R X).d (m + 1) m).hom c)
        = ((⟨((chainCx R X).d (m + 1) m).hom c, hz⟩ :
            ↥(LinearMap.ker (chainSc R X m).g.hom)) :
              (chainCx R X).X m) from rfl,
      hPsi, hG ⟨_, hb⟩, LinearMap.comp_apply]
    exact hgbar_apply c
  exact cocycleClass_eq_zero_of_eq R X (m + 1) hprim.symm hφ
    (by rw [hprim]; exact hφ)
    (cocycleClass_coboundary_zero R X m (ModuleCat.ofHom Psi) (by rw [hprim]; exact hφ))

/-- The same statement in cocycle form: every functional on homology is
represented by a cocycle. -/
theorem exists_cocycle_pairing (f : homologyOf R X n →ₗ[R] R) :
    ∃ (φ : singularCochainGroup R X n) (hφ : IsCocycle R X n φ),
      (kronOfCocycle R X n φ hφ).hom = f := by
  obtain ⟨a, ha⟩ := kronecker_surjective R X n f
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective R X n a
  exact ⟨φ, hφ, by rw [← kronecker_cocycleClass, ha]⟩

end

end GroupApproximation.AlgTop
