import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVHopfH2.Chains

/-!
# Hopf formula versus `groupHomology.H2`: the tautological twisted extension (lane LVHopfH2)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735 (Hopf formula; Brown II.5 Thm 5.3).
Put `Q := C₂ ⧸ B₂` (integral 2-chains of `G` modulo boundaries), `q g h := [(g,h)] ∈ Q`, and
`R g h := q g h - q 1 1`.  Then `R` is a normalized 2-cocycle, and `X := Q × G` with
`(a,g)(b,h) = (a + b + R g h, g h)` is a central extension of `G` by `Q`.  Since `F` is free, `f`
lifts to `F → X`.  The lift kills `[F,R]` and so descends to `E = F ⧸ [F,R] → X`.

* `hopfTwQ_cocycle`, `hopfTwR_one_left`, `hopfTwR_one_right`, `hopfTwR_cocycle`.
* `HopfTwExt G` with its `Group` instance; `hopfTw_comm_of_g_eq_one`: `Q × 1` is central.
* `hopfTwBar f : HopfExt f →* HopfTwExt G`, and `hopfTwBar_g`: its `G`-coordinate is `E → G`.
-/

namespace GroupApproximation.Full.LVHopf

section TwistedExt

variable {G : Type} [Group G]

/-- `Q = C₂ ⧸ B₂`: integral inhomogeneous 2-chains modulo 2-boundaries. -/
abbrev HopfChainQuot (G : Type) [Group G] : Type :=
  (G × G →₀ ℤ) ⧸ (hopfChainD3 (G := G)).range

/-- `q g h = [(g,h)] ∈ Q`. -/
noncomputable def hopfTwQ (g h : G) : HopfChainQuot G :=
  QuotientAddGroup.mk' (hopfChainD3 (G := G)).range (Finsupp.single (g, h) 1)

theorem hopfTwQ_def (g h : G) :
    hopfTwQ g h = QuotientAddGroup.mk' (hopfChainD3 (G := G)).range (Finsupp.single (g, h) 1) :=
  rfl

/-- `q` is a 2-cocycle, since `∂₃ (g,h,k) ∈ B₂`. -/
theorem hopfTwQ_cocycle (g h k : G) :
    hopfTwQ h k + hopfTwQ g (h * k) = hopfTwQ g h + hopfTwQ (g * h) k := by
  have e : QuotientAddGroup.mk' (hopfChainD3 (G := G)).range
      (hopfChainD3 (Finsupp.single (g, h, k) 1)) = 0 := by
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    exact AddMonoidHom.mem_range.mpr ⟨Finsupp.single (g, h, k) 1, rfl⟩
  rw [hopfChainD3_single, map_sub, map_add, map_sub] at e
  have e2 : hopfTwQ h k + hopfTwQ g (h * k) - (hopfTwQ g h + hopfTwQ (g * h) k) =
      hopfTwQ h k - hopfTwQ (g * h) k + hopfTwQ g (h * k) - hopfTwQ g h := by
    abel
  exact sub_eq_zero.mp (e2.trans e)

theorem hopfTwQ_one_left_eq (g k : G) : hopfTwQ 1 k = hopfTwQ g 1 := by
  have e := hopfTwQ_cocycle g 1 k
  rw [one_mul k, mul_one g] at e
  exact add_right_cancel e

/-- The normalized cocycle `R g h = q g h - q 1 1`. -/
noncomputable def hopfTwR (g h : G) : HopfChainQuot G :=
  hopfTwQ g h - hopfTwQ 1 1

theorem hopfTwR_one_left (h : G) : hopfTwR 1 h = 0 := by
  rw [hopfTwR, hopfTwQ_one_left_eq 1 h, sub_self]

theorem hopfTwR_one_right (g : G) : hopfTwR g 1 = 0 := by
  rw [hopfTwR, ← hopfTwQ_one_left_eq g 1, sub_self]

theorem hopfTwR_cocycle (g h k : G) :
    hopfTwR h k + hopfTwR g (h * k) = hopfTwR g h + hopfTwR (g * h) k := by
  have e := hopfTwQ_cocycle g h k
  have e2 : hopfTwQ h k - hopfTwQ 1 1 + (hopfTwQ g (h * k) - hopfTwQ 1 1) -
      (hopfTwQ g h - hopfTwQ 1 1 + (hopfTwQ (g * h) k - hopfTwQ 1 1)) =
        hopfTwQ h k + hopfTwQ g (h * k) - (hopfTwQ g h + hopfTwQ (g * h) k) := by
    abel
  exact sub_eq_zero.mp (e2.trans (sub_eq_zero.mpr e))

variable (G) in
/-- The twisted extension `X = Q × G` with `(a,g)(b,h) = (a + b + R g h, g h)`. -/
@[ext]
structure HopfTwExt where
  /-- The `Q`-coordinate. -/
  a : HopfChainQuot G
  /-- The `G`-coordinate. -/
  g : G

noncomputable instance hopfTwExtMul : Mul (HopfTwExt G) :=
  ⟨fun x y => ⟨x.a + y.a + hopfTwR x.g y.g, x.g * y.g⟩⟩

instance hopfTwExtOne : One (HopfTwExt G) :=
  ⟨⟨0, 1⟩⟩

noncomputable instance hopfTwExtInv : Inv (HopfTwExt G) :=
  ⟨fun x => ⟨-x.a - hopfTwR x.g⁻¹ x.g, x.g⁻¹⟩⟩

theorem hopfTw_mul_assoc (x y z : HopfTwExt G) : x * y * z = x * (y * z) := by
  refine HopfTwExt.ext ?_ ?_
  · show x.a + y.a + hopfTwR x.g y.g + z.a + hopfTwR (x.g * y.g) z.g =
      x.a + (y.a + z.a + hopfTwR y.g z.g) + hopfTwR x.g (y.g * z.g)
    have e2 : x.a + y.a + hopfTwR x.g y.g + z.a + hopfTwR (x.g * y.g) z.g =
        x.a + y.a + z.a + (hopfTwR x.g y.g + hopfTwR (x.g * y.g) z.g) := by
      abel
    have e3 : x.a + (y.a + z.a + hopfTwR y.g z.g) + hopfTwR x.g (y.g * z.g) =
        x.a + y.a + z.a + (hopfTwR y.g z.g + hopfTwR x.g (y.g * z.g)) := by
      abel
    rw [e2, e3, hopfTwR_cocycle x.g y.g z.g]
  · show x.g * y.g * z.g = x.g * (y.g * z.g)
    exact mul_assoc x.g y.g z.g

theorem hopfTw_one_mul (x : HopfTwExt G) : 1 * x = x := by
  refine HopfTwExt.ext ?_ ?_
  · show 0 + x.a + hopfTwR 1 x.g = x.a
    rw [hopfTwR_one_left x.g, add_zero, zero_add]
  · show 1 * x.g = x.g
    exact one_mul x.g

theorem hopfTw_inv_mul_cancel (x : HopfTwExt G) : x⁻¹ * x = 1 := by
  refine HopfTwExt.ext ?_ ?_
  · show -x.a - hopfTwR x.g⁻¹ x.g + x.a + hopfTwR x.g⁻¹ x.g = 0
    abel
  · show x.g⁻¹ * x.g = 1
    exact inv_mul_cancel x.g

noncomputable instance hopfTwExtGroup : Group (HopfTwExt G) :=
  Group.ofLeftAxioms hopfTw_mul_assoc hopfTw_one_mul hopfTw_inv_mul_cancel

theorem hopfTw_mul_a (x y : HopfTwExt G) : (x * y).a = x.a + y.a + hopfTwR x.g y.g :=
  rfl

theorem hopfTw_mul_g (x y : HopfTwExt G) : (x * y).g = x.g * y.g :=
  rfl

/-- Elements `(a, 1)` are central. -/
theorem hopfTw_comm_of_g_eq_one {x : HopfTwExt G} (hx : x.g = 1) (y : HopfTwExt G) :
    x * y = y * x := by
  refine HopfTwExt.ext ?_ ?_
  · rw [hopfTw_mul_a, hopfTw_mul_a, hx, hopfTwR_one_left y.g, hopfTwR_one_right y.g, add_zero,
      add_zero, add_comm x.a y.a]
  · rw [hopfTw_mul_g, hopfTw_mul_g, hx, one_mul, mul_one]

variable (G) in
/-- The projection `X →* G`. -/
noncomputable def hopfTwProj : HopfTwExt G →* G :=
  MonoidHom.mk' (fun x => x.g) fun x y => hopfTw_mul_g x y

variable {α : Type} (f : FreeGroup α →* G)

/-- The lift `F →* X` of `f`, sending each generator `s` to `(0, f s)`. -/
noncomputable def hopfTwLift : FreeGroup α →* HopfTwExt G :=
  FreeGroup.lift fun s => (⟨0, f (FreeGroup.of s)⟩ : HopfTwExt G)

theorem hopfTwLift_g (w : FreeGroup α) : (hopfTwLift f w).g = f w := by
  have h : (hopfTwProj G).comp (hopfTwLift f) = f :=
    FreeGroup.ext_hom _ _ fun s =>
      congrArg (hopfTwProj G)
        (FreeGroup.lift_apply_of (f := fun s => (⟨0, f (FreeGroup.of s)⟩ : HopfTwExt G)) (x := s))
  exact DFunLike.congr_fun h w

theorem hopfTwLift_commutator_le :
    ⁅(⊤ : Subgroup (FreeGroup α)), f.ker⁆ ≤ (hopfTwLift f).ker := by
  refine Subgroup.commutator_le.mpr fun w _ r hr => ?_
  have hr1 : (hopfTwLift f r).g = 1 := (hopfTwLift_g f r).trans (MonoidHom.mem_ker.mp hr)
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact (hopfTw_comm_of_g_eq_one hr1 (hopfTwLift f w)).symm

/-- The descended map `E = F ⧸ [F,R] →* X`. -/
noncomputable def hopfTwBar : HopfExt f →* HopfTwExt G :=
  QuotientGroup.lift ⁅(⊤ : Subgroup (FreeGroup α)), f.ker⁆ (hopfTwLift f)
    (hopfTwLift_commutator_le f)

theorem hopfTwBar_g (x : HopfExt f) : (hopfTwBar f x).g = hopfExtProj f x := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective ⁅(⊤ : Subgroup (FreeGroup α)), f.ker⁆ x
  exact hopfTwLift_g f w

end TwistedExt

end GroupApproximation.Full.LVHopf
