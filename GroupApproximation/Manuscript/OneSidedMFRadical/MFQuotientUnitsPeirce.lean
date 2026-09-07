import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsStepOne

/-!
# Peirce transvections in the corner-unit subgroup

The corner-unit subgroup is normal because its definition ranges over all
homomorphisms, including their conjugates. Two orthogonal copies of the unit
then suffice to kill every off-diagonal transvection relative to either copy.
This is the algebra needed to reduce arbitrary units to supported form.
-/

namespace GroupApproximation
namespace MFQuotientUnits

instance cornerUnitSubgroup_normal (R : Type) [Ring R] :
    (cornerUnitSubgroup R).Normal := by
  constructor
  intro x hx g
  have hle : cornerUnitSubgroup R ≤
      (cornerUnitSubgroup R).comap (MulAut.conj g).toMonoidHom := by
    refine iSup_le fun S ↦ iSup_le fun _ ↦ iSup_le fun _ ↦ iSup_le fun s ↦
      iSup_le fun t ↦ iSup_le fun hts ↦ iSup_le fun hfull ↦ iSup_le fun n ↦
      iSup_le fun hn ↦ iSup_le fun φ ↦ ?_
    rintro _ ⟨y, rfl⟩
    exact le_cornerUnitSubgroup S s t hts hfull n hn
      ((MulAut.conj g).toMonoidHom.comp φ) ⟨y, rfl⟩
  exact hle hx

namespace Peirce

variable {R : Type} [Ring R]

/-- A square-zero element gives a unit with its inverse displayed. -/
def squareZeroUnit (x : R) (hx : x * x = 0) : Rˣ where
  val := 1 + x
  inv := 1 - x
  val_inv := by noncomm_ring [hx]
  inv_val := by noncomm_ring [hx]

/-- Membership recorded by the ring value, without choosing an inverse. -/
def OneAddIn (N : Subgroup Rˣ) (x : R) : Prop :=
  ∃ u ∈ N, (u : R) = 1 + x

theorem OneAddIn.add {N : Subgroup Rˣ} {x y : R}
    (hx : OneAddIn N x) (hy : OneAddIn N y) (hxy : x * y = 0) :
    OneAddIn N (x + y) := by
  obtain ⟨u, hu, hux⟩ := hx
  obtain ⟨v, hv, hvy⟩ := hy
  refine ⟨u * v, N.mul_mem hu hv, ?_⟩
  rw [Units.val_mul, hux, hvy]
  noncomm_ring [hxy]

theorem OneAddIn.mem {N : Subgroup Rˣ} {x : R} (h : OneAddIn N x)
    (u : Rˣ) (hu : (u : R) = 1 + x) : u ∈ N := by
  obtain ⟨v, hv, hvx⟩ := h
  rw [Units.ext (hu.trans hvx.symm)]
  exact hv

/-- The elementary commutator calculation, also for a normal subgroup that
contains just one of the two factors. -/
theorem oneAddIn_product {N : Subgroup Rˣ} [N.Normal] {a b : R}
    (haa : a * a = 0) (hbb : b * b = 0) (hba : b * a = 0)
    (hmem : OneAddIn N a ∨ OneAddIn N b) : OneAddIn N (a * b) := by
  let A := squareZeroUnit a haa
  let B := squareZeroUnit b hbb
  have hm : A * B * A⁻¹ * B⁻¹ ∈ N := by
    rcases hmem with ha | hb
    · have hA : A ∈ N := ha.mem A rfl
      have h := N.mul_mem hA
        ((inferInstance : N.Normal).conj_mem A⁻¹ (N.inv_mem hA) B)
      simpa only [mul_assoc] using h
    · have hB : B ∈ N := hb.mem B rfl
      exact N.mul_mem ((inferInstance : N.Normal).conj_mem B hB A)
        (N.inv_mem hB)
  refine ⟨A * B * A⁻¹ * B⁻¹, hm, ?_⟩
  change (1 + a) * (1 + b) * (1 - a) * (1 - b) = 1 + a * b
  have haba : a * b * a = 0 := by rw [mul_assoc, hba, mul_zero]
  have habb : a * b * b = 0 := by rw [mul_assoc, hbb, mul_zero]
  have haab : a * a * b = 0 := by rw [haa, zero_mul]
  have habab : a * b * a * b = 0 := by rw [haba, zero_mul]
  noncomm_ring [haa, hbb, hba, haba, habb, haab, habab]

/-- Two normalized equivalent orthogonal idempotents. -/
structure Pair (R : Type) [Ring R] where
  e : R
  f : R
  a : R
  b : R
  ee : e * e = e
  ff : f * f = f
  ef : e * f = 0
  fe : f * e = 0
  ab : a * b = e
  ba : b * a = f
  ea : e * a = a
  af : a * f = a
  fb : f * b = b
  be : b * e = b

namespace Pair

variable (P : Pair R)

theorem aa : P.a * P.a = 0 := by
  calc P.a * P.a = (P.a * P.f) * (P.e * P.a) := by rw [P.af, P.ea]
    _ = P.a * (P.f * P.e) * P.a := by noncomm_ring
    _ = 0 := by rw [P.fe]; simp

theorem bb : P.b * P.b = 0 := by
  calc P.b * P.b = (P.b * P.e) * (P.f * P.b) := by rw [P.be, P.fb]
    _ = P.b * (P.e * P.f) * P.b := by noncomm_ring
    _ = 0 := by rw [P.ef]; simp

/-- The two known corner families also generate every upper Peirce root.
The part outside the second corner is a commutator with a known root. -/
theorem upper {N : Subgroup Rˣ} [N.Normal]
    (hupper : ∀ y : R, P.e * y = y → y * P.f = y → OneAddIn N y)
    {x : R} (hex : P.e * x = x) (hxe : x * P.e = 0) : OneAddIn N x := by
  let y := x * P.f
  let z := x - y
  have hey : P.e * y = y := by dsimp [y]; rw [← mul_assoc, hex]
  have hyf : y * P.f = y := by dsimp [y]; rw [mul_assoc, P.ff]
  have hye : y * P.e = 0 := by dsimp [y]; rw [mul_assoc, P.fe, mul_zero]
  have hez : P.e * z = z := by dsimp [z]; rw [mul_sub, hex, hey]
  have hze : z * P.e = 0 := by dsimp [z]; rw [sub_mul, hxe, hye, sub_self]
  have hzf : z * P.f = 0 := by dsimp [z, y]; rw [sub_mul, mul_assoc, P.ff, sub_self]
  have hzb : z * P.b = 0 := by
    calc z * P.b = z * (P.f * P.b) := by rw [P.fb]
      _ = 0 := by rw [← mul_assoc, hzf, zero_mul]
  have hza : z * P.a = 0 := by
    calc z * P.a = z * (P.e * P.a) := by rw [P.ea]
      _ = 0 := by rw [← mul_assoc, hze, zero_mul]
  have haux : (P.b * z) * (P.b * z) = 0 := by
    calc (P.b * z) * (P.b * z) = P.b * (z * P.b) * z := by noncomm_ring
      _ = 0 := by rw [hzb]; simp
  have hback : (P.b * z) * P.a = 0 := by rw [mul_assoc, hza, mul_zero]
  have hforward : P.a * (P.b * z) = z := by rw [← mul_assoc, P.ab, hez]
  have hz : OneAddIn N z := by
    rw [← hforward]
    exact oneAddIn_product P.aa haux hback (Or.inl (hupper P.a P.ea P.af))
  have hyz : y * z = 0 := by
    calc y * z = y * (P.e * z) := by rw [hez]
      _ = 0 := by rw [← mul_assoc, hye, zero_mul]
  have h := (hupper y hey hyf).add hz hyz
  have hsum : y + z = x := by dsimp [z]; abel
  rwa [hsum] at h

/-- The lower Peirce roots follow from the same commutator calculation. -/
theorem lower {N : Subgroup Rˣ} [N.Normal]
    (hlower : ∀ y : R, P.f * y = y → y * P.e = y → OneAddIn N y)
    {x : R} (hex : P.e * x = 0) (hxe : x * P.e = x) : OneAddIn N x := by
  let y := P.f * x
  let z := x - y
  have hfy : P.f * y = y := by dsimp [y]; rw [← mul_assoc, P.ff]
  have hye : y * P.e = y := by dsimp [y]; rw [mul_assoc, hxe]
  have hey : P.e * y = 0 := by dsimp [y]; rw [← mul_assoc, P.ef, zero_mul]
  have hze : z * P.e = z := by dsimp [z]; rw [sub_mul, hxe, hye]
  have hez : P.e * z = 0 := by dsimp [z]; rw [mul_sub, hex, hey, sub_self]
  have hfz : P.f * z = 0 := by dsimp [z, y]; rw [mul_sub, ← mul_assoc, P.ff, sub_self]
  have haz : P.a * z = 0 := by
    calc P.a * z = (P.a * P.f) * z := by rw [P.af]
      _ = 0 := by rw [mul_assoc, hfz, mul_zero]
  have hbz : P.b * z = 0 := by
    calc P.b * z = (P.b * P.e) * z := by rw [P.be]
      _ = 0 := by rw [mul_assoc, hez, mul_zero]
  have haux : (z * P.a) * (z * P.a) = 0 := by
    calc (z * P.a) * (z * P.a) = z * (P.a * z) * P.a := by noncomm_ring
      _ = 0 := by rw [haz]; simp
  have hback : P.b * (z * P.a) = 0 := by rw [← mul_assoc, hbz, zero_mul]
  have hforward : (z * P.a) * P.b = z := by rw [mul_assoc, P.ab, hze]
  have hz : OneAddIn N z := by
    rw [← hforward]
    exact oneAddIn_product haux P.bb hback (Or.inr (hlower P.b P.fb P.be))
  have hyz : y * z = 0 := by
    calc y * z = (y * P.e) * z := by rw [hye]
      _ = 0 := by rw [mul_assoc, hez, mul_zero]
  have h := (hlower y hfy hye).add hz hyz
  have hsum : y + z = x := by dsimp [z]; abel
  rwa [hsum] at h

end Pair

/-- Normalized witnesses for two copies of the unit. -/
structure Frame (R : Type) [Ring R] where
  s : Fin 2 → R
  t : Fin 2 → R
  ts : ∀ i, t i * s i = 1
  cross : ∀ i j, i ≠ j → t i * s j = 0

namespace Frame

variable (F : Frame R)

def e (i : Fin 2) : R := F.s i * F.t i

theorem ts_action (i j : Fin 2) (x : R) :
    F.t i * (F.s j * x) = if i = j then x else 0 := by
  rw [← mul_assoc]
  split_ifs with h
  · subst j; rw [F.ts, one_mul]
  · rw [F.cross i j h, zero_mul]

def pair (i j : Fin 2) (hij : i ≠ j) : Pair R where
  e := F.e i
  f := F.e j
  a := F.s i * F.t j
  b := F.s j * F.t i
  ee := by simp only [e, mul_assoc, F.ts_action, if_pos rfl]
  ff := by simp only [e, mul_assoc, F.ts_action, if_pos rfl]
  ef := by simp only [e, mul_assoc, F.ts_action, if_neg hij, mul_zero]
  fe := by simp only [e, mul_assoc, F.ts_action, if_neg hij.symm, mul_zero]
  ab := by simp only [e, mul_assoc, F.ts_action, if_pos rfl]
  ba := by simp only [e, mul_assoc, F.ts_action, if_pos rfl]
  ea := by simp only [e, mul_assoc, F.ts_action, if_pos rfl]
  af := by simp only [e, mul_assoc, F.ts_action, if_pos rfl]
  fb := by simp only [e, mul_assoc, F.ts_action, if_pos rfl]
  be := by simp only [e, mul_assoc, F.ts_action, if_pos rfl]

noncomputable def root (i j : Fin 2) (hij : i ≠ j) (c : R) : Rˣ :=
  matrixCornerUnitHom F.s F.t F.ts F.cross (elementaryUnit i j hij c)

theorem root_val (i j : Fin 2) (hij : i ≠ j) (c : R) :
    (F.root i j hij c : R) = 1 + F.s i * c * F.t j := by
  rw [root, coe_matrixCornerUnitHom]
  change 1 - matrixWitnessSum F.s F.t +
    matrixEmbed F.s F.t (1 + Matrix.single i j c) = _
  rw [matrixEmbed_add, matrixEmbed_one]
  have hsingle : matrixEmbed F.s F.t (Matrix.single i j c) = F.s i * c * F.t j := by
    fin_cases i <;> fin_cases j <;>
      simp [matrixEmbed, Fin.sum_univ_two, Matrix.single]
  rw [hsingle]; abel

theorem root_mem [Countable R] (hR : IsPurelyInfiniteSimpleRing R)
    (i j : Fin 2) (hij : i ≠ j) (c : R) : F.root i j hij c ∈ cornerUnitSubgroup R :=
  elementaryRange_le_cornerUnitSubgroup hR (n := 2) (by decide)
    ((matrixCornerUnitHom F.s F.t F.ts F.cross).comp (elementaryGroup (Fin 2) R).subtype)
    ⟨⟨elementaryUnit i j hij c, elementaryUnit_mem i j hij c⟩, rfl⟩

theorem between [Countable R] (hR : IsPurelyInfiniteSimpleRing R)
    (i j : Fin 2) (hij : i ≠ j) (x : R)
    (hl : F.e i * x = x) (hr : x * F.e j = x) :
    OneAddIn (cornerUnitSubgroup R) x := by
  refine ⟨F.root i j hij (F.t i * x * F.s j), F.root_mem hR i j hij _, ?_⟩
  rw [F.root_val]
  have h : F.s i * (F.t i * x * F.s j) * F.t j = x := by
    calc F.s i * (F.t i * x * F.s j) * F.t j = F.e i * x * F.e j := by
          dsimp [e]; noncomm_ring
      _ = x := by rw [hl, hr]
  rw [h]

theorem upper [Countable R] (hR : IsPurelyInfiniteSimpleRing R)
    (i j : Fin 2) (hij : i ≠ j) {x : R}
    (hl : F.e i * x = x) (hr : x * F.e i = 0) :
    OneAddIn (cornerUnitSubgroup R) x :=
  (F.pair i j hij).upper (fun y hy hy' ↦ F.between hR i j hij y hy hy') hl hr

theorem lower [Countable R] (hR : IsPurelyInfiniteSimpleRing R)
    (i j : Fin 2) (hij : i ≠ j) {x : R}
    (hl : F.e i * x = 0) (hr : x * F.e i = x) :
    OneAddIn (cornerUnitSubgroup R) x :=
  (F.pair i j hij).lower (fun y hy hy' ↦ F.between hR j i hij.symm y hy hy') hl hr

end Frame
end Peirce
end MFQuotientUnits
end GroupApproximation

#audit_axioms GroupApproximation.MFQuotientUnits.Peirce.Frame.upper
#audit_axioms GroupApproximation.MFQuotientUnits.Peirce.Frame.lower
