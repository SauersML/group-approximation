import GroupApproximation.Leavitt.HilbertHotelWhitehead
import GroupApproximation.Leavitt.UniversalLeavitt

/-!
# The Hilbert-hotel frames over `L_{𝔽₂}(1,2)`

The block algebra of `HilbertHotelBlocks`, `HilbertHotelSaturation` and
`HilbertHotelWhitehead` is stated for an arbitrary ring carrying a binary
Leavitt family.  This file instantiates all of it at the ring the construction
actually uses: the in-repo universal binary Leavitt algebra
`UniversalLeavitt.BinaryLeavittAlgebra = L_{𝔽₂}(1,2)`, with corner width
`m = 4` and frame size `N = 4m = 16`.

Nontriviality of the algebra is the one extra input, and it is already available
(`UniversalLeavittOver` builds it from the stream representation); it is what
makes the defect `e₁₃(q)` a nontrivial element of `E₁₆(L_{𝔽₂}(1,2))`.
-/

namespace GroupApproximation
namespace HilbertHotel
namespace Binary

open scoped commutatorElement

/-- The coefficient ring of the construction: `R = L_{𝔽₂}(1,2)`. -/
abbrev R : Type := UniversalLeavitt.BinaryLeavittAlgebra

/-- Its canonical binary Leavitt family `s₀, s₁, r₀, r₁`. -/
def L : LeavittFamily R := UniversalLeavitt.family

/-! ### The Leavitt input at `m = 4` -/

theorem p_add_q : L.p0 + L.p1 = 1 := HilbertHotel.p_add_q L

theorem p_mul_q : L.p0 * L.p1 = 0 := HilbertHotel.p_mul_q L

theorem r1_mul_q_mul_s1 : L.t1 * L.p1 * L.s1 = 1 := HilbertHotel.r1_mul_q_mul_s1 L

theorem q_ne_zero : L.p1 ≠ 0 := HilbertHotel.q_ne_zero L

/-! ### The `2m = 8` frame -/

theorem U8_mul_V8 : U8 L * V8 L = 1 := HilbertHotel.U8_mul_V8 L

theorem V8_mul_U8 : V8 L * U8 L = 1 := HilbertHotel.V8_mul_U8 L

theorem U8fin_mul_V8fin : U8fin L * V8fin L = 1 := HilbertHotel.U8fin_mul_V8fin L

theorem compression (g : Matrix (Fin 4) (Fin 4) R) :
    U8 L * !![g, 0; 0, 1] * V8 L
      = !![Matrix.scalar (Fin 4) L.s0 * g * Matrix.scalar (Fin 4) L.t0
             + Matrix.scalar (Fin 4) L.p1, 0; 0, 1] :=
  HilbertHotel.compression L g

theorem movedCentralizer_mark :
    U8 L * !![1, 0; 0, mark R] * V8 L
      = !![1 + Matrix.single 0 1 L.p1, 0; 0, mark R] :=
  HilbertHotel.movedCentralizer_mark L

/-! ### The `4m = 16` frame: boxed conjugation, defect, saturation -/

theorem Tunit_conj_corner (a : R) (i j : Fin 4) (h : corner i ≠ corner j) :
    Tunit L * elementaryUnit (corner i) (corner j) h a * (Tunit L)⁻¹
      = elementaryUnit (corner i) (corner j) h (L.s0 * a * L.t0) :=
  HilbertHotel.Tunit_conj_corner L a i j h

theorem Tunit_conj_mark (h45 : (4 : Fin 16) ≠ 5) (h01 : (0 : Fin 16) ≠ 1) :
    Tunit L * elementaryUnit (4 : Fin 16) 5 h45 1 * (Tunit L)⁻¹
      = elementaryUnit (0 : Fin 16) 1 h01 L.p1 * elementaryUnit (4 : Fin 16) 5 h45 1 :=
  HilbertHotel.Tunit_conj_mark L h45 h01

theorem defect_commutator
    (h01 : (0 : Fin 16) ≠ 1) (h45 : (4 : Fin 16) ≠ 5) (h12 : (1 : Fin 16) ≠ 2)
    (h02 : (0 : Fin 16) ≠ 2) :
    ⁅elementaryUnit (0 : Fin 16) 1 h01 L.p1 * elementaryUnit (4 : Fin 16) 5 h45 1,
      elementaryUnit (1 : Fin 16) 2 h12 1⁆
      = elementaryUnit (0 : Fin 16) 2 h02 L.p1 :=
  HilbertHotel.defect_commutator L h01 h45 h12 h02

theorem defect_from_conjugated_mark
    (h01 : (0 : Fin 16) ≠ 1) (h45 : (4 : Fin 16) ≠ 5) (h12 : (1 : Fin 16) ≠ 2)
    (h02 : (0 : Fin 16) ≠ 2) :
    ⁅Tunit L * elementaryUnit (4 : Fin 16) 5 h45 1 * (Tunit L)⁻¹,
      elementaryUnit (1 : Fin 16) 2 h12 1⁆
      = elementaryUnit (0 : Fin 16) 2 h02 L.p1 :=
  HilbertHotel.defect_from_conjugated_mark L h01 h45 h12 h02

/-- The defect is a nontrivial element of `E₁₆(L_{𝔽₂}(1,2))`. -/
theorem defect_ne_one (h02 : (0 : Fin 16) ≠ 2) :
    elementaryUnit (0 : Fin 16) 2 h02 L.p1 ≠ 1 :=
  HilbertHotel.defect_ne_one L h02

theorem saturation_chain (a : R)
    (h30 : (3 : Fin 16) ≠ 0) (h02 : (0 : Fin 16) ≠ 2) (h32 : (3 : Fin 16) ≠ 2)
    (h21 : (2 : Fin 16) ≠ 1) (h31 : (3 : Fin 16) ≠ 1) :
    ⁅⁅elementaryUnit (3 : Fin 16) 0 h30 (a * L.t1),
        elementaryUnit (0 : Fin 16) 2 h02 L.p1⁆,
      elementaryUnit (2 : Fin 16) 1 h21 L.s1⁆
      = elementaryUnit (3 : Fin 16) 1 h31 a :=
  HilbertHotel.saturation_chain L a h30 h02 h32 h21 h31

/-! ### Ellipticity of the stable letter -/

theorem Tunit_mem_elementaryGroup : Tunit L ∈ elementaryGroup (Fin 16) R :=
  HilbertHotel.Tunit_mem_elementaryGroup L

theorem whiteheadFactors_prod (h01 : (0 : Fin 2) ≠ 1) (h10 : (1 : Fin 2) ≠ 0) :
    (whiteheadFactors L h01 h10).prod = T16unit L :=
  HilbertHotel.whiteheadFactors_prod L h01 h10

end Binary
end HilbertHotel
end GroupApproximation
