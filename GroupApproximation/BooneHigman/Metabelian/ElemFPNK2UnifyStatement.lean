import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroNK2Cone
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2CubeResidueFieldGap
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2CubeLocalResidue
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeNilLocal
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeDilateEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# One cone residual for both the char-`p` and the char-zero cube gaps

Lane `bh-met-90i`.  Two gaps on the Boone–Higman metabelian root concern `NK₂` of polynomial
rings over a base `A`:

* `hloc = PolyK2CubeNilLocalStatement` over `A = F_p`, which lane `bh-met-90c` reduced to
  `k2CubeDilate_LocalStatement` (L) plus the Tulenbaev dilation residual
  `k2CubeDilate_PolyDilationStatement` (D);
* `hcube`, which lane `bh-met-90g` reduced to `czNK2_ConeStatement` (C), the predicate
  `czNK2_ConeOverStatement A` over every `A = ℤ[1/m]`, plus the stability half.

## LOUD: there is no implication between L and C

L speaks about `F_p[s_0..s_k]`, C about `ℤ[1/m][s_0..s_n]`.  Neither follows from the other with
the repository's tools.  There is no ring map `F_p → ℤ[1/m]`.  Reduction mod `p` sends the data
of C to data of the char-`p` type, but it cannot reflect death of `K₂` elements.  Lifting data of
L to `ℤ[1/m]` would need surjectivity of `K₂` on cube-killed elements, which is not available.
Both are true (Quillen), so each implies the other only vacuously through their truth; no
proof of either implication is given or claimed.

## What is proved instead: the cone residual is ring-generic and covers `F_p`

The predicate `czNK2_ConeOverStatement A` and the whole reduction of lanes `bh-met-81` and
`bh-met-90g` are generic in the base ring `A`.  The only ring input is the Jacobson-type property
`hres`: every maximal ideal of every `A[s_1..s_k]` contains a rational prime.  For `A = ZMod p`
this holds trivially, since `p = 0` (`nk2Unify_hres_zmod`).  So

* `nk2Unify_gapLocalOver_of_coneOver`: `czNK2_ConeOverStatement A → CZCubeGapLocalOverStatement A`
  given `hres`, and its converse `nk2Unify_coneOver_of_gapLocalOver` over every `A`;
* `CZCubeGapLocalOverStatement (ZMod p)` is **definitionally** the `p`-instance of
  `PolyK2CubeNilLocalStatement`;
* hence `nk2Unify_CharPConeStatement` (the cone residual over every `F_p`) is **logically
  equivalent** to `hloc` (both directions proved), and it needs **no dilation step**: D is not
  used anywhere on this route.

`nk2Unify_ConeStatement` (module `ElemFPNK2UnifyWire`) is the single predicate
`czNK2_ConeOverStatement` over both families of regular Jacobson bases of dimension at most one,
`ℤ[1/m]` (`m ≥ 1`) and `F_p` (`p` prime).  It gives `hloc` outright and, with the stability
half, `hcube`.  It is implied by the old sub-gaps `L ∧ D ∧ C`
(`nk2Unify_cone_of_k2CubeDilate`), so the new frontier is never stronger than the old.

## LOUD: strength

* `nk2Unify_ConeStatement ↔ PolyK2CubeNilLocalStatement ∧ czNK2_ConeStatement` (proved).  It is
  therefore **not** strictly weaker logically than `hloc ∧ C`; it is a sub-family (cone images of
  padded cube elements, at minimal rank) and strictly smaller in proof content.
* Compared with L alone, the char-`p` half is logically **at least as strong** (it implies `hloc`,
  which implies L).  If lane `bh-met-90h` closes D, the old route leaves only L, and L is then
  logically weaker than the char-`p` half here.  The gain is that D is removed from the frontier
  and the three sub-gaps L, D, C become one ring-generic statement.

## Truth check

True: by the equivalence it is `hloc ∧ C`, and both are `NK₂ = 0` for the regular rings
`F_p[s_1..s_k]` and `ℤ[1/m][s_1..s_k]` (Quillen), made unstable by stabilisation of `K₂` at a
finite rank.  Smallest char-`p` instance: `n = 0`, `v ∈ K₂(5, F_p[s_0])` with `v(0) = 1`; here
`v = 1` since `NK₂(F_p) = 0`, and `s = 1` works.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.Metabelian.ElemFP

/-- Over `F_p`, every maximal ideal of every `F_p[s_1..s_k]` contains the prime `p`, since
`p = 0` there. -/
theorem nk2Unify_hres_zmod (p : ℕ) (hp : p.Prime) :
    ∀ k : ℕ, ∀ P : Ideal (MvPolynomial (Fin k) (ZMod p)), P.IsMaximal →
      ∃ q : ℕ, q.Prime ∧ (q : MvPolynomial (Fin k) (ZMod p)) ∈ P := by
  intro k P _
  refine ⟨p, hp, ?_⟩
  rw [← map_natCast (MvPolynomial.C : ZMod p →+* MvPolynomial (Fin k) (ZMod p)) p,
    ZMod.natCast_self, map_zero]
  exact P.zero_mem

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Unify_hres_zmod

/-- **The cone residual gives the local cube form over any base `A` with `hres`.**  Chain the
generic reductions of lanes `bh-met-90g`, `bh-met-81` and `bh-met-74`. -/
theorem nk2Unify_gapLocalOver_of_coneOver (A : Type*) [CommRing A]
    (hres : ∀ k : ℕ, ∀ P : Ideal (MvPolynomial (Fin k) A), P.IsMaximal →
      ∃ p : ℕ, p.Prime ∧ (p : MvPolynomial (Fin k) A) ∈ P)
    (h : czNK2_ConeOverStatement A) : CZCubeGapLocalOverStatement A :=
  czCubeLocal_gapLocalOver_of_residueOver A hres
    (czCubeResField_residueOver_of_over A hres (czNK2_resFieldOver_of_coneOver A hres h))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Unify_gapLocalOver_of_coneOver

/-- Conversely, over every base `A`, the local cube form gives the cone residual. -/
theorem nk2Unify_coneOver_of_gapLocalOver (A : Type*) [CommRing A]
    (h : CZCubeGapLocalOverStatement A) : czNK2_ConeOverStatement A :=
  czNK2_coneOver_of_resFieldOver A
    (czCubeResField_over_of_residueOver A (czCubeLocal_residueOver_of_gapLocalOver A h))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Unify_coneOver_of_gapLocalOver

/-- **The char-`p` cone residual**: `czNK2_ConeOverStatement` over every prime field `F_p`. -/
def nk2Unify_CharPConeStatement : Prop :=
  ∀ p : ℕ, p.Prime → czNK2_ConeOverStatement (ZMod p)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Unify_CharPConeStatement

/-- **The char-`p` cone residual gives `hloc`**, with no dilation step.  At `A = ZMod p` the
local cube form is definitionally the `p`-instance of `PolyK2CubeNilLocalStatement`. -/
theorem nk2Unify_polyK2CubeNilLocal_of_charPCone (h : nk2Unify_CharPConeStatement) :
    PolyK2CubeNilLocalStatement := by
  intro p hp
  exact nk2Unify_gapLocalOver_of_coneOver (ZMod p) (nk2Unify_hres_zmod p hp) (h p hp)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Unify_polyK2CubeNilLocal_of_charPCone

/-- Conversely, `hloc` gives the char-`p` cone residual. -/
theorem nk2Unify_charPCone_of_polyK2CubeNilLocal (h : PolyK2CubeNilLocalStatement) :
    nk2Unify_CharPConeStatement := by
  intro p hp
  exact nk2Unify_coneOver_of_gapLocalOver (ZMod p) (h p hp)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Unify_charPCone_of_polyK2CubeNilLocal

/-- The old char-`p` sub-gaps L and D give the char-`p` cone residual. -/
theorem nk2Unify_charPCone_of_k2CubeDilate (hL : k2CubeDilate_LocalStatement)
    (hD : k2CubeDilate_PolyDilationStatement) : nk2Unify_CharPConeStatement :=
  nk2Unify_charPCone_of_polyK2CubeNilLocal (polyK2CubeNilLocal_of_k2CubeDilate hL hD)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Unify_charPCone_of_k2CubeDilate

/-- The char-`p` cone residual gives the old local sub-gap L. -/
theorem nk2Unify_k2CubeDilateLocal_of_charPCone (h : nk2Unify_CharPConeStatement) :
    k2CubeDilate_LocalStatement :=
  k2CubeDilate_local_of_polyK2CubeNilLocal (nk2Unify_polyK2CubeNilLocal_of_charPCone h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Unify_k2CubeDilateLocal_of_charPCone

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
