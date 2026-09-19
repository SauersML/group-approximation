import GroupApproximation.Kazhdan.RealGroupRing

/-!
# Rational proof objects for exact group-ring SOS certificates

Numerical SDP output is not trusted.  This layer lets a discovered Gram
factorization be rationalized and stored using exact rational coefficients;
Lean then maps the checked identity into the real group ring consumed by the
property `(T)` theorem.
-/

namespace GroupApproximation
namespace RationalGroupRingCertificate

universe u

variable {G : Type u} [Group G]

/-- The rational group ring used for finite certificate data. -/
abbrev Element (G : Type u) := MonoidAlgebra ℚ G

/-- Coefficientwise embedding of the rational group ring into the real group
ring. -/
noncomputable def toReal : Element G →+* RealGroupRing.Element G :=
  MonoidAlgebra.mapRingHom G (Rat.castHom ℝ)

/-- Rational convolution. -/
noncomputable def convolution (a b : Element G) : Element G := a * b

/-- The rational group-ring involution induced by inversion. -/
noncomputable def adjoint (a : Element G) : Element G :=
  MonoidAlgebra.mapDomain (fun g ↦ g⁻¹) a

/-- The rational Laplacian for a finite control set. -/
noncomputable def laplacianElement (S : Finset G) : Element G :=
  ∑ g ∈ S,
    (MonoidAlgebra.single 1 1 - MonoidAlgebra.single g 1)

@[simp] theorem toReal_single (g : G) (c : ℚ) :
    toReal (MonoidAlgebra.single g c) =
      MonoidAlgebra.single g (c : ℝ) := by
  simp [toReal]

@[simp] theorem toReal_adjoint (a : Element G) :
    toReal (adjoint a) = RealGroupRing.adjoint (toReal a) := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp [adjoint, RealGroupRing.adjoint]
  | add a b ha hb =>
      simp only [adjoint, MonoidAlgebra.mapDomain_add, map_add]
      change toReal (adjoint a) + toReal (adjoint b) =
        RealGroupRing.adjoint (toReal a + toReal b)
      rw [ha, hb, RealGroupRing.adjoint_add]
  | single g c => simp [adjoint, RealGroupRing.adjoint]

@[simp] theorem toReal_convolution (a b : Element G) :
    toReal (convolution a b) =
      RealGroupRing.convolution (toReal a) (toReal b) := by
  exact map_mul toReal a b

@[simp] theorem toReal_laplacianElement (S : Finset G) :
    toReal (laplacianElement S) = RealGroupRing.laplacianElement S := by
  classical
  simp [laplacianElement, RealGroupRing.laplacianElement]

@[simp] theorem toReal_smul (c : ℚ) (a : Element G) :
    toReal (c • a) = (c : ℝ) • toReal a := by
  simp [Algebra.smul_def, toReal]

/-- A finite exact rational certificate.  Equality here is decidable
coefficient arithmetic on finitely supported rational functions. -/
def IsRationalSOSQuadraticGap (S : Finset G) (c : ℚ) : Prop :=
  ∃ n : ℕ, ∃ factor : Fin n → Element G,
    convolution (adjoint (laplacianElement S)) (laplacianElement S) -
        c • laplacianElement S =
      ∑ i, convolution (adjoint (factor i)) (factor i)

/-- Exact rational certificate data maps to the real SOS identity required by
the analytic property `(T)` bridge. -/
theorem real_sos_of_rational_sos (S : Finset G) {c : ℚ}
    (hcert : IsRationalSOSQuadraticGap S c) :
    RealGroupRing.IsSOSQuadraticGap S (c : ℝ) := by
  classical
  rcases hcert with ⟨n, factor, hidentity⟩
  refine ⟨n, fun i ↦ toReal (factor i), ?_⟩
  have hmapped := congrArg toReal hidentity
  simpa [map_sub] using hmapped

end RationalGroupRingCertificate
end GroupApproximation
