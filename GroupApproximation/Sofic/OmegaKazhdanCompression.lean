import GroupApproximation.Sofic.OmegaCoronaFinite
import GroupApproximation.Sofic.UltraproductKazhdanTransport

/-!
# The Kazhdan compression bundle over `B_ω`

`Sofic/UltraproductKazhdanProjection.lean` builds the manuscript's Kazhdan
projection over an **abstract** unital C-star algebra `B`, as
`KazhdanCompressionRep Γ H B`, and `Sofic/UltraproductKazhdanTransport.lean`
proves the endgame `V P V* = P` there, from Dedekind finiteness alone
(`kt_10_shift_conjugate_proj`).  Both were then specialized to the *cofinite*
corona, because that was the only corona in the tree.

Nothing in that machinery needed the cofinite filter; it needed a C-star algebra
that is Dedekind finite and a unitary representation into it.  `B_ω` is such an
algebra (`OmegaCoronaFinite`), and `OmegaAlmostRepresentation.piHom` is such a
representation.  So the printed algebra now carries the printed bundle, and this
file is the specialization:

* `omegaAdjointCorona_nontrivial` -- `B_ω ≠ 0`, which the Kazhdan average
  estimates ask for.  It is not automatic: it says `1` is not `ω`-null, which
  holds because the coordinate algebras are nonzero;
* `omegaCompressionRep` -- the bundle over `B_ω`, whose representation is
  `[Ad U_n(·)]_ω`;
* `kt_10_omega_shift_conjugate_proj` -- KT.10's consumed form, `V P V* = P`, in
  `B_ω`.

## What this is and is not

This is the printed *algebra* carrying the printed *projection*, with the
printed finiteness argument closing the conjugation step.  It is not yet a
re-proof of `thm:kazhdan-transport` along the printed route: that also needs the
action of `B_ω` on `K_ω` to read `Fix ⊆ ran P` back off the spectral gap, which
the development still does through the algebraic absorption identities on the
cofinite corona.  KT.00 stays open, and this file does not claim otherwise.
-/

namespace GroupApproximation
namespace OmegaKazhdanCompression

open Filter Matrix Topology
open UltraproductModelConstruction OmegaOperatorUltraproduct
open UltraproductKazhdanProjection
open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)] (ω : Ultrafilter ℕ)

/-- **`B_ω` is nonzero.**  Equivalently, the constant sequence `1` is not
`ω`-null, which is true because every coordinate algebra is nonzero -- the
hypothesis `[∀ n, Nonempty (Y n)]` in disguise. -/
instance omegaAdjointCorona_nontrivial : Nontrivial (OmegaAdjointCorona Y ω) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  have h0 : omegaMk Y ω 1 = 0 := by rw [map_one]; exact h
  rw [omegaMk_eq_zero_iff] at h0
  -- the coordinate norms are constantly `1`, because each coordinate algebra is
  -- nonzero, and a constant-one sequence does not tend to zero along `ω`
  simp at h0

/-- **The manuscript's bundle, over the manuscript's algebra.**  The
representation is `π(g) = [Ad U_n(g)]_ω`; every other field is data about the
groups and is independent of the algebra it is realized in. -/
def omegaCompressionRep {Γ : Type} {H : Type u} [Group Γ] [Group H]
    (A : OpAlmostRepresentation H) (hω : (ω : Filter ℕ) ≤ cofinite)
    (iota : Γ →* H) (s : H) (Q : Finset Γ) (kappa : ℝ)
    (kazhdan : IsKazhdanPair Γ Q kappa) (S : Finset Γ)
    (hQS : Q ⊆ S) (hone : (1 : Γ) ∈ S) (hsymm : ∀ γ ∈ S, γ⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hcomp : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ) :
    KazhdanCompressionRep Γ H (OmegaAdjointCorona A.model ω) where
  pi := OmegaAlmostRepresentation.piHom A ω hω
  iota := iota
  s := s
  Q := Q
  kappa := kappa
  kazhdan := kazhdan
  S := S
  QS := hQS
  one_mem := hone
  symm := hsymm
  generates := hgen
  compresses := hcomp

@[simp] theorem omegaCompressionRep_pi {Γ : Type} {H : Type u} [Group Γ] [Group H]
    (A : OpAlmostRepresentation H) (hω : (ω : Filter ℕ) ≤ cofinite)
    (iota : Γ →* H) (s : H) (Q : Finset Γ) (kappa : ℝ)
    (kazhdan : IsKazhdanPair Γ Q kappa) (S : Finset Γ)
    (hQS : Q ⊆ S) (hone : (1 : Γ) ∈ S) (hsymm : ∀ γ ∈ S, γ⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hcomp : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ) :
    (omegaCompressionRep ω A hω iota s Q kappa kazhdan S hQS hone hsymm hgen
      hcomp).pi = OmegaAlmostRepresentation.piHom A ω hω := rfl

/-- **KT.10 in `B_ω` itself.**  The conjugated Kazhdan projection equals the
Kazhdan projection, in the norm ultraproduct along `ω`.

Specializing `kt_10_shift_conjugate_proj` discharges the finiteness hypothesis
outright: `OmegaCoronaFinite.omegaAdjointCorona_isDedekindFiniteMonoid` is an
instance, so this carries no `Prop` premise beyond the bundle.  This is the
manuscript's "finiteness of `B_ω` makes `σ` unitary, and `σσ* = P + (1 - Q)`
forces `Q = P`" -- on `B_ω` rather than on the cofinite corona standing in for
it. -/
theorem kt_10_omega_shift_conjugate_proj {Γ : Type} {H : Type u} [Group Γ] [Group H]
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) :
    D.shift * D.proj * star D.shift = D.proj :=
  kt_10_shift_conjugate_proj D

end

end OmegaKazhdanCompression
end GroupApproximation
