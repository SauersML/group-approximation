import GroupApproximation.BooneHigmanLinear.Tulenbaev.Components
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# Horrocks for Steinberg groups: piece H of the `K₂` program (lane pal-q111)

Piece H of `board/k2-poly.md`: M. S. Tulenbaev, *The Steinberg group of a polynomial ring*,
Math. USSR Sb. 45 (1983) 139–154, Theorem 5.1 and Corollary 5.2. Read at source (pp. 139–153).
`A[X⁻¹] → A[X, X⁻¹]` is modelled, as in `Tulenbaev.Components`, by a second copy of `A[X]`
mapped by `X ↦ T⁻¹` (`Tulenbaev.toLaurentNeg`).

**Targets.**
* H.a `StHorrocksStatementAt` (T 5.1(a)). `St_r(A[X]) → St_r(A[X,X⁻¹]) ← St_r(A[X⁻¹])` are
  injective, and the images meet in `St_r(A)`. This is the whole Steinberg group, not only `K₂`, so
  it implies `Tulenbaev.K2HorrocksStatementAt` (sk-k2-loc).
* H.b `StMonicInjStatementAt` (T 5.2(a)). For monic `f`, `St_r(A[X]) → St_r(A[X]_f)` is injective.
* H.c `StHorrocksRelStatementAt` and `StMonicRelStatementAt` (T 5.1(b), 5.2(b)), the relative
  forms, with `r = N + 1` and "the image of `St_N`" through `SteinbergBasic.stab`.
* `...FR` versions restricted to rings whose residue fields at maximal ideals are finite
  (`HasFiniteResidueFields`). **The chain only needs these.** STAB applies Cor 5.2(a) over
  `F_p[X₂..X_n]`, LOCAL over localizations of `F_p[s]`, and the `ℤ[1/m]` analogue over
  `ℤ[1/m][s]`. All of these are finitely generated `ℤ`-algebras, so their residue fields are finite.

**What the proof uses (from the source).** The board's "nothing is Quillen-level" is too strong.
* T 5.1(a) ⇐ T 2.1 (local–global, `Tulenbaev.StLocalGlobalStatementAt`, sk-k2-loc) ∧ T Prop 4.3(a)
  over the local rings `A_𝔪` (`StLocalHorrocksStatementAt` below).
* T Prop 4.3(a) and T Cor 4.2 over a local ring `A` with residue field `k` need the FIELD case at `k`:
  `St_r(k[X]) → St_r(k[X,X⁻¹]) ← St_r(k[X⁻¹])` injective, with images meeting in `St_r(k)`.
  - Tulenbaev takes it from Quillen's fundamental theorem plus `K₂` stabilization.
  - For a FINITE field it follows from `K₂(r, k[X]) = 1` alone, with `SL_r(k) = E_r(k)`.
    The matrix of a common image has entries in `k[X] ∩ k[X⁻¹] = k`.
  - `K₂(r, F_p[X]) = 1` for `r ≥ 5` is on main (`ElemFP.bhNagaoUncond_wire_K2_bot_nagao`, Nagao).
    The chain needs every finite field `F_q`: `FiniteFieldPolyK2Statement`, the residue fields of
    `F_p[s]` and `ℤ[1/m][s]`.
* The rest of T §§3–4 is Steinberg words over a local ring. Lemmas 3.1–3.4 and Props 4.1, 4.3 use
  van der Kallen's `X_{v,w}` (foundations F, bh-pal-linear-char0) and two classical inputs:
  - the Dennis–Vaserstein theorem (T Lemma 3.1(d), (e)): `K₂(r, A)` of a local ring is generated
    over the relevant parabolic, as cited from Suslin–Tulenbaev (Zap. LOMI 64, 1976);
  - Wagoner/Loday (T Lemma 3.1(g)): `a ↦ {X, a}` is left inverse to the boundary map
    `K₂(A[X,X⁻¹]) → K₁(A)`, so `{X, a} = 1` forces `a = 1`.
* T Cor 5.2(a) ⇐ T 5.1(a) ∧ patching (T Prop 1.4(b), F.4) ∧ retraction splitting (T Prop 1.6,
  F.3).
* The relative forms (H.c) also use `K₁`/`K₂` stabilization over `k[X]`, `k[X⁻¹]` and `k[X,X⁻¹]`
  (T 4.3(b)). Nothing downstream in the chain needs H.c; STAB uses 5.2(a) only for (a).

No reduction theorem is claimed in this module. Not root-wired.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace TulenbaevHorrocks

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic Polynomial
open GroupApproximation.BooneHigmanLinear.Tulenbaev

/-- Every residue field of `A` at a maximal ideal is finite. This holds for every finitely generated
`ℤ`-algebra, e.g. `F_p[s₁..s_k]`, `ℤ[1/m][s₁..s_k]` and their quotients. -/
def HasFiniteResidueFields (A : Type) [CommRing A] : Prop :=
  ∀ M : Ideal A, M.IsMaximal → Finite (A ⧸ M)

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.HasFiniteResidueFields

/-- **The Horrocks property of `St_N` over `A`** (T 5.1(a) at one ring and rank): the two maps
`St_N(A[X]) → St_N(A[X,X⁻¹]) ← St_N(A[X⁻¹])` are injective, and two elements with the same image
come from one element of `St_N(A)`. -/
def StHorrocksAt (A : Type) [CommRing A] (N : ℕ) : Prop :=
  Function.Injective (ringMap (I := Fin N) (toLaurentPos A)) ∧
    Function.Injective (ringMap (I := Fin N) (toLaurentNeg A)) ∧
    ∀ α β : SteinbergGroup (Fin N) A[X],
      ringMap (toLaurentPos A) α = ringMap (toLaurentNeg A) β →
        ∃ γ : SteinbergGroup (Fin N) A,
          ringMap (Polynomial.C : A →+* A[X]) γ = α ∧ ringMap (Polynomial.C : A →+* A[X]) γ = β

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.StHorrocksAt

/-- **H.a** (T 5.1(a)): the Horrocks property of `St_N` over every commutative ring, `N ≥ n₀`
(Tulenbaev: `n₀ = 5`). -/
def StHorrocksStatementAt (n₀ : ℕ) : Prop :=
  ∀ (A : Type) [CommRing A] (N : ℕ), n₀ ≤ N → StHorrocksAt A N

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.StHorrocksStatementAt

/-- **H.a, finite residue fields**: the only case the `K₂` chain uses. -/
def StHorrocksFRStatementAt (n₀ : ℕ) : Prop :=
  ∀ (A : Type) [CommRing A], HasFiniteResidueFields A → ∀ N : ℕ, n₀ ≤ N → StHorrocksAt A N

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.StHorrocksFRStatementAt

/-- **Injectivity along a monic localization** at one ring and rank (T 5.2(a)). -/
def StMonicInjAt (A : Type) [CommRing A] (N : ℕ) : Prop :=
  ∀ f : A[X], f.Monic → ∀ α : SteinbergGroup (Fin N) A[X],
    ringMap (algebraMap A[X] (Localization.Away f)) α = 1 → α = 1

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.StMonicInjAt

/-- **H.b** (T 5.2(a)): for monic `f ∈ A[X]`, `St_N(A[X]) → St_N(A[X]_f)` is injective, `N ≥ n₀`. -/
def StMonicInjStatementAt (n₀ : ℕ) : Prop :=
  ∀ (A : Type) [CommRing A] (N : ℕ), n₀ ≤ N → StMonicInjAt A N

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.StMonicInjStatementAt

/-- **H.b, finite residue fields**: what STAB (T 5.3 at `F_p`) and LOCAL use. -/
def StMonicInjFRStatementAt (n₀ : ℕ) : Prop :=
  ∀ (A : Type) [CommRing A], HasFiniteResidueFields A → ∀ N : ℕ, n₀ ≤ N → StMonicInjAt A N

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.StMonicInjFRStatementAt

/-- **H.c, part 1** (T 5.1(b)), at rank `r = N + 1`.  Let `α ∈ K₂(N+1, A[X])` with `α(0) = 1`, and
suppose its image in `St_{N+1}(A[X,X⁻¹])` is `stab γ · β` with `γ ∈ St_N(A[X,X⁻¹])` and `β` coming
from `St_{N+1}(A[X⁻¹])`.  Then `α` lies in the image of `St_N(A[X])`. -/
def StHorrocksRelStatementAt (n₀ : ℕ) : Prop :=
  ∀ (A : Type) [CommRing A] (N : ℕ), n₀ ≤ N + 1 →
    ∀ α ∈ K2 (Fin (N + 1)) A[X], ringMap (Polynomial.evalRingHom (0 : A)) α = 1 →
      ∀ (γ : St N (LaurentPolynomial A)) (β : St (N + 1) A[X]),
        ringMap (toLaurentPos A) α = stab N _ γ * ringMap (toLaurentNeg A) β →
          α ∈ (stab N A[X]).range

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.StHorrocksRelStatementAt

/-- **H.c, part 2** (T 5.2(b)), at rank `r = N + 1`: if `α ∈ K₂(N+1, A[X])`, `α(0) = 1`, `f` is monic
and the image of `α` in `St_{N+1}(A[X]_f)` comes from `St_N(A[X]_f)`, then `α` comes from
`St_N(A[X])`. -/
def StMonicRelStatementAt (n₀ : ℕ) : Prop :=
  ∀ (A : Type) [CommRing A] (N : ℕ), n₀ ≤ N + 1 →
    ∀ f : A[X], f.Monic →
      ∀ α ∈ K2 (Fin (N + 1)) A[X], ringMap (Polynomial.evalRingHom (0 : A)) α = 1 →
        ringMap (algebraMap A[X] (Localization.Away f)) α ∈ (stab N (Localization.Away f)).range →
          α ∈ (stab N A[X]).range

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.StMonicRelStatementAt

/-! ### Inputs of T 5.1(a), read at source -/

/-- **T Prop 4.3(a)**: the Horrocks property of `St_N` over local rings, `N ≥ n₀`.  With T 2.1
(`Tulenbaev.StLocalGlobalStatementAt`) it gives H.a (T 5.1(a) proof, p. 152). -/
def StLocalHorrocksStatementAt (n₀ : ℕ) : Prop :=
  ∀ (A : Type) [CommRing A] [IsLocalRing A] (N : ℕ), n₀ ≤ N → StHorrocksAt A N

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.StLocalHorrocksStatementAt

/-- **T Prop 4.3(a), finite residue field**: the local case the chain needs. -/
def StLocalHorrocksFRStatementAt (n₀ : ℕ) : Prop :=
  ∀ (A : Type) [CommRing A] [IsLocalRing A], Finite (IsLocalRing.ResidueField A) →
    ∀ N : ℕ, n₀ ≤ N → StHorrocksAt A N

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.StLocalHorrocksFRStatementAt

/-- **The field input** of T Cor 4.2 / Prop 4.3(a) at a finite residue field: `K₂(N, k[X]) = 1`.
It gives `StHorrocksAt k N` for a finite field (`SL_N(k) = E_N(k)`, `k[X] ∩ k[X⁻¹] = k`).  The case
`k = F_p`, `N ≥ 5` is on main (`ElemFP.bhNagaoUncond_wire_K2_bot_nagao`, Nagao's amalgam). -/
def FiniteFieldPolyK2Statement (n₀ : ℕ) : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (N : ℕ), n₀ ≤ N → K2 (Fin N) k[X] = ⊥

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.FiniteFieldPolyK2Statement

end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation
