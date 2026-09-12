import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationCore
import Mathlib.Order.Filter.Cofinite

namespace GroupApproximation.Manuscript.OneSidedMFRadical
namespace TensorSynchronizationGroupData

open Filter

universe u v w

theorem ker_prod_one_eq_prod_of_ker_le
    {S : Type w} [Group S] {G : Type v} [Group G]
    {Q : Type u} [Group Q] (lambda : S →* G) (eta : S →* Q)
    (hker : lambda.ker ≤ eta.ker) :
    (lambda.prod (1 : S →* Q)).ker = (lambda.prod eta).ker := by
  ext s
  constructor
  · intro hs
    have hpair := MonoidHom.mem_ker.mp hs
    have hlambda : lambda s = 1 := by
      simpa using congrArg Prod.fst hpair
    have heta : eta s = 1 :=
      MonoidHom.mem_ker.mp (hker (MonoidHom.mem_ker.mpr hlambda))
    apply MonoidHom.mem_ker.mpr
    apply Prod.ext
    · exact hlambda
    · exact heta
  · intro hs
    have hpair := MonoidHom.mem_ker.mp hs
    have hlambda : lambda s = 1 := by
      simpa using congrArg Prod.fst hpair
    apply MonoidHom.mem_ker.mpr
    apply Prod.ext
    · exact hlambda
    · simp

def productFiniteQuotientHom
    {Gamma : Type*} [Group Gamma] {Q : Type*} [Group Q]
    {G : Type*} [Group G] {B : Type*} [Group B]
    (lambda : Gamma →* G) (beta : Q →* B) : Gamma × Q →* G × B :=
  (lambda.comp (MonoidHom.fst Gamma Q)).prod
    (beta.comp (MonoidHom.snd Gamma Q))

@[simp] theorem productFiniteQuotientHom_apply
    {Gamma : Type*} [Group Gamma] {Q : Type*} [Group Q]
    {G : Type*} [Group G] {B : Type*} [Group B]
    (lambda : Gamma →* G) (beta : Q →* B) (z : Gamma × Q) :
    productFiniteQuotientHom lambda beta z = (lambda z.1, beta z.2) := rfl

def tensorSynchronizationSource
    {S : Type u} [Group S] {Gamma : Type v} [Group Gamma]
    {Q : Type w} [Group Q] (iota : S →* Gamma) : S →* Gamma × Q :=
  iota.prod (1 : S →* Q)

def tensorSynchronizationTarget
    {S : Type u} [Group S] {Gamma : Type v} [Group Gamma]
    {Q : Type w} [Group Q] (iota : S →* Gamma) (tau : S →* Q) :
    S →* Gamma × Q := iota.prod tau

@[simp] theorem tensorSynchronizationSource_apply
    {S : Type u} [Group S] {Gamma : Type v} [Group Gamma]
    {Q : Type w} [Group Q] (iota : S →* Gamma) (s : S) :
    tensorSynchronizationSource (Q := Q) iota s = (iota s, 1) := rfl

@[simp] theorem tensorSynchronizationTarget_apply
    {S : Type u} [Group S] {Gamma : Type v} [Group Gamma]
    {Q : Type w} [Group Q] (iota : S →* Gamma) (tau : S →* Q) (s : S) :
    tensorSynchronizationTarget iota tau s = (iota s, tau s) := rfl

theorem productFiniteQuotient_source_target_ker_eq
    {S : Type*} [Group S] {Gamma : Type*} [Group Gamma]
    {Q : Type*} [Group Q] {G : Type*} [Group G] {B : Type*} [Group B]
    (iota : S →* Gamma) (tau : S →* Q)
    (lambda : Gamma →* G) (beta : Q →* B)
    (hker : (lambda.comp iota).ker ≤ (beta.comp tau).ker) :
    ((productFiniteQuotientHom lambda beta).comp
      (tensorSynchronizationSource (Q := Q) iota)).ker =
    ((productFiniteQuotientHom lambda beta).comp
      (tensorSynchronizationTarget iota tau)).ker := by
  ext s
  constructor
  · intro hs
    have hpair := MonoidHom.mem_ker.mp hs
    have hlambda : lambda (iota s) = 1 := by
      simpa [productFiniteQuotientHom, tensorSynchronizationSource] using
        congrArg Prod.fst hpair
    have hbeta : beta (tau s) = 1 :=
      MonoidHom.mem_ker.mp (hker (MonoidHom.mem_ker.mpr hlambda))
    apply MonoidHom.mem_ker.mpr
    apply Prod.ext <;>
      simp [productFiniteQuotientHom, tensorSynchronizationTarget, hlambda, hbeta]
  · intro hs
    have hpair := MonoidHom.mem_ker.mp hs
    have hlambda : lambda (iota s) = 1 := by
      simpa [productFiniteQuotientHom, tensorSynchronizationTarget] using
        congrArg Prod.fst hpair
    apply MonoidHom.mem_ker.mpr
    apply Prod.ext <;>
      simp [productFiniteQuotientHom, tensorSynchronizationSource, hlambda]

theorem productFiniteQuotient_eventually_detects_second
    {Gamma : Type w} [Group Gamma] {Q : Type v} [Group Q]
    {G : ℕ → Type u} [∀ n, Group (G n)]
    {B : ℕ → Type u} [∀ n, Group (B n)]
    (lambda : ∀ n, Gamma →* G n) (beta : ∀ n, Q →* B n)
    (hdetect : ∀ q : Q, q ≠ 1 → ∀ᶠ n in cofinite, beta n q ≠ 1)
    (z : Gamma × Q) (_hfirst : z.1 = 1) (hsecond : z.2 ≠ 1) :
    ∀ᶠ n in cofinite, productFiniteQuotientHom (lambda n) (beta n) z ≠ 1 := by
  filter_upwards [hdetect z.2 hsecond] with n hn
  intro hz
  apply hn
  simpa using congrArg Prod.snd hz

end TensorSynchronizationGroupData
end GroupApproximation.Manuscript.OneSidedMFRadical
