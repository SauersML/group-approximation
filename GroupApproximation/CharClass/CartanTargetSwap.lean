import GroupApproximation.CharClass.SteenrodDiagonalTarget
import GroupApproximation.CharClass.CartanGroupRing

/-!
# The `ℤ/2`-action on `S(X) ⊗ S(X)`

The target of Steenrod's diagonal is the free `F₂`-module on pairs of singular
simplices, and the group ring acts on it **through the factor swap** — not by
scalar multiplication on coefficients.

That distinction is the whole equivariant content of the Cartan comparison, and
it is forced by the chain-map condition.  The source's differential begins with
multiplication by `1 + t` as a `Λ`-scalar, so the chain-map condition for `Φ`
reads

```text
∂ Φ(e_{i+1} ⊗ σ) = Φ(e_i ⊗ σ) + t · Φ(e_i ⊗ σ) + Φ(e_{i+1} ⊗ ∂σ),
```

and `cc-steenrod`'s boundary identity supplies the middle term as
`T Φ(e_i ⊗ σ)` with `T` the swap.  The two agree exactly when `t` acts as `T`.
On the free `Λ`-module on pairs, `t` acts on coefficients and moves no index, so
the condition is false there; `S(X) ⊗ S(X)` is not a free `Λ`-module and must not
be replaced by one.

Note that the swap exchanges the two *degrees* as well as the two simplices.
That costs nothing here because the target index carries both degrees as data
with the sum constraint as a proposition: only a proof of a `ℕ` equation moves,
and proofs are irrelevant, so the swap is cast-free.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

/-! ## 1. The swap on the index -/

/-- Exchange the two degrees. -/
def pairDegSwap {k : ℕ} (p : Steenrod.PairDeg k) : Steenrod.PairDeg k :=
  ⟨(p.val.2, p.val.1), by have := p.property; omega⟩

/-- Exchange the two factors of a pair of simplices, degrees and all. -/
def pairIdxSwap {X : TopCat.{0}} {k : ℕ} (q : Steenrod.PairIdx X k) :
    Steenrod.PairIdx X k :=
  ⟨pairDegSwap q.1, (q.2.2, q.2.1)⟩

theorem pairIdxSwap_involutive {X : TopCat.{0}} {k : ℕ} (q : Steenrod.PairIdx X k) :
    pairIdxSwap (pairIdxSwap q) = q := rfl

/-! ## 2. The swap as an involution of the free module -/

/-- The factor swap, as an endomorphism of the free `F₂`-module on pairs. -/
def pairSwap (X : TopCat.{0}) (k : ℕ) :
    Module.End (ZMod 2) (Steenrod.PairIdx X k →₀ ZMod 2) :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) pairIdxSwap

theorem pairSwap_apply (X : TopCat.{0}) (k : ℕ)
    (y : Steenrod.PairIdx X k →₀ ZMod 2) :
    pairSwap X k y = Finsupp.mapDomain pairIdxSwap y := rfl

@[simp] theorem pairSwap_single (X : TopCat.{0}) (k : ℕ)
    (q : Steenrod.PairIdx X k) (c : ZMod 2) :
    pairSwap X k (Finsupp.single q c) = Finsupp.single (pairIdxSwap q) c := by
  rw [pairSwap_apply, Finsupp.mapDomain_single]

theorem pairSwap_mul_self (X : TopCat.{0}) (k : ℕ) :
    pairSwap X k * pairSwap X k = 1 := by
  apply LinearMap.ext
  intro y
  show pairSwap X k (pairSwap X k y) = y
  rw [pairSwap_apply, pairSwap_apply, ← Finsupp.mapDomain_comp]
  have h : (pairIdxSwap ∘ pairIdxSwap :
      Steenrod.PairIdx X k → Steenrod.PairIdx X k) = id :=
    funext fun q => pairIdxSwap_involutive q
  rw [h, Finsupp.mapDomain_id]

/-! ## 3. The group-ring module structure -/

/-- **The `Λ`-module structure of the target**: the generator acts by the factor
swap.  This is the structure the chain-map condition for `Φ` requires; the free
`Λ`-module on pairs is a different object and the condition is false there. -/
noncomputable abbrev pairModule (X : TopCat.{0}) (k : ℕ) :
    Module GroupRingZ2 (Steenrod.PairIdx X k →₀ ZMod 2) :=
  moduleOfInvolution (pairSwap X k) (pairSwap_mul_self X k)

theorem pairModule_gen_smul (X : TopCat.{0}) (k : ℕ)
    (y : Steenrod.PairIdx X k →₀ ZMod 2) :
    letI := pairModule X k
    groupRingGen • y = pairSwap X k y :=
  moduleOfInvolution_smul (pairSwap X k) (pairSwap_mul_self X k) y

/-- `(1 + t) · y = y + T y`: the shape in which the action meets the source's
differential. -/
theorem pairModule_one_add_gen_smul (X : TopCat.{0}) (k : ℕ)
    (y : Steenrod.PairIdx X k →₀ ZMod 2) :
    letI := pairModule X k
    (1 + groupRingGen) • y = y + pairSwap X k y := by
  letI := pairModule X k
  rw [add_smul, one_smul, pairModule_gen_smul]

end

end GroupApproximation.CharClass
