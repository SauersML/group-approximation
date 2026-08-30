import GroupApproximation.GGT.ElementaryOsinSNormal
import GroupApproximation.Manuscript.NonMF.AcylindricallyHyperbolic

/-!
# Hull's `K_G(S)`, in the one direction his `yi` consumes

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, Lemma
`K(S)`: for a non-elementary `S`, the intersection of the elementary closures
of the loxodromic elements of `S` is **the maximal finite subgroup of `G`
normalised by `S`**; consequently `S` is suitable if and only if that
intersection is trivial.

**Only one direction is built here, and that is deliberate.**  Hull's lemma has
two halves and `yi` consumes one of them:

* *this file* — the intersection is finite, is normalised by `S`, and is
  therefore **trivial when `S` is suitable**;
* *not built* — maximality, that every `S`-normalised finite subgroup lies
  inside it.  That half needs "a finite subgroup normalised by `⟨h⟩` is
  centralised by some power of `h`", i.e. finiteness of the automorphism group
  of a finite group and a pigeonhole on the conjugation action, and **nothing
  downstream asks for it**.

Dropping it also drops Hull's `ℒ_S` and his `E⁺` — the orientation-preserving
elementary closure — neither of which this repository has.  `loxRadical` below
intersects over *all* loxodromic elements of `S` rather than over `ℒ_S`, which
makes it a smaller subgroup and the triviality conclusion correspondingly
weaker; that is all `yi` needs, and it costs no new vocabulary.

## What `yi` actually consumes

`eq_one_of_mem_elementaryClosure_of_suitable`: over a suitable `S`, an element
lying in the elementary closure of **every** loxodromic element of `S` is the
identity.  In `yi` that element is the label `c` of the connecting edge, shown
to lie in `E(f₁) ∩ … ∩ E(f_k)`; here it is asked to lie in all of them, which is
the form that needs no choice of the family and so can be proved before the
family exists.

## Where the two hypotheses come from

`ElementaryClosureVirtuallyCyclic` is carried as a leading binder rather than as
a named leaf: it is Osin's Theorem 6.8 in the form
`GGT.Elementary.not_infinite_le_inf_elementaryClosure` consumes, and that lemma
— **proved** — is what makes the radical finite.  Note that this route needs no
hyperbolic embedding, so this file is independent of Hull's `heGX`; the finite
intersection comes from the two independent loxodromics that `Suitable` already
supplies.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.GGT.Elementary
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

variable {G : Type u} [Group G]

/-- **The loxodromic radical of `S`**: the intersection of the elementary
closures of the loxodromic elements of `S`.  This is Hull's `K_G(S)` with the
intersection taken over every loxodromic element rather than over his `ℒ_S`. -/
def loxRadical (A : Alphabet G) (S : Subgroup G) : Subgroup G :=
  ⨅ h : {h : G // h ∈ S ∧ IsLoxodromic h (Cayley.base A)}, elementaryClosure (h : G)

theorem mem_loxRadical {A : Alphabet G} {S : Subgroup G} {x : G} :
    x ∈ loxRadical A S ↔
      ∀ h : G, h ∈ S → IsLoxodromic h (Cayley.base A) →
        x ∈ elementaryClosure h := by
  constructor
  · intro hx h hS hlox
    exact Subgroup.mem_iInf.mp hx ⟨h, hS, hlox⟩
  · intro hx
    refine Subgroup.mem_iInf.mpr ?_
    intro h
    exact hx (h : G) h.2.1 h.2.2

/-- The radical sits inside each closure it is built from. -/
theorem loxRadical_le {A : Alphabet G} {S : Subgroup G} {h : G} (hS : h ∈ S)
    (hlox : IsLoxodromic h (Cayley.base A)) :
    loxRadical A S ≤ elementaryClosure h :=
  fun _ hx => mem_loxRadical.mp hx h hS hlox

/-- **The radical is normalised by `S`.**  The loxodromic elements of `S` are
closed under conjugation by `S`, and `E(·)` is equivariant, so conjugating a
member of every closure lands in every closure again. -/
theorem conj_mem_loxRadical {A : Alphabet G} {S : Subgroup G} {g x : G}
    (hg : g ∈ S) (hx : x ∈ loxRadical A S) :
    g * x * g⁻¹ ∈ loxRadical A S := by
  refine mem_loxRadical.mpr ?_
  intro h hhS hhlox
  have hconjS : g⁻¹ * h * g ∈ S := mul_mem (mul_mem (inv_mem hg) hhS) hg
  have hconjlox : IsLoxodromic (g⁻¹ * h * g) (Cayley.base A) := by
    have hc := isLoxodromic_conj (isIsometricAction_cayley A) (a := g⁻¹) hhlox
    rwa [inv_inv] at hc
  have hmem := mem_loxRadical.mp hx (g⁻¹ * h * g) hconjS hconjlox
  have hconj := mem_elementaryClosure_conj (a := g) hmem
  have heq : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
  rwa [heq] at hconj

/-- **The radical is finite.**  It lies inside the elementary closures of the
two independent loxodromics that `Suitable` supplies, and no infinite subgroup
lies in both. -/
theorem finite_loxRadical {A : Alphabet G} {S : Subgroup G}
    (hvc : ElementaryClosureVirtuallyCyclic G (Cayley.base A))
    (hS : Suitable A S) : ((loxRadical A S : Subgroup G) : Set G).Finite := by
  obtain ⟨a, haS, b, hbS, halox, hblox, hind⟩ := hS.actsNonElementarily
  by_contra hinf
  exact not_infinite_le_inf_elementaryClosure (isIsometricAction_cayley A) hvc
    halox hblox hind (loxRadical_le haS halox) (loxRadical_le hbS hblox) hinf

/-- **Hull's Lemma `K(S)`, in the direction `yi` uses it**: over a suitable
subgroup the radical is trivial.  It is finite and `S`-normalised, and
suitability is exactly that no such subgroup is nontrivial. -/
theorem loxRadical_eq_bot_of_suitable {A : Alphabet G} {S : Subgroup G}
    (hvc : ElementaryClosureVirtuallyCyclic G (Cayley.base A))
    (hS : Suitable A S) : loxRadical A S = ⊥ :=
  hS.normalizesNoNontrivialFinite (loxRadical A S)
    (finite_loxRadical hvc hS).to_subtype
    (fun _ hs _ hx => conj_mem_loxRadical hs hx)

/-- **The form `yi` consumes.**  Over a suitable `S`, an element lying in the
elementary closure of every loxodromic element of `S` is the identity.

In `yi` this is applied to the label of the edge joining the two `ε`-close
paths, which the commuting argument places in `E(f₁) ∩ … ∩ E(f_k)`. -/
theorem eq_one_of_mem_elementaryClosure_of_suitable {A : Alphabet G}
    {S : Subgroup G} (hvc : ElementaryClosureVirtuallyCyclic G (Cayley.base A))
    (hS : Suitable A S) {c : G}
    (hc : ∀ h : G, h ∈ S → IsLoxodromic h (Cayley.base A) →
      c ∈ elementaryClosure h) : c = 1 := by
  have hmem : c ∈ loxRadical A S := mem_loxRadical.mpr hc
  rw [loxRadical_eq_bot_of_suitable hvc hS, Subgroup.mem_bot] at hmem
  exact hmem

end HullSC
end GroupApproximation
