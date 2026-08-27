import GroupApproximation.GGT.WPDElement
import GroupApproximation.GGT.WPDHyperbolicallyEmbedded

/-!
# Osin's Theorem 1.2: from a WPD element to the Cayley-graph definition

Minasyan--Osin's tree criterion (*Acylindrical hyperbolicity of groups acting
on trees*, Theorem 2.1) produces its conclusion through one citation, their
Theorem 3.3, which is Osin, *Acylindrically hyperbolic groups*, Trans. Amer.
Math. Soc. 368 (2016), Theorem 1.2:

> For any group `G` the following conditions are equivalent.
> * `(AH₁)` `G` is acylindrically hyperbolic in the sense of Definition 1.1
>   (some generating set `X` makes `Γ(G,X)` hyperbolic and non-elementary and
>   the action acylindrical).
> * `(AH₂)` `G` admits a non-elementary acylindrical action on a hyperbolic
>   space.
> * `(AH₃)` `G` is not virtually cyclic and admits an action on a hyperbolic
>   space such that at least one element of `G` is loxodromic and satisfies
>   the WPD condition.
> * `(AH₄)` `G` contains a proper infinite hyperbolically embedded subgroup.

`(AH₁)` is the repository's `TorsionFree.IsAcylindricallyHyperbolic`, `(AH₃)` is
`AH3Data` together with `¬ IsVirtuallyCyclic`, and `(AH₄)` is
`GGT.IsHypEmbedded`.  The implication the manuscript needs is `(AH₃) ⇒ (AH₁)`,
which in the literature factors as

* `(AH₃) ⇒ (AH₄)`: Dahmani--Guirardel--Osin, Mem. Amer. Math. Soc. 245 (2017),
  Theorem 6.8 — a loxodromic WPD element `g` lies in a maximal virtually cyclic
  subgroup `E(g)` which is hyperbolically embedded in `G`; and
* `(AH₄) ⇒ (AH₁)`: Osin, Theorem 1.2, proved in §5 of that paper.

Both are stated here as named propositions, `DGOTheorem68` and `OsinAH4ToAH1`,
and `osinTheorem12_of` assembles `OsinTheorem12` from them.  Nothing in this
development inhabits either.

## What is proved

* `exists_ah3Data_of_isAcylindricallyHyperbolic` — the **converse**
  implication `(AH₁) ⇒ (AH₃)`, in full: the Cayley graph of an acylindrically
  hyperbolic group is a hyperbolic space on which some element is loxodromic
  and, by `isWPDAt_of_isAcylindrical`, WPD.  So the `(AH₃)` interface is not
  vacuous, and the two named propositions above are the only debt.
* `exists_zpow_eq_of_isVirtuallyCyclic` — in a virtually cyclic group every
  element has a positive power inside the cyclic subgroup of finite index.
* `not_isVirtuallyCyclic_of_no_common_power` — **the criterion consumers use**:
  two elements with no common nonzero power force `¬ IsVirtuallyCyclic`.  For a
  group containing a free subgroup of rank two — such as a double HNN extension
  containing its two stable letters — this discharges the non-virtual-cyclicity
  hypothesis of `(AH₃)` outright.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## Virtually cyclic groups -/

/-- **A virtually cyclic group**: some cyclic subgroup `⟨g⟩` has finite index,
i.e. finitely many right cosets `⟨g⟩x` cover `G`. -/
def IsVirtuallyCyclic (G : Type u) [Group G] : Prop :=
  ∃ (g : G) (F : Finset G), ∀ a : G, ∃ x ∈ F, ∃ m : ℤ, a = g ^ m * x

/-- **The pigeonhole consequence of finite index**: in a virtually cyclic group
every element has a positive power in the cyclic subgroup.  Among the powers
`a ^ 0, a ^ 1, …` two lie in the same coset of `⟨g⟩`, and their quotient is a
power of `g`. -/
theorem exists_zpow_eq_of_isVirtuallyCyclic {G : Type u} [Group G]
    (h : IsVirtuallyCyclic G) :
    ∃ g : G, ∀ a : G, ∃ (n : ℕ) (m : ℤ), 0 < n ∧ a ^ n = g ^ m := by
  classical
  obtain ⟨g, F, hF⟩ := h
  refine ⟨g, fun a => ?_⟩
  choose xa hxa ma hma using hF
  have key : ∀ p q : ℕ, p < q → xa (a ^ p) = xa (a ^ q) →
      ∃ (n : ℕ) (m : ℤ), 0 < n ∧ a ^ n = g ^ m := by
    intro p q hpq hx
    refine ⟨q - p, ma (a ^ q) - ma (a ^ p), Nat.sub_pos_of_lt hpq, ?_⟩
    have h1 : a ^ p = g ^ (ma (a ^ p)) * xa (a ^ p) := hma _
    have h2 : a ^ q = g ^ (ma (a ^ q)) * xa (a ^ q) := hma _
    have h3 : a ^ (q - p + p) = a ^ (q - p) * a ^ p := pow_add a (q - p) p
    rw [Nat.sub_add_cancel (le_of_lt hpq)] at h3
    calc a ^ (q - p)
        = a ^ q * (a ^ p)⁻¹ := by rw [h3, mul_inv_cancel_right]
      _ = g ^ (ma (a ^ q)) * xa (a ^ q) *
            (g ^ (ma (a ^ p)) * xa (a ^ p))⁻¹ := by rw [← h1, ← h2]
      _ = g ^ (ma (a ^ q) - ma (a ^ p)) := by rw [hx]; group
  obtain ⟨p, q, hpq, hval⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun n : ℕ => (⟨xa (a ^ n), hxa _⟩ : {y : G // y ∈ F}))
  rcases Nat.lt_or_ge p q with hlt | hge
  · exact key p q hlt (congrArg Subtype.val hval)
  · exact key q p (lt_of_le_of_ne hge (Ne.symm hpq))
      (congrArg Subtype.val hval).symm

/-- **Two elements with no common nonzero power make a group non-virtually
cyclic.**  This is the form in which the hypothesis of `(AH₃)` is discharged
for a group containing a free subgroup of rank two. -/
theorem not_isVirtuallyCyclic_of_no_common_power {G : Type u} [Group G]
    {a b : G} (hab : ∀ m k : ℤ, a ^ m = b ^ k → m = 0 ∧ k = 0) :
    ¬ IsVirtuallyCyclic G := by
  intro h
  obtain ⟨g, hg⟩ := exists_zpow_eq_of_isVirtuallyCyclic h
  obtain ⟨n, p, hn, hnp⟩ := hg a
  obtain ⟨n', q, hn', hnq⟩ := hg b
  have hnp' : a ^ ((n : ℤ)) = g ^ p := by
    rw [zpow_natCast]
    exact hnp
  have hnq' : b ^ ((n' : ℤ)) = g ^ q := by
    rw [zpow_natCast]
    exact hnq
  have hA : a ^ ((n : ℤ) * q) = g ^ (p * q) := by
    rw [zpow_mul, hnp', ← zpow_mul]
  have hB : b ^ ((n' : ℤ) * p) = g ^ (p * q) := by
    rw [zpow_mul, hnq', ← zpow_mul, mul_comm q p]
  obtain ⟨hq0, -⟩ := hab ((n : ℤ) * q) ((n' : ℤ) * p) (by rw [hA, hB])
  have hnpos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hn'pos : (0 : ℤ) < (n' : ℤ) := by exact_mod_cast hn'
  have hqz : q = 0 := by
    rcases mul_eq_zero.mp hq0 with h0 | h0
    · exact absurd h0 (ne_of_gt hnpos)
    · exact h0
  have hb1 : b ^ ((n' : ℤ)) = 1 := by
    rw [hnq', hqz, zpow_zero]
  have hfinal := hab 0 (n' : ℤ) (by rw [zpow_zero, hb1])
  exact absurd hfinal.2 (ne_of_gt hn'pos)

/-! ## `(AH₃)`: an action with a loxodromic WPD element -/

/-- **The data of Osin's condition `(AH₃)`**, apart from non-virtual-cyclicity:
an isometric action on a hyperbolic space with a distinguished element that is
loxodromic and satisfies the WPD condition.

This is the interface a Bass--Serre tree action is expected to produce: for the
double HNN extension of the manuscript, the tree, the element `u₁u₂⁻¹`, and the
base vertex. -/
structure AH3Data (G : Type u) [Group G] where
  /-- The hyperbolic space acted upon. -/
  Space : Type v
  [metricSpace : PseudoMetricSpace Space]
  [mulAction : MulAction G Space]
  /-- The action is by isometries. -/
  isometric : IsIsometricAction G Space
  /-- The hyperbolicity constant. -/
  delta : ℝ
  /-- The space is `delta`-hyperbolic in the four-point sense. -/
  hyperbolic : IsHyperbolicSpace delta Space
  /-- The distinguished element. -/
  elt : G
  /-- The basepoint. -/
  base : Space
  /-- The distinguished element is loxodromic. -/
  loxodromic : IsLoxodromic elt base
  /-- The distinguished element satisfies the WPD condition. -/
  wpd : IsWPDAt elt base

/-! ## The two literature inputs -/

/-- **Dahmani--Guirardel--Osin, Theorem 6.8**, in the form Osin's Theorem 1.2
uses it for `(AH₃) ⇒ (AH₄)`: a loxodromic WPD element of an action on a
hyperbolic space is contained in a hyperbolically embedded subgroup `E(g)`,
which is virtually cyclic — hence infinite, since a loxodromic element has
infinite order, and proper as soon as `G` is not virtually cyclic.

The properness and infinitude clauses are the trivial deductions from `E(g)`
being virtually cyclic and containing the loxodromic `g`; they are folded into
the statement so that the consumer needs nothing else. -/
def DGOTheorem68 : Prop :=
  ∀ (G : Type u) [Group G] (D : AH3Data.{u, v} G), ¬ IsVirtuallyCyclic G →
    ∃ E : Subgroup G, D.elt ∈ E ∧ E ≠ ⊤ ∧ (E : Set G).Infinite ∧
      IsHypEmbedded G E

/-- **Osin, Theorem 1.2, the implication `(AH₄) ⇒ (AH₁)`** (proved in §5 of
*Acylindrically hyperbolic groups*): a proper infinite hyperbolically embedded
subgroup produces a generating set for which the Cayley graph is hyperbolic,
the action acylindrical, and the group non-elementary. -/
def OsinAH4ToAH1 : Prop :=
  ∀ (G : Type u) [Group G] (E : Subgroup G), E ≠ ⊤ → (E : Set G).Infinite →
    IsHypEmbedded G E → IsAcylindricallyHyperbolic G

/-- **Osin, Theorem 1.2, the implication `(AH₃) ⇒ (AH₁)`** — the form
Minasyan--Osin cite as their Theorem 3.3. -/
def OsinTheorem12 : Prop :=
  ∀ (G : Type u) [Group G], AH3Data.{u, v} G → ¬ IsVirtuallyCyclic G →
    IsAcylindricallyHyperbolic G

/-- `(AH₃) ⇒ (AH₁)` is the composite of the two cited steps. -/
theorem osinTheorem12_of (h68 : DGOTheorem68) (h4 : OsinAH4ToAH1) :
    OsinTheorem12 := by
  intro G _ D hvc
  obtain ⟨E, _, hne, hinf, hemb⟩ := h68 G D hvc
  exact h4 G E hne hinf hemb

/-! ## The converse, proved -/

/-- **`(AH₁) ⇒ (AH₃)`, proved.**  An acylindrically hyperbolic group acts on
its Hull--Osin Cayley graph, which is hyperbolic; non-elementarity supplies a
loxodromic element, and acylindricity makes it WPD.

This is not needed by the manuscript's chain, but it certifies that the `(AH₃)`
interface above is the right one: it is exactly what the conclusion produces. -/
theorem exists_ah3Data_of_isAcylindricallyHyperbolic (G : Type u) [Group G]
    [h : IsAcylindricallyHyperbolic G] : Nonempty (AH3Data.{u, u} G) := by
  obtain ⟨A, δ, hδ, hacy, hne⟩ := h.out
  obtain ⟨g, _, _, _, hlox, _, _⟩ := hne
  exact ⟨{ Space := Cayley A
           isometric := isIsometricAction_cayley A
           delta := δ
           hyperbolic := hδ
           elt := g
           base := Cayley.base A
           loxodromic := hlox
           wpd := isWPDAt_of_isAcylindrical hacy hlox }⟩

end GGT
end GroupApproximation
