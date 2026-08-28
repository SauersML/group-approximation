import GroupApproximation.GGT.ElementaryMorseAlphabet
import GroupApproximation.GGT.ElementaryOsinNormalClosed
import GroupApproximation.GGT.PingPongFreeSubgroup
import GroupApproximation.GGT.WPDElement
import GroupApproximation.GGT.WPDHyperbolicallyEmbedded

/-!
# Osin's Theorem 1.2: from a WPD element to the Cayley-graph definition

Minasyan--Osin's tree criterion (*Acylindrical hyperbolicity of groups acting
on trees*, Theorem 2.1) produces its conclusion through one citation, their
Theorem 3.3, which is Osin, *Acylindrically hyperbolic groups*, Trans. Amer.
Math. Soc. 368 (2016), Theorem 1.2:

> For any group `G` the following conditions are equivalent.
> * `(AH₁)` There exists a generating set `X` of `G` such that the
>   corresponding Cayley graph `Γ(G,X)` is hyperbolic, `|∂Γ(G,X)| > 2`, and
>   the natural action of `G` on `Γ(G,X)` is acylindrical.
> * `(AH₂)` `G` admits a non-elementary acylindrical action on a hyperbolic
>   space.
> * `(AH₃)` `G` is not virtually cyclic and admits an action on a hyperbolic
>   space such that at least one element of `G` is loxodromic and satisfies
>   the WPD condition.
> * `(AH₄)` `G` contains a proper infinite hyperbolically embedded subgroup.

`(AH₁)` is the repository's `TorsionFree.IsAcylindricallyHyperbolic`, with
`|∂Γ(G,X)| > 2` in the equivalent form `ActsNonElementarily` that Osin's
Theorem 1.1 licenses for acylindrical actions; `(AH₃)` is `AH3Data` together
with `¬ IsVirtuallyCyclic`; `(AH₄)` is `GGT.IsHypEmbedded`.  Osin records the
routing himself: "*It immediately follows from definitions that
`(AH₁) ⟹ (AH₂) ⟹ (AH₃)`.  The implication `(AH₃) ⟹ (AH₄)` is non-trivial and
was proved in [Dahmani--Guirardel--Osin].  Thus we only need to prove that
`(AH₄) ⟹ (AH₁)`.  In fact, we prove a stronger statement, Theorem 5.4*".  So
the implication the manuscript needs, `(AH₃) ⇒ (AH₁)`, factors as

* `(AH₃) ⇒ (AH₄)`: Dahmani--Guirardel--Osin, Mem. Amer. Math. Soc. 245 (2017)
  — a loxodromic WPD element lies in a virtually cyclic hyperbolically embedded
  subgroup.  This is `(L₃) ⇒ (L₄)` of Osin's own Theorem 1.4, which he
  attributes to that paper; here it is `DGOTheorem68`.
* `(AH₄) ⇒ (AH₁)`: Osin, Theorem 5.4, here `OsinTheorem54`, together with his
  Lemma 5.12, here `RelativeCayleyNonElementary`.  Lemma 5.12 is in turn
  assembled by `relativeCayleyNonElementary_of` from `DGOCorollary612`,
  `DGOTheorem614`, and the two facts of Osin's §6 that `GGT.Elementary`
  records.  Its appeal to Osin's Theorem 1.1 is *proved* here, not cited.

`osinAH4ToAH1_of` proves `OsinAH4ToAH1` from Theorem 5.4 and Lemma 5.12, and
`osinTheorem12_of` assembles `OsinTheorem12`.  Nothing in this development
inhabits the named literature propositions, and exactly four remain:
`DGOTheorem68`, `OsinTheorem54`, `DGOCorollary612` and `DGOTheorem614`.  The
two facts of Osin's §6 that the argument rests on are no longer among them —
`ElementaryMorse.independentOfNoCommonZpow_cayley_of_hyperbolic` and
`centralizerOrbitNearAxis_cayley_of_hyperbolic` prove them at a bare alphabet
from hyperbolicity and acylindricity alone, with no non-elementarity in their
hypotheses, which is what lets this file consume them upstream of the
non-elementarity it is proving.

## What is proved

* `exists_ah3Data_of_isAcylindricallyHyperbolic` — the **converse**
  implication `(AH₁) ⇒ (AH₃)`, in full: the Cayley graph of an acylindrically
  hyperbolic group is a hyperbolic space on which some element is loxodromic
  and, by `isWPDAt_of_isAcylindrical`, WPD.  So the `(AH₃)` interface is not
  vacuous, and the named propositions above are the only debt.
* `osinAH4ToAH1_of` — `(AH₄) ⇒ (AH₁)` from Osin's Theorem 5.4 and his
  Lemma 5.12, the last step being a definitional unpacking of the Cayley-graph
  form.
* `relativeCayleyNonElementary_of` — Lemma 5.12 from the results its own proof
  cites, so that the non-elementarity clause is no longer a citation in its own
  right.
* `exists_notMem_elementaryClosure_of_no_common_power` — `E(g)` is a proper
  subgroup as soon as some pair of elements has no common nonzero power.
* `actsNonElementarily_of_no_common_power` — **the exclusion step of Osin's
  Theorem 1.1, proved**: a loxodromic element and a common-power-free pair give
  two independent loxodromics, namely `g` and its conjugate by an element
  outside `E(g)`.
* `infinite_zpowers_of_not_isOfFinOrder` — an element of infinite order
  generates an infinite cyclic subgroup.
* `infinite_of_mem_of_isLoxodromic` — a subgroup containing a loxodromic
  element is infinite, so the infinitude clause of `(AH₄)` is derived from the
  loxodromy `AH3Data` already records rather than asked of the citation.
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

/-- **A subgroup containing a loxodromic element is infinite.**  A loxodromic
element has infinite order (`HullGeometry.not_isOfFinOrder_of_isLoxodromic`), so
its integer powers are pairwise distinct and all lie in the subgroup.

This discharges the infinitude clause of `(AH₄)` from the loxodromy already
recorded in `AH3Data`, so `DGOTheorem68` below does not have to carry it: the
citation is asked for strictly less. -/
theorem infinite_of_mem_of_isLoxodromic {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] {g : G} {x : X}
    (hlox : IsLoxodromic g x) {E : Subgroup G} (hg : g ∈ E) :
    (E : Set G).Infinite := by
  have hinj : Function.Injective (fun n : ℤ => g ^ n) :=
    injective_zpow_iff_not_isOfFinOrder.mpr
      (not_isOfFinOrder_of_isLoxodromic hlox)
  exact Set.infinite_of_injective_forall_mem hinj fun n => Subgroup.zpow_mem E hg n

/-- **Packaging an `(AH₃)` witness.**  The structure's `Space` field carries its
own universe parameter, so the universe has to be chosen where the witness is
built; this constructor is that choice, made once, with the instances taken as
ordinary binders rather than left to synthesis at the call site.

It consumes the three conclusions of an equivariant additive-distortion
transfer directly: given `h : IsHyperbolicSpace δ X ∧ IsLoxodromic g x ∧
IsWPDAt g x`, the witness is `AH3Data.ofData X hiso δ h.1 g x h.2.1 h.2.2`. -/
def AH3Data.ofData {G : Type u} [Group G] (X : Type v) [PseudoMetricSpace X]
    [MulAction G X] (hiso : IsIsometricAction G X) (δ : ℝ)
    (hδ : IsHyperbolicSpace δ X) (g : G) (x : X) (hlox : IsLoxodromic g x)
    (hwpd : IsWPDAt g x) : AH3Data.{u, v} G where
  Space := X
  isometric := hiso
  delta := δ
  hyperbolic := hδ
  elt := g
  base := x
  loxodromic := hlox
  wpd := hwpd

/-! ## The literature inputs -/

/-- **`(AH₃) ⇒ (AH₄)`: Dahmani--Guirardel--Osin, Theorem 6.8.**  The number is
Osin's own: his proof of Theorem 1.2 reads *"the implication
`(AH₃) ⟹ (AH₄)` was proved in [DGO, Theorem 6.8]"*.  He also states it per
element, as `(L₃) ⇒ (L₄)` of his Theorem 1.4:

> `(L₃)` There exists an action of `G` on a hyperbolic space such that `g` acts
>   loxodromically and satisfies the WPD condition.
> `(L₄)` The order of `g` is infinite and `g` is contained in a virtually
>   cyclic hyperbolically embedded subgroup of `G`.

Two clauses of `(L₄)` are dropped rather than asked for.  Infinitude of the
subgroup is derived from loxodromy by `infinite_of_mem_of_isLoxodromic`;
virtual cyclicity is used only to make the subgroup proper, and properness is
asked for directly.  So this proposition asks the literature for strictly less
than `(AH₄)` consumes. -/
def DGOTheorem68 : Prop :=
  ∀ (G : Type u) [Group G] (D : AH3Data G), ¬ IsVirtuallyCyclic G →
    ∃ E : Subgroup G, D.elt ∈ E ∧ E ≠ ⊤ ∧ IsHypEmbedded G E

/-- **Osin, Theorem 1.2, the implication `(AH₄) ⇒ (AH₁)`**: a proper infinite
hyperbolically embedded subgroup makes `G` acylindrically hyperbolic.  Osin
proves it in §5 of *Acylindrically hyperbolic groups* through his Theorem 5.4,
which is stated separately below and is what this proposition is assembled
from. -/
def OsinAH4ToAH1 : Prop :=
  ∀ (G : Type u) [Group G] (E : Subgroup G), E ≠ ⊤ → (E : Set G).Infinite →
    IsHypEmbedded G E → IsAcylindricallyHyperbolic G

/-- **Osin, *Acylindrically hyperbolic groups*, Theorem 5.4**, verbatim:

> Let `G` be a group, `{H_λ}_{λ∈Λ}` a finite collection of subgroups of `G`,
> `X` a subset of `G`.  Suppose that `{H_λ}_{λ∈Λ} ↪_h (G,X)`.  Then there
> exists `Y ⊆ G` such that `X ⊆ Y` and the following conditions hold.
> (a) `{H_λ}_{λ∈Λ} ↪_h (G,Y)`.  In particular, the Cayley graph
>     `Γ(G, Y ⊔ H)` is hyperbolic.
> (b) The action of `G` on `Γ(G, Y ⊔ H)` is acylindrical.

**The enlargement of `X` to `Y` is not a convenience, it is necessary**, and
this is why no proposition here asserts that `G` acts acylindrically on
`Γ(G, X ⊔ H)` itself.  Osin gives the counterexample immediately before
Theorem 5.4: for `G = (K × ℤ) * H` with `K` infinite and `H` nontrivial, and
`X = K ∪ {x}` with `x` a generator of `ℤ`, one has `H ↪_h (G,X)` while the
action on `Γ(G, X ⊔ H)` is *not* acylindrical — every element of `K` moves
every vertex of the ray labelled by the positive powers of `x` a distance at
most `1`.  Enlarging to `Y = K × ℤ` repairs it, and `Γ(G, Y ⊔ H)` is then
quasi-isometric to the Bass--Serre tree of the free product.

Clause (a) is `D'.IsHyperbolicallyEmbedded`, whose own first field is the
hyperbolicity of `Γ(G, Y ⊔ H)`; clause (b) is the acylindricity of the
translation action on that Cayley graph. -/
def OsinTheorem54 : Prop :=
  ∀ (G : Type u) [Group G] (D : RelGenSet G Unit), D.IsHyperbolicallyEmbedded →
    ∃ D' : RelGenSet G Unit, D.base ⊆ D'.base ∧ D'.fam = D.fam ∧
      D'.IsHyperbolicallyEmbedded ∧ IsAcylindrical G (Cayley D'.alphabet)

/-- **A non-degenerate subgroup**, in Osin's and Dahmani--Guirardel--Osin's
sense: `H ↪_h G` holds trivially for `H = G` (take `X = ∅`) and for finite `H`,
and those two cases are called *degenerate*.  Non-degenerate therefore means
proper and infinite — exactly the hypothesis of `(AH₄)`. -/
def IsNonDegenerate {G : Type u} [Group G] (H : Subgroup G) : Prop :=
  H ≠ ⊤ ∧ (H : Set G).Infinite

/-- **Osin, Lemma 5.12**, verbatim:

> Let `G` be a group, `H` a subgroup of `G`, `X` a subset of `G`.  Suppose that
> `H` is non-degenerate and `H ↪_h (G,X)`.  Then the action of `G` on
> `Γ(G, X ⊔ H)` is non-elementary.

This is the clause of `(AH₄) ⇒ (AH₁)` that Theorem 5.4 does not supply; Osin's
proof of Theorem 1.2 applies it to the generating set Theorem 5.4 produces.

Two remarks on the translation.  Osin's conclusion is `|∂Γ| > 2`; this
repository has no Gromov boundary, and what is recorded here is
`ActsNonElementarily`, *two independent loxodromic elements*.  Under the
acylindricity hypothesis the two are equivalent by Osin's Theorem 1.1, and two
independent loxodromics is what his proof actually produces.  That hypothesis
is *added* rather than dropped — the assembly never uses this proposition
without it — which makes this statement weaker than the printed lemma, hence a
safe citation. -/
def RelativeCayleyNonElementary : Prop :=
  ∀ (G : Type u) [Group G] (D : RelGenSet G Unit), D.IsHyperbolicallyEmbedded →
    IsAcylindrical G (Cayley D.alphabet) → IsNonDegenerate (D.fam ()) →
      ActsNonElementarily (⊤ : Subgroup G) (Cayley.base D.alphabet)

/-! ### The two results Lemma 5.12's proof cites -/

/-- **Dahmani--Guirardel--Osin, Corollary 6.12**, as Osin's Lemma 5.12 cites
it: a non-degenerate hyperbolically embedded subgroup makes `G` contain
elements acting loxodromically on `Γ(G, X ⊔ H)`.

No such element lies in `H` itself: by
`RelGenSet.not_isLoxodromic_of_mem_fam`, coning off `H` makes every element of
`H` elliptic.  So this citation is a statement about the rest of `G`. -/
def DGOCorollary612 : Prop :=
  ∀ (G : Type u) [Group G] (D : RelGenSet G Unit), D.IsHyperbolicallyEmbedded →
    IsNonDegenerate (D.fam ()) →
      ∃ g : G, IsLoxodromic g (Cayley.base D.alphabet)

/-- **Dahmani--Guirardel--Osin, Theorem 6.14**, in the form Osin's Lemma 5.12
uses it: *"by Theorem 6.14 from [DGO] `G` contains non-abelian free subgroups.
In particular, `G` is not virtually cyclic."*

Recorded verbatim, as the free subgroup: `PingPong.FreeRankTwo G` is an
injective `FreeGroup (Fin 2) →* G`.  The pair of elements with no common
nonzero power that the argument below consumes is extracted from it by
`PingPong.exists_noCommonZpow_of_freeRankTwo`, and Osin's own "in particular,
`G` is not virtually cyclic" comes back from the same pair through
`not_isVirtuallyCyclic_of_no_common_power`.  Neither derivation belongs in the
citation, so the citation states what the theorem states. -/
def DGOTheorem614 : Prop :=
  ∀ (G : Type u) [Group G] (D : RelGenSet G Unit), D.IsHyperbolicallyEmbedded →
    IsNonDegenerate (D.fam ()) → PingPong.FreeRankTwo G

/-! ### The elementary closure supplies the exclusion Osin's Theorem 1.1 makes

Osin's Lemma 5.12 finishes through his Theorem 1.1 — the trichotomy for
acylindrical actions — to pass from "a loxodromic exists and `G` is not
virtually cyclic" to non-elementarity.  That step does not have to be a
citation here.  The two facts of Osin's §6 it rests on —
`Elementary.IndependentOfNoCommonZpow` (Lemma 6.5 and Corollary 6.6) and
`Elementary.CentralizerOrbitNearAxis` — are theorems at a bare alphabet, and
the passage from them to two independent loxodromics is proved below.  Neither
Osin's Theorem 6.8 nor Bowditch's dichotomy is needed: only the elementwise
half of 6.8 is, and that is
`Elementary.exists_common_zpow_of_mem_elementaryClosure_of_infiniteOrder'`.
Nothing here restates any of them. -/

/-- The cyclic subgroup generated by an element of infinite order is infinite. -/
theorem infinite_zpowers_of_not_isOfFinOrder {G : Type u} [Group G] {a : G}
    (ha : ¬ IsOfFinOrder a) :
    ((Subgroup.zpowers a : Subgroup G) : Set G).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℤ => a ^ n)
    (injective_zpow_iff_not_isOfFinOrder.mpr ha) ?_
  intro n
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩

/-- **The elementary closure of a loxodromic element is proper**, as soon as
some pair of elements has no common nonzero power.

If every element lay in `E(g)` then both cyclic subgroups `⟨a⟩` and `⟨b⟩` would
lie in `E(g)`; both are generated by an element of infinite order, because a
common-power-free pair has both entries of infinite order; so the elementwise
half of Osin's Theorem 6.8 puts a nonzero power of `g` inside each, say
`a ^ m = g ^ j` and `b ^ n = g ^ k` with `j, k ≠ 0`.  Then
`a ^ (m k) = g ^ (j k) = b ^ (n j)`, and the pair forbids it unless `m = 0` —
which would make `g ^ j = 1` for `j ≠ 0`, impossible for a loxodromic.

**Neither Theorem 6.8 nor Bowditch's dichotomy is used.**  Only the elementwise
half of 6.8 is needed — an infinite-order element of `E(g)` shares a nonzero
power with `g` — and
`Elementary.exists_common_zpow_of_mem_elementaryClosure_of_infiniteOrder'`
proves it from the centralizer theorem alone: the element's square commutes
with a nonzero power of `g` and still has infinite order, so it is loxodromic
by `Elementary.isLoxodromic_of_commute_of_orbitNearAxis`, and the centralizer
theorem supplies the common power.  The finite-index half of 6.8 — an
*arbitrary* infinite subgroup of `E(g)` meeting `⟨g⟩` — is what would need the
torsion of `E(g)` to be finite, and nothing here asks for it.

What remains is `CentralizerOrbitNearAxis`, which the repository carries for
Osin's Lemma 7.1 in any case.  So this chain contributes no elementary-closure
leaf of its own. -/
theorem exists_notMem_elementaryClosure_of_no_common_power
    {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]
    {x : X} (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X)
    (hnear : Elementary.CentralizerOrbitNearAxis G x) {g : G}
    (hg : IsLoxodromic g x) {a b : G}
    (hab : ∀ m k : ℤ, a ^ m = b ^ k → m = 0 ∧ k = 0) :
    ∃ h : G, h ∉ Elementary.elementaryClosure g := by
  by_contra hall
  push_neg at hall
  have hafin : ¬ IsOfFinOrder a := by
    intro hfin
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    have h1 : a ^ (n : ℤ) = b ^ (0 : ℤ) := by
      rw [zpow_zero, zpow_natCast, hpow]
    have hz : (n : ℤ) = 0 := (hab (n : ℤ) 0 h1).1
    omega
  have hbfin : ¬ IsOfFinOrder b := by
    intro hfin
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    have h1 : a ^ (0 : ℤ) = b ^ (n : ℤ) := by
      rw [zpow_zero, zpow_natCast, hpow]
    have hz : (n : ℤ) = 0 := (hab 0 (n : ℤ) h1).2
    omega
  obtain ⟨j, m, -, hm, hea⟩ :=
    Elementary.exists_common_zpow_of_mem_elementaryClosure_of_infiniteOrder'
      hiso hacy hnear hg (hall a) hafin
  obtain ⟨k, n, hk, -, heb⟩ :=
    Elementary.exists_common_zpow_of_mem_elementaryClosure_of_infiniteOrder'
      hiso hacy hnear hg (hall b) hbfin
  have hkey : a ^ (m * k) = b ^ (n * j) := by
    rw [zpow_mul, ← hea, zpow_mul, ← heb, ← zpow_mul, ← zpow_mul, mul_comm j k]
  exact hm ((mul_eq_zero.mp (hab (m * k) (n * j) hkey).1).resolve_right hk)

/-- **Osin's Theorem 1.1 exclusion, proved rather than cited.**  A loxodromic
element together with a common-power-free pair gives two independent
loxodromics: `g` and its conjugate by an element outside `E(g)`. -/
theorem actsNonElementarily_of_no_common_power
    {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]
    {x : X} (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X)
    (hindep : Elementary.IndependentOfNoCommonZpow G x)
    (hnear : Elementary.CentralizerOrbitNearAxis G x) {g : G}
    (hg : IsLoxodromic g x) {a b : G}
    (hab : ∀ m k : ℤ, a ^ m = b ^ k → m = 0 ∧ k = 0) :
    ActsNonElementarily (⊤ : Subgroup G) x := by
  obtain ⟨h, hh⟩ :=
    exists_notMem_elementaryClosure_of_no_common_power hiso hacy hnear hg hab
  exact Elementary.actsNonElementarily_of_notMem_elementaryClosure hiso hindep
    (Subgroup.mem_top g) (Subgroup.mem_top h) hg hh

/-- **Osin's Lemma 5.12, assembled.**  His proof runs: loxodromic elements
exist by Dahmani--Guirardel--Osin's Corollary 6.12, non-abelian free subgroups
by their Theorem 6.14, and the trichotomy of Osin's Theorem 1.1 then leaves
only the non-elementary case.  The last step is
`actsNonElementarily_of_no_common_power`, which is proved from the two facts of
Osin's §6 that `GGT.Elementary` records, so the trichotomy is not carried here
as a citation of its own. -/
theorem relativeCayleyNonElementary_of (h612 : DGOCorollary612)
    (h614 : DGOTheorem614) : RelativeCayleyNonElementary := by
  intro G _ D hemb hacy hnd
  obtain ⟨δ, hδ⟩ := hemb.hyperbolic
  obtain ⟨g, hg⟩ := h612 G D hemb hnd
  obtain ⟨a, b, hab⟩ :=
    PingPong.exists_noCommonZpow_of_freeRankTwo (h614 G D hemb hnd)
  exact actsNonElementarily_of_no_common_power
    (isIsometricAction_cayley D.alphabet) hacy
    (ElementaryMorse.independentOfNoCommonZpow_cayley_of_hyperbolic
      D.alphabet hδ hacy)
    (ElementaryMorse.centralizerOrbitNearAxis_cayley_of_hyperbolic
      D.alphabet hδ) hg hab

/-- **`(AH₄) ⇒ (AH₁)` from Theorem 5.4 and the non-elementarity clause.**

The last step is a definitional unpacking: `IsAcylindricallyHyperbolic` is the
Cayley-graph form, and Theorem 5.4's `Y` supplies the alphabet, its clause (a)
the hyperbolicity, its clause (b) the acylindricity. -/
theorem osinAH4ToAH1_of (h54 : OsinTheorem54)
    (hne : RelativeCayleyNonElementary) : OsinAH4ToAH1 := by
  intro G _ E hE hinf hemb
  obtain ⟨_X, D, -, hfam, hhyp⟩ := hemb
  obtain ⟨D', -, hfam', hhyp', hacy⟩ := h54 G D hhyp
  obtain ⟨δ, hδ⟩ := hhyp'.hyperbolic
  have hlam : D'.fam () = E := by
    rw [hfam']
    exact congrFun hfam ()
  have hEne : D'.fam () ≠ ⊤ := by rw [hlam]; exact hE
  have hEinf : ((D'.fam () : Set G)).Infinite := by rw [hlam]; exact hinf
  exact ⟨⟨D'.alphabet, δ, hδ, hacy, hne G D' hhyp' hacy ⟨hEne, hEinf⟩⟩⟩

/-- **Osin, Theorem 1.2, the implication `(AH₃) ⇒ (AH₁)`** — the form
Minasyan--Osin cite as their Theorem 3.3. -/
def OsinTheorem12 : Prop :=
  ∀ (G : Type u) [Group G], AH3Data G → ¬ IsVirtuallyCyclic G →
    IsAcylindricallyHyperbolic G

/-- `(AH₃) ⇒ (AH₁)` is the composite of the two cited steps, with the
infinitude of `E(g)` supplied by loxodromy rather than by the citation. -/
theorem osinTheorem12_of (h68 : DGOTheorem68) (h4 : OsinAH4ToAH1) :
    OsinTheorem12 := by
  intro G _ D hnvc
  letI := D.metricSpace
  letI := D.mulAction
  obtain ⟨E, hmem, hne, hemb⟩ := h68 G D hnvc
  exact h4 G E hne (infinite_of_mem_of_isLoxodromic D.loxodromic hmem) hemb

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
