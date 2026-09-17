import Mathlib.GroupTheory.Solvable
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.Countable.Defs

/-!
# Induction along a solvable quotient by cyclic extensions and increasing unions

`non_mf_group_notes.tex`, proof of `thm:fixed-radical-membership`
(tex l. 1376--1378):

> Let `A` be Kharlampovich's finitely presented solvable group of derived
> length three with undecidable word problem.  It is amenable, so `C*_r(A)` is
> quasidiagonal [TWW] and embeds in a norm matrix corona, and `A` is MF.

The group-theoretic half of the Ozawa--Rørdam--Sato route to that step
("elementary amenable groups have quasidiagonal reduced group C*-algebras")
is an induction over the class of groups. This file proves that induction
for the groups the manuscript needs, with no analytic input.

Let `G` be a countable group, `L ⊴ G` a normal subgroup with `G ⧸ L` solvable,
and `Q` any predicate on subgroups of `G`. Suppose `Q` is

* closed under increasing unions (`IsSequentialUnionClosed`), and
* closed under adjoining one element that normalizes the subgroup
  (`IsCyclicExtensionClosed`): if `k H k⁻¹ = H` and `Q H`, then `Q (H ⊔ ⟨k⟩)`.

Then `Q L` implies `Q ⊤` (`of_isSolvable_quotient`). With `L = ⊥` this covers
every countable solvable group (`of_isSolvable`), for example Kharlampovich's
group (sibling lane NN03b). With `L` locally finite it covers the amenable
realized Clifford quotients, which are (locally finite)-by-metabelian
(sibling lane NN10b).

The proof never uses the structure of an abelian quotient. If `N ≤ M` and
every commutator of two elements of `M` lies in `N`, enumerate
`M = {m₀, m₁, …}` and put `H₀ = N`, `H_{i+1} = H_i ⊔ ⟨m_i⟩`. Every `m_i`
normalizes `H_i`, because `m h m⁻¹ = [m, h] h` and `[m, h] ∈ N ≤ H_i`.
Finally `M = ⨆ H_i`. Iterating this along the comapped derived series of
`G ⧸ L` gives the result.

`Q` is an honest parameter of an induction principle, not a stand-in for a
cited theorem. The intended instance is
`Q H := IsQuasidiagonalTrace (canonicalReducedTrace ↥H)`. For that instance the
two closure properties, the locally finite base case
(`isQuasidiagonalTrace_canonicalReduced_of_locallyFinite`) and the passage to
`IsOperatorMF` (`isOperatorMF_of_isQuasidiagonalCanonicalTrace`) are separate
theorems.
-/

namespace GroupApproximation.Full.TWW

open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

/-! ## The two closure properties -/

/-- A predicate on subgroups is closed under increasing sequential unions. -/
def IsSequentialUnionClosed (Q : Subgroup G → Prop) : Prop :=
  ∀ H : ℕ → Subgroup G, Monotone H → (∀ n, Q (H n)) → Q (⨆ n, H n)

/-- A predicate on subgroups is closed under adjoining one normalizing element.
Such an element `k` makes `H` normal in `H ⊔ ⟨k⟩` with cyclic quotient, so the
quotient is either finite cyclic or infinite cyclic. -/
def IsCyclicExtensionClosed (Q : Subgroup G → Prop) : Prop :=
  ∀ (H : Subgroup G) (k : G), (∀ h ∈ H, k * h * k⁻¹ ∈ H) →
    (∀ h ∈ H, k⁻¹ * h * k ∈ H) → Q H → Q (H ⊔ Subgroup.zpowers k)

/-! ## The cyclic chain -/

/-- The chain `H₀ = N`, `H_{i+1} = H_i ⊔ ⟨m_i⟩`. -/
def cyclicChain (N : Subgroup G) (m : ℕ → G) : ℕ → Subgroup G
  | 0 => N
  | i + 1 => cyclicChain N m i ⊔ Subgroup.zpowers (m i)

theorem cyclicChain_succ (N : Subgroup G) (m : ℕ → G) (i : ℕ) :
    cyclicChain N m (i + 1) = cyclicChain N m i ⊔ Subgroup.zpowers (m i) :=
  rfl

theorem cyclicChain_monotone (N : Subgroup G) (m : ℕ → G) :
    Monotone (cyclicChain N m) :=
  monotone_nat_of_le_succ fun i => by
    rw [cyclicChain_succ]
    exact le_sup_left

theorem le_cyclicChain (N : Subgroup G) (m : ℕ → G) (i : ℕ) :
    N ≤ cyclicChain N m i :=
  cyclicChain_monotone N m (Nat.zero_le i)

theorem cyclicChain_le {N M : Subgroup G} {m : ℕ → G} (hNM : N ≤ M)
    (hm : ∀ i, m i ∈ M) (i : ℕ) : cyclicChain N m i ≤ M := by
  induction i with
  | zero => exact hNM
  | succ i ih =>
    rw [cyclicChain_succ]
    exact sup_le ih (Subgroup.zpowers_le.mpr (hm i))

/-! ## Normalizing by commutator control -/

/-- If `N ≤ H ≤ M` and commutators of `M` lie in `N`, then every `k ∈ M`
conjugates `H` into itself: `k h k⁻¹ = [k, h] h`. -/
theorem conj_mem_of_commutator_mem {N H M : Subgroup G} (hNH : N ≤ H) (hHM : H ≤ M)
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) {k : G} (hk : k ∈ M)
    {h : G} (hh : h ∈ H) : k * h * k⁻¹ ∈ H := by
  have hc : k * h * k⁻¹ * h⁻¹ ∈ H := hNH (hcomm k hk h (hHM hh))
  have hprod : k * h * k⁻¹ * h⁻¹ * h ∈ H := mul_mem hc hh
  rwa [inv_mul_cancel_right (k * h * k⁻¹) h] at hprod

/-- The inverse conjugation, from the previous lemma at `k⁻¹`. -/
theorem inv_conj_mem_of_commutator_mem {N H M : Subgroup G} (hNH : N ≤ H) (hHM : H ≤ M)
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) {k : G} (hk : k ∈ M)
    {h : G} (hh : h ∈ H) : k⁻¹ * h * k ∈ H := by
  have hconj : k⁻¹ * h * k⁻¹⁻¹ ∈ H :=
    conj_mem_of_commutator_mem hNH hHM hcomm (inv_mem hk) hh
  rwa [inv_inv] at hconj

/-! ## Solvable quotients -/

/-- The derived series of `G ⧸ L`, pulled back to `G`. -/
def quotientDerivedComap (L : Subgroup G) [L.Normal] (i : ℕ) : Subgroup G :=
  (derivedSeries (G ⧸ L) i).comap (QuotientGroup.mk' L)

theorem mem_quotientDerivedComap (L : Subgroup G) [L.Normal] (i : ℕ) {x : G} :
    x ∈ quotientDerivedComap L i ↔ QuotientGroup.mk' L x ∈ derivedSeries (G ⧸ L) i :=
  Iff.rfl

theorem quotientDerivedComap_succ_le (L : Subgroup G) [L.Normal] (i : ℕ) :
    quotientDerivedComap L (i + 1) ≤ quotientDerivedComap L i := by
  intro x hx
  rw [mem_quotientDerivedComap] at hx ⊢
  exact derivedSeries_antitone (G ⧸ L) (Nat.le_add_right i 1) hx

theorem commutator_mem_quotientDerivedComap (L : Subgroup G) [L.Normal] (i : ℕ)
    {x y : G} (hx : x ∈ quotientDerivedComap L i) (hy : y ∈ quotientDerivedComap L i) :
    x * y * x⁻¹ * y⁻¹ ∈ quotientDerivedComap L (i + 1) := by
  rw [mem_quotientDerivedComap] at hx hy ⊢
  have hc := Subgroup.commutator_mem_commutator hx hy
  rw [commutatorElement_def] at hc
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, derivedSeries_succ]
  exact hc

theorem quotientDerivedComap_zero (L : Subgroup G) [L.Normal] :
    quotientDerivedComap L 0 = ⊤ := by
  show (derivedSeries (G ⧸ L) 0).comap (QuotientGroup.mk' L) = ⊤
  rw [derivedSeries_zero, Subgroup.comap_top]

theorem quotientDerivedComap_eq_of_derivedSeries_eq_bot (L : Subgroup G) [L.Normal]
    {d : ℕ} (hd : derivedSeries (G ⧸ L) d = ⊥) : quotientDerivedComap L d = L := by
  show (derivedSeries (G ⧸ L) d).comap (QuotientGroup.mk' L) = L
  rw [hd, MonoidHom.comap_bot, QuotientGroup.ker_mk']

/-! ## One step: from `N` to `M` when `[M, M] ⊆ N ≤ M` -/

variable [Countable G]

/-- **One induction step.** If `N ≤ M` and every commutator of two elements of
`M` lies in `N`, then `Q N` implies `Q M`. -/
theorem of_commutator_mem {Q : Subgroup G → Prop} (hunion : IsSequentialUnionClosed Q)
    (hcyc : IsCyclicExtensionClosed Q) {N M : Subgroup G} (hNM : N ≤ M)
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) (hN : Q N) : Q M := by
  have hex : ∃ m : ℕ → G, (∀ i, m i ∈ M) ∧ ∀ x ∈ M, ∃ i, m i = x := by
    haveI : Nonempty (↥M) := ⟨1⟩
    obtain ⟨f, hf⟩ := exists_surjective_nat (↥M)
    refine ⟨fun i => (f i : G), fun i => (f i).2, fun x hx => ?_⟩
    obtain ⟨i, hi⟩ := hf ⟨x, hx⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  obtain ⟨m, hm, hsurj⟩ := hex
  have hle : ∀ i, cyclicChain N m i ≤ M := cyclicChain_le hNM hm
  have hQ : ∀ i, Q (cyclicChain N m i) := by
    intro i
    induction i with
    | zero => exact hN
    | succ i ih =>
      show Q (cyclicChain N m i ⊔ Subgroup.zpowers (m i))
      exact hcyc (cyclicChain N m i) (m i)
        (fun _ hh => conj_mem_of_commutator_mem (le_cyclicChain N m i) (hle i) hcomm
          (hm i) hh)
        (fun _ hh => inv_conj_mem_of_commutator_mem (le_cyclicChain N m i) (hle i) hcomm
          (hm i) hh)
        ih
  have hsup : (⨆ i, cyclicChain N m i) = M := by
    refine le_antisymm (iSup_le hle) ?_
    intro x hx
    obtain ⟨i, rfl⟩ := hsurj x hx
    have hmem : m i ∈ cyclicChain N m (i + 1) := by
      rw [cyclicChain_succ]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (m i))
    exact Subgroup.mem_iSup_of_mem (i + 1) hmem
  rw [← hsup]
  exact hunion (cyclicChain N m) (cyclicChain_monotone N m) hQ

/-- **Descending a commutator series.** If `S (i+1) ≤ S i`, commutators of
`S i` lie in `S (i+1)`, and `Q (S d)`, then `Q (S 0)`. -/
theorem of_commutator_series {Q : Subgroup G → Prop} (hunion : IsSequentialUnionClosed Q)
    (hcyc : IsCyclicExtensionClosed Q) (S : ℕ → Subgroup G) (d : ℕ)
    (hS : ∀ i, S (i + 1) ≤ S i)
    (hcomm : ∀ i, ∀ x ∈ S i, ∀ y ∈ S i, x * y * x⁻¹ * y⁻¹ ∈ S (i + 1))
    (hbase : Q (S d)) : Q (S 0) := by
  have key : ∀ k i : ℕ, i + k = d → Q (S i) := by
    intro k
    induction k with
    | zero =>
      intro i hi
      obtain rfl : i = d := by omega
      exact hbase
    | succ k ih =>
      intro i hi
      exact of_commutator_mem hunion hcyc (hS i) (hcomm i) (ih (i + 1) (by omega))
  exact key d 0 (Nat.zero_add d)

/-! ## The induction theorems -/

/-- **Induction along a solvable quotient.** Let `Q` be closed under
increasing unions and normalizing cyclic extensions, and let `L ⊴ G` with
`G ⧸ L` solvable. Then `Q L` implies `Q ⊤`.

Manuscript use: `thm:fixed-radical-membership`, `non_mf_group_notes.tex`
l. 1376--1378 (the TWW step, for a solvable group) and the amenable Clifford
quotient (locally finite normal `L`, metabelian quotient). -/
theorem of_isSolvable_quotient {Q : Subgroup G → Prop} (hunion : IsSequentialUnionClosed Q)
    (hcyc : IsCyclicExtensionClosed Q) (L : Subgroup G) [L.Normal]
    [hsol : IsSolvable (G ⧸ L)] (hL : Q L) : Q ⊤ := by
  obtain ⟨⟨d, hd⟩⟩ := hsol
  have hbase : Q (quotientDerivedComap L d) := by
    rw [quotientDerivedComap_eq_of_derivedSeries_eq_bot L hd]
    exact hL
  have h0 := of_commutator_series hunion hcyc (quotientDerivedComap L) d
    (quotientDerivedComap_succ_le L)
    (fun i _ hx _ hy => commutator_mem_quotientDerivedComap L i hx hy) hbase
  rwa [quotientDerivedComap_zero] at h0

/-- **Induction over a countable solvable group.** A predicate closed under
increasing unions and normalizing cyclic extensions that holds at `⊥` holds at
`⊤`. -/
theorem of_isSolvable {Q : Subgroup G → Prop} (hunion : IsSequentialUnionClosed Q)
    (hcyc : IsCyclicExtensionClosed Q) [IsSolvable G] (hbot : Q ⊥) : Q ⊤ :=
  of_isSolvable_quotient hunion hcyc ⊥ hbot

end GroupApproximation.Full.TWW
