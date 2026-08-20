import GroupApproximation.Higman.Pinch

/-!
# The pinch lemma with a value attached, and the homomorphism it produces

The pinch lemma says where the subgroup `⟨Z, Qᵗ⟩` meets the base.  The rope
trick needs more: for `Z = Q = A` it needs the *homomorphism*

    τ : ⟨A, Aᵗ⟩ → T

which is a prescribed `φ : A → T` on `A` and trivial on `Aᵗ`.  Such a `τ`
exists exactly because `⟨A, Aᵗ⟩` is the free product of `A` and `Aᵗ`
amalgamated over `A ∩ M`, and this file proves what is needed of that without
constructing the amalgam: it attaches to every block word the value

    tau (a₀, [(c₁,a₁), …, (cₖ,aₖ)]) = φ a₀ · φ a₁ ⋯ φ aₖ

--- the `c`'s, which sit inside the conjugate, contribute nothing --- and
shows the value depends only on the element.

The reason it does is that both collapses of `Higman.Pinch` preserve it, and
that is exactly the hypothesis `φ` kills `A ∩ M`:

* the collapse of a block with `cᵢ ∈ M` inserts `cᵢ ∈ A ⊓ M` into the
  `a`-product, and `φ cᵢ = 1`;
* the collapse merging two blocks across `aᵢ ∈ M` deletes `aᵢ ∈ A ⊓ M` from
  the `a`-product, and again `φ aᵢ = 1`.

So the descent of `Higman.Pinch` runs unchanged with the value carried along,
and lands on `of y` with `φ y` the value.  In particular a block word equal
to `1` has value `1`, which is precisely the statement that the graph of the
values is the graph of a function.
-/

namespace GroupApproximation
namespace Higman
namespace Pinch

open HNNExtension

variable {P : Type} [Group P] (M A : Subgroup P)
  {T : Type} [Group T] (φ : ↥A →* T)

/-! ## 1.  Block data with entries in `A` -/

/-- The element of `A` recorded by a block. -/
def blockValue (p : ↥A × ↥A) : T := φ p.2

/-- The value attached to a block word: the product of the `A`-entries that
sit *outside* the conjugate. -/
def tau (a₀ : ↥A) (l : List (↥A × ↥A)) : T :=
  φ a₀ * ((l.map (blockValue A φ)).prod)

@[simp] theorem tau_nil (a₀ : ↥A) : tau A φ a₀ [] = φ a₀ := by
  unfold tau
  simp

theorem tau_cons (a₀ : ↥A) (p : ↥A × ↥A) (l : List (↥A × ↥A)) :
    tau A φ a₀ (p :: l) = φ a₀ * φ p.2 * ((l.map (blockValue A φ)).prod) := by
  unfold tau blockValue
  rw [List.map_cons, List.prod_cons, ← mul_assoc]

theorem tau_append (a₀ : ↥A) (l₁ l₂ : List (↥A × ↥A)) :
    tau A φ a₀ (l₁ ++ l₂)
      = φ a₀ * ((l₁.map (blockValue A φ)).prod) * ((l₂.map (blockValue A φ)).prod) := by
  unfold tau
  rw [List.map_append, List.prod_append, ← mul_assoc]

/-- The underlying block list, with the subgroup coercions forgotten. -/
def carrier (l : List (↥A × ↥A)) : List (P × P) :=
  l.map (fun p => ((p.1 : P), (p.2 : P)))

@[simp] theorem carrier_nil : carrier A ([] : List (↥A × ↥A)) = [] := rfl

@[simp] theorem carrier_cons (p : ↥A × ↥A) (l : List (↥A × ↥A)) :
    carrier A (p :: l) = ((p.1 : P), (p.2 : P)) :: carrier A l := rfl

theorem carrier_append (l₁ l₂ : List (↥A × ↥A)) :
    carrier A (l₁ ++ l₂) = carrier A l₁ ++ carrier A l₂ := by
  unfold carrier
  rw [List.map_append]

theorem length_carrier (l : List (↥A × ↥A)) : (carrier A l).length = l.length := by
  unfold carrier
  rw [List.length_map]

theorem mem_carrier_of_mem {p : ↥A × ↥A} {l : List (↥A × ↥A)} (hp : p ∈ l) :
    ((p.1 : P), (p.2 : P)) ∈ carrier A l := by
  unfold carrier
  exact List.mem_map.mpr ⟨p, hp, rfl⟩

/-- A splitting of the underlying list lifts to a splitting of the block
data. -/
theorem split_carrier : ∀ (l : List (↥A × ↥A)) (s₁ : List (P × P)) (p : P × P)
    (s₂ : List (P × P)), carrier A l = s₁ ++ p :: s₂ →
    ∃ (l₁ : List (↥A × ↥A)) (pv : ↥A × ↥A) (l₂ : List (↥A × ↥A)),
      l = l₁ ++ pv :: l₂ ∧ ((pv.1 : P), (pv.2 : P)) = p
  | [], s₁, p, s₂, h => by
      rw [carrier_nil] at h
      exact absurd h.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | pv :: l, [], p, s₂, h => by
      rw [carrier_cons, List.nil_append] at h
      injection h with hhead _
      exact ⟨[], pv, l, rfl, hhead⟩
  | pv :: l, s :: s₁, p, s₂, h => by
      rw [carrier_cons, List.cons_append] at h
      injection h with _ htail
      obtain ⟨l₁, pv', l₂, hl, hp⟩ := split_carrier l s₁ p s₂ htail
      exact ⟨pv :: l₁, pv', l₂, by rw [hl]; rfl, hp⟩

/-- The same for two consecutive entries. -/
theorem split_carrier₂ : ∀ (l : List (↥A × ↥A)) (s₁ : List (P × P))
    (p p' : P × P) (s₂ : List (P × P)), carrier A l = s₁ ++ p :: p' :: s₂ →
    ∃ (l₁ : List (↥A × ↥A)) (pv pv' : ↥A × ↥A) (l₂ : List (↥A × ↥A)),
      l = l₁ ++ pv :: pv' :: l₂ ∧ ((pv.1 : P), (pv.2 : P)) = p ∧
        ((pv'.1 : P), (pv'.2 : P)) = p'
  | [], s₁, p, p', s₂, h => by
      rw [carrier_nil] at h
      exact absurd h.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | pv :: l, [], p, p', s₂, h => by
      rw [carrier_cons, List.nil_append] at h
      injection h with hhead htail
      cases l with
      | nil =>
          rw [carrier_nil] at htail
          exact absurd htail.symm (List.cons_ne_nil _ _)
      | cons pv' l' =>
          rw [carrier_cons] at htail
          injection htail with hhead' _
          exact ⟨[], pv, pv', l', rfl, hhead, hhead'⟩
  | pv :: l, s :: s₁, p, p', s₂, h => by
      rw [carrier_cons, List.cons_append] at h
      injection h with _ htail
      obtain ⟨l₁, pva, pvb, l₂, hl, hpa, hpb⟩ := split_carrier₂ l s₁ p p' s₂ htail
      exact ⟨pv :: l₁, pva, pvb, l₂, by rw [hl]; rfl, hpa, hpb⟩

/-- The block word of block data with entries in `A`. -/
def wordA (a₀ : ↥A) (l : List (↥A × ↥A)) : CentHNN M :=
  word M (a₀ : P) (carrier A l)

theorem wordA_nil (a₀ : ↥A) : wordA M A a₀ [] = of (a₀ : P) := by
  unfold wordA
  rw [carrier_nil, word_nil]

theorem wordA_cons (a₀ : ↥A) (p : ↥A × ↥A) (l : List (↥A × ↥A)) :
    wordA M A a₀ (p :: l)
      = of (a₀ : P) * blockOf M ((p.1 : P), (p.2 : P)) *
          (((carrier A l).map (blockOf M)).prod) := by
  unfold wordA
  rw [carrier_cons, word_cons]

/-! ## 2.  The descent, carrying the value -/

/-- **The descent with the value carried.**  Same induction as
`Pinch.descent`, with the `a`-product tracked; both collapses change it only
by an element of `A ⊓ M`, which `φ` kills. -/
theorem descentTau (hφ : ∀ x : ↥A, (x : P) ∈ M → φ x = 1) :
    ∀ (n : ℕ) (a₀ : ↥A) (l : List (↥A × ↥A)), l.length ≤ n →
      wordA M A a₀ l ∈ (of : P →* CentHNN M).range →
      ∃ y : ↥A, wordA M A a₀ l = of (y : P) ∧ φ y = tau A φ a₀ l := by
  intro n
  induction n with
  | zero =>
      intro a₀ l hlen _
      have hnil : l = [] := by
        cases l with
        | nil => rfl
        | cons a t => simp at hlen
      subst hnil
      exact ⟨a₀, wordA_nil M A a₀, (tau_nil A φ a₀).symm⟩
  | succ n ih =>
      intro a₀ l hlen hmem
      by_cases hc : Clean M (carrier A l)
      · have hnil : carrier A l = [] :=
          eq_nil_of_clean M (a₀ : P) (carrier A l) hc hmem
        have hl : l = [] := by
          cases l with
          | nil => rfl
          | cons p l' => simp [carrier] at hnil
        subst hl
        exact ⟨a₀, wordA_nil M A a₀, (tau_nil A φ a₀).symm⟩
      · rcases exists_violation M (carrier A l) hc with
          ⟨s₁, q, z, s₂, heq, hqM⟩ | ⟨s₁, q, z, q', z', s₂, heq, hzM⟩
        · -- a block whose conjugated entry lies in `M`
          obtain ⟨l₁, pv, l₂, hl, hpv⟩ :=
            split_carrier A l s₁ (q, z) s₂ heq
          subst hl
          have hq : (pv.1 : P) = q := congrArg Prod.fst hpv
          have hz : (pv.2 : P) = z := congrArg Prod.snd hpv
          have hpvM : (pv.1 : P) ∈ M := by rw [hq]; exact hqM
          have hφpv : φ pv.1 = 1 := hφ pv.1 hpvM
          rcases eq_nil_or_append_singleton l₁ with rfl | ⟨l₁', p₀, rfl⟩
          · -- the block is the first one
            refine ?_
            have hrw : wordA M A a₀ ([] ++ pv :: l₂)
                = wordA M A (a₀ * pv.1 * pv.2) l₂ := by
              unfold wordA
              rw [List.nil_append, carrier_cons, word_cons,
                blockOf_of_mem M (pv.1 : P) (pv.2 : P) hpvM, ← map_mul]
              show _ = word M ((a₀ : P) * (pv.1 : P) * (pv.2 : P)) (carrier A l₂)
              unfold word
              rw [mul_assoc]
            have hlen' : l₂.length ≤ n := by
              simp only [List.nil_append, List.length_cons] at hlen
              omega
            have hmem' : wordA M A (a₀ * pv.1 * pv.2) l₂
                ∈ (of : P →* CentHNN M).range := by
              rw [← hrw]
              exact hmem
            obtain ⟨y, hy, hyval⟩ := ih (a₀ * pv.1 * pv.2) l₂ hlen' hmem'
            refine ⟨y, by rw [hrw]; exact hy, ?_⟩
            rw [hyval]
            unfold tau
            rw [List.nil_append, List.map_cons, List.prod_cons, map_mul, map_mul,
              hφpv, mul_one]
            unfold blockValue
            group
          · -- the block merges into the block before it
            have hrw : wordA M A a₀ (l₁' ++ [p₀] ++ pv :: l₂)
                = wordA M A a₀ (l₁' ++ (p₀.1, p₀.2 * pv.1 * pv.2) :: l₂) := by
              unfold wordA
              rw [carrier_append, carrier_append, carrier_cons, carrier_cons,
                carrier_cons, carrier_nil, word_append, word_append]
              rw [List.map_append, List.prod_append, List.map_cons, List.prod_cons,
                List.map_cons, List.prod_cons, List.map_nil, List.prod_nil]
              rw [blockOf_of_mem M (pv.1 : P) (pv.2 : P) hpvM]
              show _ = _
              rw [blockOf_mul_of]
              group
            have hlen' : (l₁' ++ (p₀.1, p₀.2 * pv.1 * pv.2) :: l₂).length ≤ n := by
              simp only [List.length_append, List.length_cons, List.length_nil]
                at hlen ⊢
              omega
            have hmem' : wordA M A a₀ (l₁' ++ (p₀.1, p₀.2 * pv.1 * pv.2) :: l₂)
                ∈ (of : P →* CentHNN M).range := by
              rw [← hrw]
              exact hmem
            obtain ⟨y, hy, hyval⟩ :=
              ih a₀ (l₁' ++ (p₀.1, p₀.2 * pv.1 * pv.2) :: l₂) hlen' hmem'
            refine ⟨y, by rw [hrw]; exact hy, ?_⟩
            rw [hyval]
            rw [tau_append, tau_append]
            rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
              List.map_cons, List.prod_cons, List.map_nil, List.prod_nil]
            unfold blockValue
            simp only [map_mul, hφpv, mul_one]
            group
        · -- two blocks whose middle base entry lies in `M`
          obtain ⟨l₁, pv, pv', l₂, hl, hpv, hpv'⟩ :=
            split_carrier₂ A l s₁ (q, z) (q', z') s₂ heq
          subst hl
          have hz : (pv.2 : P) = z := congrArg Prod.snd hpv
          have hpvM : (pv.2 : P) ∈ M := by rw [hz]; exact hzM
          have hφpv : φ pv.2 = 1 := hφ pv.2 hpvM
          have hrw : wordA M A a₀ (l₁ ++ pv :: pv' :: l₂)
              = wordA M A a₀ (l₁ ++ (pv.1 * pv.2 * pv'.1, pv'.2) :: l₂) := by
            unfold wordA
            rw [carrier_append, carrier_append, carrier_cons, carrier_cons,
              carrier_cons, word_append, word_append]
            rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
              List.map_cons, List.prod_cons]
            rw [← blockOf_mul_blockOf M (pv.1 : P) (pv.2 : P) (pv'.1 : P)
              (pv'.2 : P) hpvM]
            group
          have hlen' : (l₁ ++ (pv.1 * pv.2 * pv'.1, pv'.2) :: l₂).length ≤ n := by
            simp only [List.length_append, List.length_cons] at hlen ⊢
            omega
          have hmem' : wordA M A a₀ (l₁ ++ (pv.1 * pv.2 * pv'.1, pv'.2) :: l₂)
              ∈ (of : P →* CentHNN M).range := by
            rw [← hrw]
            exact hmem
          obtain ⟨y, hy, hyval⟩ :=
            ih a₀ (l₁ ++ (pv.1 * pv.2 * pv'.1, pv'.2) :: l₂) hlen' hmem'
          refine ⟨y, by rw [hrw]; exact hy, ?_⟩
          rw [hyval]
          rw [tau_append, tau_append]
          rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
            List.map_cons, List.prod_cons]
          unfold blockValue
          simp only [map_mul, hφpv, mul_one]
          group

end Pinch
end Higman
end GroupApproximation

namespace GroupApproximation
namespace Higman
namespace Pinch

open HNNExtension

variable {P : Type} [Group P] (M A : Subgroup P)
  {T : Type} [Group T] (φ : ↥A →* T)

/-! ## 3.  The graph of the value -/

/-- The subgroup of `Γ × T` generated by the pairs `(a, φ a)` for `a ∈ A` and
`(aᵗ, 1)` for `a ∈ A`.  It is the graph of the homomorphism the rope trick
needs, and `snd_eq_one_of_fst_eq_one` is the statement that it is a graph. -/
def blockGraph : Subgroup (CentHNN M × T) :=
  Subgroup.closure
    ({x : CentHNN M × T | ∃ a : ↥A, x = (of (a : P), φ a)} ∪
      {x : CentHNN M × T | ∃ a : ↥A, x = ((t : CentHNN M)⁻¹ * of (a : P) * t, 1)})

theorem pair_mem_blockGraph (a : ↥A) :
    ((of (a : P) : CentHNN M), φ a) ∈ blockGraph M A φ :=
  Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)

theorem conj_pair_mem_blockGraph (a : ↥A) :
    (((t : CentHNN M)⁻¹ * of (a : P) * t : CentHNN M), (1 : T))
      ∈ blockGraph M A φ :=
  Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)

/-- Every element of the graph is a block word paired with its value. -/
theorem exists_blockData {x : CentHNN M × T} (hx : x ∈ blockGraph M A φ) :
    ∃ (a₀ : ↥A) (l : List (↥A × ↥A)),
      x = (wordA M A a₀ l, tau A φ a₀ l) := by
  obtain ⟨L, hL, rfl⟩ := Subgroup.exists_list_of_mem_closure hx
  clear hx
  induction L with
  | nil =>
      refine ⟨1, [], ?_⟩
      rw [List.prod_nil]
      rw [wordA_nil, tau_nil]
      refine Prod.ext ?_ ?_
      · show (1 : CentHNN M) = of ((1 : ↥A) : P)
        rw [Subgroup.coe_one, map_one]
      · show (1 : T) = φ 1
        rw [map_one]
  | cons y L ih =>
      have hLtail : ∀ u ∈ L, u ∈ _ ∨ u⁻¹ ∈ _ := fun u hu =>
        hL u (List.mem_cons_of_mem _ hu)
      obtain ⟨a₀, l, hprod⟩ := ih hLtail
      have hy : y ∈ ({x : CentHNN M × T | ∃ a : ↥A, x = (of (a : P), φ a)} ∪
          {x : CentHNN M × T | ∃ a : ↥A,
            x = ((t : CentHNN M)⁻¹ * of (a : P) * t, 1)}) := by
        rcases hL y List.mem_cons_self with h | h
        · exact h
        · rcases h with ⟨a, ha⟩ | ⟨a, ha⟩
          · refine Or.inl ⟨a⁻¹, ?_⟩
            have := congrArg (fun z : CentHNN M × T => z⁻¹) ha
            rw [inv_inv] at this
            rw [this]
            refine Prod.ext ?_ ?_
            · show _ = of ((a⁻¹ : ↥A) : P)
              rw [Subgroup.coe_inv, map_inv]
              rfl
            · show _ = φ a⁻¹
              rw [map_inv]
              rfl
          · refine Or.inr ⟨a⁻¹, ?_⟩
            have := congrArg (fun z : CentHNN M × T => z⁻¹) ha
            rw [inv_inv] at this
            rw [this]
            refine Prod.ext ?_ ?_
            · show _ = (t : CentHNN M)⁻¹ * of ((a⁻¹ : ↥A) : P) * t
              rw [Subgroup.coe_inv, map_inv]
              group
            · show (1 : T)⁻¹ = 1
              rw [inv_one]
      rw [List.prod_cons, hprod]
      rcases hy with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · refine ⟨a * a₀, l, ?_⟩
        refine Prod.ext ?_ ?_
        · show of ((a : P)) * wordA M A a₀ l = wordA M A (a * a₀) l
          unfold wordA
          rw [of_mul_word]
          rfl
        · show φ a * tau A φ a₀ l = tau A φ (a * a₀) l
          unfold tau
          rw [map_mul]
          group
      · refine ⟨1, (a, a₀) :: l, ?_⟩
        refine Prod.ext ?_ ?_
        · show ((t : CentHNN M)⁻¹ * of (a : P) * t) * wordA M A a₀ l
            = wordA M A 1 ((a, a₀) :: l)
          unfold wordA
          rw [conj_mul_word]
          show _ = word M ((1 : ↥A) : P) (carrier A ((a, a₀) :: l))
          rw [carrier_cons]
          rw [Subgroup.coe_one]
        · show (1 : T) * tau A φ a₀ l = tau A φ 1 ((a, a₀) :: l)
          rw [one_mul, tau_cons, map_one, one_mul]
          unfold tau
          rfl

/-- **The graph is a graph.**  An element of the graph whose first coordinate
is trivial has trivial second coordinate; this is `descentTau` at the element
`1`. -/
theorem snd_eq_one_of_fst_eq_one (hφ : ∀ x : ↥A, (x : P) ∈ M → φ x = 1)
    {x : CentHNN M × T} (hx : x ∈ blockGraph M A φ) (h1 : x.1 = 1) : x.2 = 1 := by
  obtain ⟨a₀, l, hxeq⟩ := exists_blockData M A φ hx
  have hfst : wordA M A a₀ l = 1 := by
    rw [← h1, hxeq]
  have hmem : wordA M A a₀ l ∈ (of : P →* CentHNN M).range := by
    rw [hfst]
    exact ⟨1, map_one _⟩
  obtain ⟨y, hy, hval⟩ := descentTau M A φ hφ l.length a₀ l le_rfl hmem
  have hy1 : of (y : P) = (1 : CentHNN M) := by
    rw [← hy]
    exact hfst
  have hyone : (y : P) = 1 := by
    have := of_injective_centHNN M
    apply this
    rw [hy1, map_one]
  have hyy : y = 1 := Subtype.ext hyone
  have : x.2 = tau A φ a₀ l := by rw [hxeq]
  rw [this, ← hval, hyy, map_one]

end Pinch
end Higman
end GroupApproximation

namespace GroupApproximation
namespace Higman
namespace Pinch

open HNNExtension

variable {P : Type} [Group P] (M A : Subgroup P)
  {T : Type} [Group T] (φ : ↥A →* T)

/-! ## 4.  The graph is the graph of a homomorphism on `⟨A, Aᵗ⟩` -/

/-- Block words lie in the subgroup generated by `A` and `Aᵗ`. -/
theorem wordA_mem_closure (a₀ : ↥A) (l : List (↥A × ↥A)) :
    wordA M A a₀ l ∈ Subgroup.closure (genSet M A A) := by
  induction l generalizing a₀ with
  | nil =>
      rw [wordA_nil]
      exact Subgroup.subset_closure (Or.inl ⟨(a₀ : P), a₀.2, rfl⟩)
  | cons p l ih =>
      rw [wordA_cons]
      have h₁ : (of ((a₀ : P)) : CentHNN M) ∈ Subgroup.closure (genSet M A A) :=
        Subgroup.subset_closure (Or.inl ⟨(a₀ : P), a₀.2, rfl⟩)
      have h₂ : ((t : CentHNN M)⁻¹ * of ((p.1 : P)) * t)
          ∈ Subgroup.closure (genSet M A A) := by
        refine Subgroup.subset_closure (Or.inr ?_)
        refine ⟨of ((p.1 : P)), ⟨(p.1 : P), p.1.2, rfl⟩, ?_⟩
        show _ * _ * _ = _
        rw [inv_inv]
      have h₃ : (of ((p.2 : P)) : CentHNN M) ∈ Subgroup.closure (genSet M A A) :=
        Subgroup.subset_closure (Or.inl ⟨(p.2 : P), p.2.2, rfl⟩)
      have hblock : blockOf M ((p.1 : P), (p.2 : P))
          ∈ Subgroup.closure (genSet M A A) := by
        unfold blockOf
        have : (t : CentHNN M)⁻¹ * of ((p.1 : P)) * t * of ((p.2 : P))
            = ((t : CentHNN M)⁻¹ * of ((p.1 : P)) * t) * of ((p.2 : P)) := by
          group
        rw [this]
        exact Subgroup.mul_mem _ h₂ h₃
      have htail : (((carrier A l).map (blockOf M)).prod)
          ∈ Subgroup.closure (genSet M A A) := by
        have := ih a₀
        rw [wordA_nil] at this
        have hrest : wordA M A 1 l ∈ Subgroup.closure (genSet M A A) := by
          have h0 := ih 1
          exact h0
        unfold wordA word at hrest
        rw [Subgroup.coe_one, map_one, one_mul] at hrest
        exact hrest
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ hblock) htail

/-- The first-coordinate projection of the graph. -/
def graphProj : ↥(blockGraph M A φ) →* CentHNN M :=
  (MonoidHom.fst (CentHNN M) T).comp (blockGraph M A φ).subtype

theorem graphProj_injective (hφ : ∀ x : ↥A, (x : P) ∈ M → φ x = 1) :
    Function.Injective (graphProj M A φ) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  refine Subtype.ext ?_
  refine Prod.ext hz ?_
  exact snd_eq_one_of_fst_eq_one M A φ hφ z.2 hz

theorem graphProj_range :
    (graphProj M A φ).range = Subgroup.closure (genSet M A A) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, rfl⟩
    obtain ⟨a₀, l, hz⟩ := exists_blockData M A φ z.2
    have : (graphProj M A φ) z = wordA M A a₀ l := by
      show (z : CentHNN M × T).1 = _
      rw [hz]
    rw [this]
    exact wordA_mem_closure M A a₀ l
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact ⟨⟨(of u, φ ⟨u, hu⟩), pair_mem_blockGraph M A φ ⟨u, hu⟩⟩, rfl⟩
    · obtain ⟨v, hv, rfl⟩ := hu
      refine ⟨⟨((t : CentHNN M)⁻¹ * of v * t, 1),
        conj_pair_mem_blockGraph M A φ ⟨v, hv⟩⟩, ?_⟩
      show (t : CentHNN M)⁻¹ * of v * t = _
      show _ = _ * _ * _
      rw [inv_inv]

/-- The graph, as a copy of `⟨A, Aᵗ⟩`. -/
noncomputable def graphEquiv (hφ : ∀ x : ↥A, (x : P) ∈ M → φ x = 1) :
    ↥(blockGraph M A φ) ≃* ↥(Subgroup.closure (genSet M A A)) := by
  refine MulEquiv.trans (MulEquiv.ofBijective (graphProj M A φ).rangeRestrict ?_)
    (MulEquiv.subgroupCongr (graphProj_range M A φ))
  refine ⟨?_, (graphProj M A φ).rangeRestrict_surjective⟩
  intro x y hxy
  exact graphProj_injective M A φ hφ (congrArg Subtype.val hxy)

/-- The homomorphism the rope trick needs: `φ` on `A`, trivial on `Aᵗ`. -/
noncomputable def tauHom (hφ : ∀ x : ↥A, (x : P) ∈ M → φ x = 1) :
    ↥(Subgroup.closure (genSet M A A)) →* T :=
  ((MonoidHom.snd (CentHNN M) T).comp (blockGraph M A φ).subtype).comp
    (graphEquiv M A φ hφ).symm.toMonoidHom

end Pinch
end Higman
end GroupApproximation
