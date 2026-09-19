import GroupApproximation.GGT.OsinTheorem54SepFinite
import GroupApproximation.GGT.OsinTheorem54SepTransportFam

/-!
# Local finiteness transports, at a general family

The general-`Λ` form of `GGT/OsinTheorem54SepFinite.lean`.  With
`X ⊆ X' ⊆ X ∪ N`, every element of `N` lying in some `H_μ`, and `d̂_λ` locally
finite for `X`, it is locally finite for `X'`.

The recursion is the one at `Unit`, cut at the first new letter read inside
`H_λ`.  The one difference is which letters count as obstructions: a new letter
outside `H_λ` is demoted to a letter of its own family and never troubles
`AvoidsFrom … λ`, so the cut is taken only at new letters that lie in `H_λ`
themselves --- which is also what makes the cut vertex stay in the coset, so that
the suffix can be translated back to `1`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The peel, at a general family.** -/
theorem exists_peel' (D D' : RelGenSet G Λ) (lam : Λ) (hfam : D'.fam = D.fam)
    {N : Set G} (hN : ∀ x ∈ N, ∃ mu : Λ, x ∈ D.fam mu)
    (hbase : D'.base ⊆ D.base ∪ N) {n : ℕ} {h : G}
    (hh : h ∈ D'.relBall lam (n + 1)) :
    h ∈ D.relBall lam (n + 1) ∨
      ∃ p x q : G, p ∈ D.relBall lam (n + 1) ∧ x ∈ N ∧
        q ∈ D'.relBall lam n ∧ h = p * x * q := by
  classical
  obtain ⟨hfamh, w, hlet, hval, hav, hlen⟩ := hh
  have hfamh' : h ∈ D.fam lam := by rw [← hfam]; exact hfamh
  by_cases hgood : ∀ (j : ℕ) (hj : j < w.length) (x : G),
      (w[j]'hj) = RelLetter.base x → x ∈ N → x ∉ D.base → x ∈ D.fam lam →
        vertex (1 : G) w j ∉ D.fam lam
  · exact Or.inl (mem_relBall_of_noNewLetterInFam' D D' lam hfam hN hbase hfamh'
      hlet hval hav hlen hgood)
  · have hex : ∃ j : ℕ, ∃ hj : j < w.length, ∃ x : G,
        (w[j]'hj) = RelLetter.base x ∧ x ∈ N ∧ x ∉ D.base ∧ x ∈ D.fam lam ∧
          vertex (1 : G) w j ∈ D.fam lam := by
      by_contra hcon
      refine hgood ?_
      intro j hj x hx hxN hxb hxlam hv
      exact hcon ⟨j, hj, x, hx, hxN, hxb, hxlam, hv⟩
    obtain ⟨hj₀len, x, hx, hxN, hxb, hxlam, hvH⟩ := Nat.find_spec hex
    have hpre : vertex (1 : G) w (Nat.find hex) ∈ D.relBall lam (n + 1) := by
      refine mem_relBall_of_noNewLetterInFam' D D' lam hfam hN hbase hvH
        (fun a ha => hlet a (List.take_subset (Nat.find hex) w ha)) ?_
        (avoidsFrom_take D'.fam lam 1 w (Nat.find hex) hav) ?_ ?_
      · rw [vertex_eq_mul_listVal_take w 1 (Nat.find hex), one_mul]
      · rw [List.length_take]
        omega
      · intro m hm y hy hyN hyb hylam hv
        have hmj : m < Nat.find hex := by
          rw [List.length_take] at hm
          omega
        have hmw : m < w.length := by omega
        refine Nat.find_min hex hmj ⟨hmw, y, ?_, hyN, hyb, hylam, ?_⟩
        · rw [← getElem_take_eq w (Nat.find hex) m hm hmw]
          exact hy
        · rwa [vertex_take_eq 1 w (Nat.find hex) m (le_of_lt hmj)] at hv
    have hxval : (w[Nat.find hex]'hj₀len).val = x := by
      simp [hx, RelLetter.val]
    have hsucc : vertex (1 : G) w (Nat.find hex + 1)
        = vertex (1 : G) w (Nat.find hex) * x := by
      rw [vertex_succ w 1 (Nat.find hex) hj₀len, hxval]
    have hvH1 : vertex (1 : G) w (Nat.find hex + 1) ∈ D'.fam lam := by
      rw [hfam, hsucc]
      exact mul_mem hvH hxlam
    have hendq : (vertex (1 : G) w (Nat.find hex + 1))⁻¹ * RelLetter.listVal w
        ∈ D'.fam lam := by
      rw [hfam, hval, hsucc]
      exact mul_mem (inv_mem (mul_mem hvH hxlam)) hfamh'
    have hle : w.length - (Nat.find hex + 1) ≤ n := by omega
    have hq : (vertex (1 : G) w (Nat.find hex + 1))⁻¹ * RelLetter.listVal w
        ∈ D'.relBall lam n :=
      relBall_mono_radius D' lam hle
        (mem_relBall_vertex_inv_mul D' lam hlet hav (Nat.find hex + 1) hvH1 hendq)
    refine Or.inr ⟨vertex (1 : G) w (Nat.find hex), x,
      (vertex (1 : G) w (Nat.find hex + 1))⁻¹ * RelLetter.listVal w,
      hpre, hxN, hq, ?_⟩
    rw [hsucc, ← hval]
    group

/-- **Local finiteness transports across a finite enlargement of the base inside
the family**, at a general family.  No hypothesis on `Λ` is needed: the argument
runs one `lam` at a time. -/
theorem relBall_finite_of_base_subset' (D D' : RelGenSet G Λ) (lam : Λ)
    (hfam : D'.fam = D.fam) {N : Set G}
    (hN : ∀ x ∈ N, ∃ mu : Λ, x ∈ D.fam mu) (hNfin : N.Finite)
    (hbase : D'.base ⊆ D.base ∪ N)
    (hDfin : ∀ m : ℕ, (D.relBall lam m).Finite) :
    ∀ n : ℕ, (D'.relBall lam n).Finite := by
  intro n
  induction n with
  | zero =>
      rw [RelGenSet.relBall_zero]
      exact Set.finite_singleton 1
  | succ n ih =>
      refine Set.Finite.subset
        ((hDfin (n + 1)).union
          (((hDfin (n + 1)).prod (hNfin.prod ih)).image
            (fun t : G × G × G => t.1 * t.2.1 * t.2.2))) ?_
      intro g hg
      rcases exists_peel' D D' lam hfam hN hbase hg with
        hd | ⟨p, x, q, hp, hx, hq, heq⟩
      · exact Or.inl hd
      · exact Or.inr ⟨(p, x, q), ⟨hp, hx, hq⟩, heq.symm⟩

end OsinComponents
end GGT
end GroupApproximation
