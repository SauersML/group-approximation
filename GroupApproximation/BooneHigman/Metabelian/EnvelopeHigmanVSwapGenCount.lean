import GroupApproximation.BooneHigman.V.ConeSwap
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card
import GroupApproximation.Meta.AxiomGuard

/-!
# Counting leaves of a prefix substitution

Word-level facts about prefix substitutions `f` of the Cantor space, used to show that the cone
swaps generate `V_d` (`EnvelopeHigmanVSwapGenAll.lean`).

* `swapGen_exists_source`: if every word of length `N` has a target, every stream lies in some
  target cone.
* `swapGen_source_eq_of_prefix`: two sources of the same length whose targets are comparable
  coincide.
* `swapGen_length_eq_of_le`: if every word of length `N` has a target of length `≥ N`, all these
  targets have length exactly `N` (a pigeonhole count over the finitely many words of length `N`).
* `swapGen_inv_ge`: if every target has length `≤ N`, then `f⁻¹` has depth `N` with targets of
  length `≥ N`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {X : Type*}

/-- Equal streams with prefixes `v` and `u` agree at every common position. -/
theorem swapGen_getElem_eq {v u : List X} {a b : Cantor X} (h : prepend v a = prepend u b)
    {k : ℕ} (hv : k < v.length) (hu : k < u.length) : v[k] = u[k] := by
  have hc := congrFun h k
  rwa [prepend_getElem v a hv, prepend_getElem u b hu] at hc

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_getElem_eq

/-- Every stream lies in a target cone of a depth-`N` prefix substitution. -/
theorem swapGen_exists_source {f : Equiv.Perm (Cantor X)} {N : ℕ}
    (hf : ∀ w : List X, w.length = N → ∃ v, MapsCone f w v) (z : Cantor X) :
    ∃ w v y, w.length = N ∧ MapsCone f w v ∧ prepend v y = z := by
  obtain ⟨v, hv⟩ := hf (firstWord N (f⁻¹ z)) (length_firstWord N _)
  refine ⟨firstWord N (f⁻¹ z), v, dropN N (f⁻¹ z), length_firstWord N _, hv, ?_⟩
  rw [← hv (dropN N (f⁻¹ z)), prepend_firstWord]
  exact f.apply_symm_apply z

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_exists_source

/-- Equal streams with long enough prefixes `v` and `u` have `v.take N = u.take N`. -/
theorem swapGen_take_eq_of_prepend_eq {v u : List X} {a b : Cantor X}
    (h : prepend v a = prepend u b) {N : ℕ} (hv : N ≤ v.length) (hu : N ≤ u.length) :
    v.take N = u.take N := by
  apply List.ext_getElem
  · rw [List.length_take, List.length_take]
    omega
  · intro k hk1 _
    have hk : k < N := lt_of_lt_of_le hk1 (List.length_take_le N v)
    rw [List.getElem_take, List.getElem_take]
    exact swapGen_getElem_eq h (by omega) (by omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_take_eq_of_prepend_eq

/-- Two sources of the same length with comparable targets coincide. -/
theorem swapGen_source_eq_of_prefix [Nontrivial X] {f : Equiv.Perm (Cantor X)}
    {w₁ w₂ v₁ v₂ : List X} (h₁ : MapsCone f w₁ v₁) (h₂ : MapsCone f w₂ v₂)
    (hlen : w₁.length = w₂.length) (hpre : v₁ <+: v₂) : w₁ = w₂ := by
  obtain ⟨a, -, -⟩ := exists_pair_ne X
  obtain ⟨t, rfl⟩ := hpre
  have key : prepend w₂ (fun _ => a) = prepend w₁ (prepend t (fun _ => a)) := by
    apply f.injective
    rw [h₂ (fun _ => a), h₁ (prepend t (fun _ => a)), prepend_append]
  exact ((prefix_of_prepend_eq key hlen.symm.le).eq_of_length hlen.symm).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_source_eq_of_prefix

/-- **Pigeonhole on leaves.** If every word of length `N` has a target of length `≥ N`, every
such target has length exactly `N`. -/
theorem swapGen_length_eq_of_le [Finite X] [Nontrivial X] {f : Equiv.Perm (Cantor X)} {N : ℕ}
    (hf : ∀ w : List X, w.length = N → ∃ v, MapsCone f w v ∧ N ≤ v.length)
    {w v : List X} (hw : w.length = N) (hv : MapsCone f w v) : v.length = N := by
  choose t ht htl using hf
  haveI : Finite ↥{l : List X | l.length = N} := (finite_words_length_eq N).to_subtype
  let π : ↥{l : List X | l.length = N} → ↥{l : List X | l.length = N} := fun l =>
    ⟨(t l.1 l.2).take N, by
      show ((t l.1 l.2).take N).length = N
      rw [List.length_take]
      exact min_eq_left (htl l.1 l.2)⟩
  have hsurj : Function.Surjective π := by
    rintro ⟨u, hu⟩
    have hu' : u.length = N := hu
    obtain ⟨a, -, -⟩ := exists_pair_ne X
    obtain ⟨w', v', y, hw', hv', hy⟩ :=
      swapGen_exists_source (fun w h => ⟨t w h, ht w h⟩) (prepend u (fun _ => a))
    have hvv : t w' hw' = v' := MapsCone.unique (ht w' hw') hv'
    have hNv' : N ≤ v'.length := hvv ▸ htl w' hw'
    refine ⟨⟨w', hw'⟩, Subtype.ext ?_⟩
    show (t w' hw').take N = u
    rw [hvv, swapGen_take_eq_of_prepend_eq hy hNv' hu'.ge, List.take_of_length_le hu'.le]
  have hinj : Function.Injective π := Finite.injective_iff_surjective.mpr hsurj
  have hvt : t w hw = v := MapsCone.unique (ht w hw) hv
  have hNv : N ≤ v.length := hvt ▸ htl w hw
  by_contra hne
  have hlt : N < v.length := lt_of_le_of_ne hNv (Ne.symm hne)
  obtain ⟨c, hc⟩ := exists_ne (v[N]'hlt)
  obtain ⟨w', v', y, hw', hv', hy⟩ :=
    swapGen_exists_source (fun w h => ⟨t w h, ht w h⟩) (prepend (v.take N) (fun _ => c))
  have hvv' : t w' hw' = v' := MapsCone.unique (ht w' hw') hv'
  have hNv' : N ≤ v'.length := hvv' ▸ htl w' hw'
  have hNt : ¬ N < (v.take N).length := by
    rw [List.length_take]
    omega
  have htake : v'.take N = v.take N := by
    have h1 := swapGen_take_eq_of_prepend_eq hy hNv' (by rw [List.length_take]; omega)
    rwa [List.take_of_length_le (List.length_take_le N v)] at h1
  have h2 : π ⟨w', hw'⟩ = π ⟨w, hw⟩ := by
    apply Subtype.ext
    show (t w' hw').take N = (t w hw).take N
    rw [hvv', hvt, htake]
  have hww : w' = w := congrArg Subtype.val (hinj h2)
  subst hww
  have hvv2 : v' = v := MapsCone.unique hv' hv
  subst hvv2
  have h3 := congrFun hy N
  rw [prepend_getElem v' y hlt, prepend_of_length_le (v'.take N) (fun _ => c) hNt] at h3
  exact hc h3.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_length_eq_of_le

/-- If every word of length `N` has a target of length `≤ N`, then every word of length `N` has
an `f⁻¹`-target of length `≥ N`. -/
theorem swapGen_inv_ge [Nontrivial X] {f : Equiv.Perm (Cantor X)} {N : ℕ}
    (hf : ∀ w : List X, w.length = N → ∃ v, MapsCone f w v ∧ v.length ≤ N)
    (u : List X) (hu : u.length = N) : ∃ v, MapsCone f⁻¹ u v ∧ N ≤ v.length := by
  obtain ⟨a, -, -⟩ := exists_pair_ne X
  obtain ⟨w, v, y, hw, hv, hy⟩ :=
    swapGen_exists_source (fun w h => (hf w h).imp fun _ h' => h'.1) (prepend u (fun _ => a))
  obtain ⟨v₀, hv₀, hl⟩ := hf w hw
  have hvv : v₀ = v := MapsCone.unique hv₀ hv
  subst hvv
  obtain ⟨s, rfl⟩ := prefix_of_prepend_eq hy (by omega)
  refine ⟨w ++ s, (hv₀.append s).inv, ?_⟩
  rw [List.length_append]
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_inv_ge

end GroupApproximation.BooneHigman.Metabelian.Envelope
