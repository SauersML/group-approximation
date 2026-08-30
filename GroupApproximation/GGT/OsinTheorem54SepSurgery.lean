import GroupApproximation.GGT.OsinTheorem54SepYLetterWord
import GroupApproximation.GGT.OsinTheorem54SepPieces
import GroupApproximation.GGT.OsinTheorem54SepInhabit

/-!
# The path surgery of Osin's Lemma 5.8

An admissible path over the enlarged alphabet `Y ⊔ ℋ` is rebuilt over `Z ⊔ ℋ`,
one letter at a time, keeping its endpoints and its admissibility and gaining a
side structure:

* a letter of `Y` becomes a geodesic of the ORIGINAL alphabet with its
  peripheral letters demoted to base letters of `Z` --- legitimate because
  `S(1,y;D) = ∅` makes every component of that geodesic shallow, which is
  `forall_base_demote_of_sepSet_empty`;
* a letter of `ℋ` is kept as it is, and is already a letter of `Z`, the family
  being untouched by the enlargement of the base.

The output is a list of PIECES rather than a word, because that is what
`isQuasiGeodesicPolygon_flatten` consumes: one side per letter of the original
path, so the side count is the original length and not the rebuilt one.  That
distinction is the whole point of the construction --- the rebuilt path can be
arbitrarily longer, since a letter of `Y` may be far away in `Γ(G, X ⊔ ℋ)`, but
the polygon's side count is what the isolated-component bound is indexed by.

## The three things carried through the recursion

Length (one piece per letter), geodesy of each piece from every basepoint, and
the value.  Admissibility is carried as a fourth clause and is where the two
cases differ: a demoted piece reads no peripheral letter at all, so it avoids
`Γ_{H_λ}` from any vertex whatever; a kept `ℋ`-letter avoids it for exactly the
reason the original path did, at exactly the same vertex.

`hne` --- no letter of the input is trivial --- is spent only on the kept
letters, where it is what makes a one-letter side geodesic.  It comes from
`exists_nontrivial_word_of_mem_relBall`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinEnlargement

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Two small facts -/

/-- **A word of base letters avoids every `Γ_{H_λ}`**, from any vertex. -/
theorem avoidsFrom_of_forall_base (H : Λ → Subgroup G) (lam : Λ) :
    ∀ (q : List (RelLetter G Λ)) (v : G),
      (∀ b ∈ q, ∃ x : G, b = RelLetter.base x) → AvoidsFrom H lam q v := by
  intro q
  induction q with
  | nil => intro _ _; trivial
  | cons a t ih =>
      intro v hbase
      obtain ⟨x, rfl⟩ := hbase a List.mem_cons_self
      exact ⟨fun hc => hc.1, ih (v * (RelLetter.base x).val)
        (fun b hb => hbase b (List.mem_cons_of_mem _ hb))⟩

/-- **A single non-trivial letter is a geodesic word.** -/
theorem isGeodesicWord_singleton (D : RelGenSet G Λ) {a : RelLetter G Λ}
    (hlet : D.IsLetter a) (hne : a.val ≠ 1) (u : G) :
    IsGeodesicWord D u (u * a.val) [a] := by
  have hmem : a.val ∈ D.alphabet.carrier := by
    cases a with
    | base x => exact Set.mem_union_left _ hlet
    | comp mu x =>
        exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨mu, hlet⟩)
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    rw [List.mem_singleton.mp hb]
    exact hlet
  · rw [listVal_cons, RelLetter.listVal_nil, mul_one]
  · have hd : wordDist D.alphabet.carrier u (u * a.val)
        = wordNorm D.alphabet.carrier a.val := by
      show wordNorm D.alphabet.carrier (u⁻¹ * (u * a.val)) = _
      rw [inv_mul_cancel_left]
    have hle : wordNorm D.alphabet.carrier a.val ≤ 1 :=
      wordNorm_le_one_of_mem hmem
    have hne' : wordNorm D.alphabet.carrier a.val ≠ 0 := by
      intro h0
      exact hne ((wordNorm_eq_zero_iff D.alphabet.symmetricGenerating a.val).mp h0)
    have hlen : ([a] : List (RelLetter G Λ)).length = 1 := rfl
    rw [hlen, hd]
    omega

/-! ## The surgery -/

/-- **Every admissible path over `Y ⊔ ℋ` is a chain of geodesic pieces over
`Z ⊔ ℋ`**, one piece per letter, with the same endpoints and the same
admissibility. -/
theorem exists_pieces_of_enlargedWord (D : RelGenSet G Λ) {Dc : ℕ}
    (hDc : 1 ≤ Dc) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) :
    ∀ w : List (RelLetter G Λ),
      (∀ a ∈ w, (enlargedY D hDc hsymm).IsLetter a) → (∀ a ∈ w, a.val ≠ 1) →
      ∃ ps : List (List (RelLetter G Λ)), ps.length = w.length ∧
        (∀ q ∈ ps, ∀ u : G,
          IsGeodesicWord (relGenSetZ D Dc) u (u * RelLetter.listVal q) q) ∧
        RelLetter.listVal ps.flatten = RelLetter.listVal w ∧
        ∀ (lam : Λ) (v : G), AvoidsFrom D.fam lam w v →
          AvoidsFrom D.fam lam ps.flatten v := by
  intro w
  induction w with
  | nil =>
      intro _ _
      refine ⟨[], rfl, ?_, rfl, ?_⟩
      · intro q hq
        simp at hq
      · intro _ _ _
        trivial
  | cons a t ih =>
      intro hlet hne
      obtain ⟨ps, hlen, hgeo, hval, hav⟩ :=
        ih (fun b hb => hlet b (List.mem_cons_of_mem a hb))
          (fun b hb => hne b (List.mem_cons_of_mem a hb))
      -- the piece for the head letter
      obtain ⟨q, hqgeo, hqval, hqav⟩ :
          ∃ q : List (RelLetter G Λ),
            (∀ u : G, IsGeodesicWord (relGenSetZ D Dc) u
              (u * RelLetter.listVal q) q) ∧
            RelLetter.listVal q = a.val ∧
            ∀ (lam : Λ) (v : G),
              ¬ (RelLetter.IsCompOf lam a ∧ v ∈ D.fam lam) →
              AvoidsFrom D.fam lam q v := by
        have hale : (enlargedY D hDc hsymm).IsLetter a := hlet a List.mem_cons_self
        cases a with
        | comp mu x =>
            refine ⟨[RelLetter.comp mu x], ?_, ?_, ?_⟩
            · intro u
              have hz : (relGenSetZ D Dc).IsLetter (RelLetter.comp mu x) := hale
              have hg := isGeodesicWord_singleton (relGenSetZ D Dc) hz
                (hne _ List.mem_cons_self) u
              rw [listVal_cons, RelLetter.listVal_nil, mul_one]
              exact hg
            · rw [listVal_cons, RelLetter.listVal_nil, mul_one]
            · intro lam v hcl
              exact ⟨hcl, trivial⟩
        | base y =>
            have hy : ∀ lam : Λ, sepSet D lam Dc 1 y = ∅ := hale
            obtain ⟨p, hp⟩ := existsGeodesicWord D 1 y
            refine ⟨demote p, ?_, ?_, ?_⟩
            · intro u
              have hbase := forall_base_demote_of_sepSet_empty D Dc hy hp
              have hlenp : (demote p).length = p.length := length_demote p
              have hvalp : RelLetter.listVal (demote p) = y := by
                rw [listVal_demote]
                have := hp.2.1
                rwa [one_mul] at this
              have hinv : wordDist D.alphabet.carrier u (u * y)
                  = wordDist D.alphabet.carrier 1 y := by
                have h1 := wordDist_left_invariant D.alphabet.carrier u 1 y
                rwa [mul_one] at h1
              refine ⟨?_, ?_, ?_⟩
              · intro b hb
                obtain ⟨x, rfl, hx⟩ := hbase b hb
                exact hx
              · rw [hvalp]
              · rw [hlenp, hvalp, alphabet_carrier_relGenSetZ D Dc, hinv]
                exact hp.2.2
            · rw [listVal_demote]
              have := hp.2.1
              rwa [one_mul] at this
            · intro lam v _
              refine avoidsFrom_of_forall_base D.fam lam (demote p) v ?_
              intro b hb
              obtain ⟨x, hbx, -⟩ := forall_base_demote_of_sepSet_empty D Dc hy hp b hb
              exact ⟨x, hbx⟩
      refine ⟨q :: ps, ?_, ?_, ?_, ?_⟩
      · rw [List.length_cons, List.length_cons, hlen]
      · intro r hr u
        rcases List.mem_cons.mp hr with hr' | hr'
        · rw [hr']
          exact hqgeo u
        · exact hgeo r hr' u
      · rw [List.flatten_cons, listVal_append, hqval, hval, listVal_cons]
      · intro lam v havw
        obtain ⟨hfirst, hrest⟩ := havw
        rw [List.flatten_cons, avoidsFrom_append]
        refine ⟨hqav lam v hfirst, ?_⟩
        rw [hqval]
        exact hav lam (v * a.val) hrest

end OsinComponents
end GGT
end GroupApproximation
