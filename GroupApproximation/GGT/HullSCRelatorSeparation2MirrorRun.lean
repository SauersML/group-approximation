import GroupApproximation.GGT.HullSCRelatorSeparation2Mirror

/-!
# Step (c), second half: the run read backwards

The case step (b) and `GGT/HullSCRelatorSeparation2Mirror.lean` leave open is
the mixed one: one member of the symmetrized closure a rotation of the relator,
the other a rotation of its formal inverse.  The two words are never equal, so
the argument by positions does not apply, and something else has to fail.

What fails is the order of the exponents.  Reading the run of the relator
forwards visits `ms` in increasing order of index; reading the run of the formal
inverse forwards visits `ms` in **decreasing** order.  So if two blocks at
consecutive positions of the one match two blocks at consecutive positions of
the other, the same exponent occurs at two indices of `ms` whose distance is
`2`, and `ms` has no repetitions.  That is `not_mirrored_exponent_match`, and it
is arithmetic: no injectivity, no group theory, nothing about the geometry.

The three lemmas before it are what turns a matched block into an index of
`ms`.

* `getElem?_revInv'` reads the formal inverse at an index, in the form of
  `List.getElem?_reverse'` -- with the linear relation `t + q + 1 = |v|` as a
  hypothesis, so that no truncated subtraction enters the statements.
* `blockWord_getElem?_exponent` names the exponent of the block at a position of
  the run.
* `revInv_blockWord_getElem?_exponent` does the same for the mirrored run, and
  it is the lemma that reverses the index.

`not_mirrored_block_match` is the packaging the consumer wants: the four letters
and the two exponent equalities that `HullSC.exponent_eq_of_mirroredBlockMatch₂`
produces, and `False`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry

universe u w

/-- **Reading a formal inverse at an index.**  The linear form of
`List.getElem?_reverse`. -/
theorem getElem?_revInv' {G : Type u} [Group G] {Λ : Type w}
    {l : List (GGT.RelLetter G Λ)} {t q : ℕ} (h : t + q + 1 = l.length) :
    (RelWord.revInv l)[t]? = Option.map RelWord.inv l[q]? := by
  have hlen : t + q + 1 = (l.map RelWord.inv).length := by
    rw [List.length_map]
    exact h
  show ((l.map RelWord.inv).reverse)[t]? = Option.map RelWord.inv l[q]?
  rw [List.getElem?_reverse' hlen, List.getElem?_map]

section Run

variable {G : Type u} [Group G]

/-- **The exponent of the block at a position of the run.** -/
theorem blockWord_getElem?_exponent (h₀ h₁ : G) :
    ∀ (s : Bool) (ms : List ℕ) (k : ℕ) (b : Bool) (x : G),
      (blockWord h₀ h₁ s ms)[k]? = some (GGT.RelLetter.comp b x) →
        ∃ m : ℕ, ms[k]? = some m ∧ x = (if b then h₁ else h₀) ^ m := by
  intro s ms
  induction ms generalizing s with
  | nil =>
      intro k b x hk
      rw [blockWord_nil] at hk
      simp at hk
  | cons m t ih =>
      intro k b x hk
      rw [blockWord_cons] at hk
      cases k with
      | zero =>
          rw [List.getElem?_cons_zero] at hk
          have heq := Option.some.inj hk
          rw [GGT.RelLetter.comp.injEq] at heq
          obtain ⟨hb, hx⟩ := heq
          refine ⟨m, ?_, ?_⟩
          · rw [List.getElem?_cons_zero]
          · rw [← hx, hb]
      | succ k' =>
          rw [List.getElem?_cons_succ] at hk
          obtain ⟨m', hm', hx'⟩ := ih (!s) k' b x hk
          refine ⟨m', ?_, hx'⟩
          rw [List.getElem?_cons_succ]
          exact hm'

/-- **The exponent of the block at a position of the mirrored run**, at the
reversed index.  The letter is the formal inverse of a block letter, so the
element it carries is the inverse of a power. -/
theorem revInv_blockWord_getElem?_exponent (h₀ h₁ : G) (s : Bool) (ms : List ℕ)
    {t q : ℕ} (hq : t + q + 1 = ms.length) {b : Bool} {x : G}
    (hx : (RelWord.revInv (blockWord h₀ h₁ s ms))[t]?
      = some (GGT.RelLetter.comp b x)) :
    ∃ m : ℕ, ms[q]? = some m ∧ x = ((if b then h₁ else h₀) ^ m)⁻¹ := by
  have hlen : t + q + 1 = (blockWord h₀ h₁ s ms).length := by
    rw [length_blockWord]
    exact hq
  rw [getElem?_revInv' hlen] at hx
  obtain ⟨a, ha, hfa⟩ := Option.map_eq_some_iff.mp hx
  cases a with
  | base g =>
      have hfa' : (GGT.RelLetter.base g⁻¹ : GGT.RelLetter G Bool)
          = GGT.RelLetter.comp b x := hfa
      exact absurd hfa' (base_ne_comp g⁻¹ x b)
  | comp c z =>
      have hfa' : (GGT.RelLetter.comp c z⁻¹ : GGT.RelLetter G Bool)
          = GGT.RelLetter.comp b x := hfa
      rw [GGT.RelLetter.comp.injEq] at hfa'
      obtain ⟨hc, hz⟩ := hfa'
      obtain ⟨m, hm, hzm⟩ := blockWord_getElem?_exponent h₀ h₁ s ms q c z ha
      refine ⟨m, hm, ?_⟩
      rw [← hz, hzm, hc]

end Run

/-! ## The mixed case is impossible -/

/-- **The exponents cannot match in reversed order.**

Two positions of `ms` read forwards, `k` and `k + 1`, against two positions read
backwards, `q` and `q'`, with `q = q' + 1` forced by the two linear relations.
Repetition-freeness turns the two matches into `k = q` and `k + 1 = q'`, so
`k + 1 = k - 1`. -/
theorem not_mirrored_exponent_match {ms : List ℕ} (hnodup : ms.Nodup)
    {k t q q' i i' : ℕ} (hq : t + q + 1 = ms.length)
    (hq' : t + 1 + q' + 1 = ms.length)
    (h1 : ms[k]? = some i) (h2 : ms[q]? = some i)
    (h3 : ms[k + 1]? = some i') (h4 : ms[q']? = some i') : False := by
  have e1 : k = q := getElem?_eq_of_nodup hnodup h1 h2
  have e2 : k + 1 = q' := getElem?_eq_of_nodup hnodup h3 h4
  omega

section Match

variable {G : Type u} [Group G]

/-- **The mixed case of step (c), closed.**

Two blocks at consecutive positions of the run, two blocks at consecutive
positions of the mirrored run, and the two exponent equalities that a mirrored
match produces: impossible.  The hypotheses are exactly what step (a) and
`HullSC.exponent_eq_of_mirroredBlockMatch₂` deliver. -/
theorem not_mirrored_block_match {h₀ h₁ : G}
    (hinj : ∀ c : Bool,
      Function.Injective (fun n : ℕ => (if c then h₁ else h₀) ^ n))
    {s : Bool} {ms : List ℕ} (hnodup : ms.Nodup) {k t : ℕ}
    (ht : t + 1 < ms.length) {b b' : Bool} {i i' j j' : ℕ}
    (hw : (blockWord h₀ h₁ s ms)[k]?
      = some (GGT.RelLetter.comp b ((if b then h₁ else h₀) ^ i)))
    (hw' : (blockWord h₀ h₁ s ms)[k + 1]?
      = some (GGT.RelLetter.comp b' ((if b' then h₁ else h₀) ^ i')))
    (hv : (RelWord.revInv (blockWord h₀ h₁ s ms))[t]?
      = some (GGT.RelLetter.comp b (((if b then h₁ else h₀) ^ j)⁻¹)))
    (hv' : (RelWord.revInv (blockWord h₀ h₁ s ms))[t + 1]?
      = some (GGT.RelLetter.comp b' (((if b' then h₁ else h₀) ^ j')⁻¹)))
    (hij : i = j) (hij' : i' = j') : False := by
  obtain ⟨m, hm, hmx⟩ := blockWord_getElem?_exponent h₀ h₁ s ms k b _ hw
  obtain ⟨n, hn, hnx⟩ := blockWord_getElem?_exponent h₀ h₁ s ms (k + 1) b' _ hw'
  obtain ⟨r, hr, hrx⟩ :=
    revInv_blockWord_getElem?_exponent h₀ h₁ s ms
      (q := ms.length - 1 - t) (by omega) hv
  obtain ⟨r', hr', hr'x⟩ :=
    revInv_blockWord_getElem?_exponent h₀ h₁ s ms
      (t := t + 1) (q := ms.length - 2 - t) (by omega) hv'
  have hmi : m = i := (hinj b hmx).symm
  have hni : n = i' := (hinj b' hnx).symm
  have hrj : r = j := (hinj b (inv_injective hrx)).symm
  have hr'j : r' = j' := (hinj b' (inv_injective hr'x)).symm
  rw [hmi] at hm
  rw [hni] at hn
  rw [hrj, ← hij] at hr
  rw [hr'j, ← hij'] at hr'
  exact not_mirrored_exponent_match hnodup (t := t)
    (q := ms.length - 1 - t) (q' := ms.length - 2 - t) (by omega) (by omega)
    hm hr hn hr'

end Match

end HullSC
end GroupApproximation
