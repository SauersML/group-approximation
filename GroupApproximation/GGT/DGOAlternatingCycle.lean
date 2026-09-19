import GroupApproximation.GGT.DGOAlternatingWord

/-!
# Two cycles carrying an `H`-letter of `(a h)^n`, and the growth of `|(a h)^n|`

This module is the geometric half of a proof of Dahmani--Guirardel--Osin's
Corollary 6.12 that does **not** pass through their Proposition 4.14.

Their route to Corollary 6.12 is Theorem 6.11, whose proof runs on Lemma 4.21(a)
--- *a word satisfying `(W1)`--`(W3)` labels a `(4,1)`-quasi-geodesic* --- and
that lemma counts isolated components of a polygon with `2m+2` sides, so it
needs the linear isolated-component bound at an **unbounded** number of sides.
The repository has that bound only at `n ≤ 6`
(`DGOPolygonBaseCaseTower.isolatedComponentBound_of_fourPointHyperbolic`), and
Lemma 4.17 cannot extend it to all `n` --- its constant grows.

What is used here instead is only their Lemma 4.6, already unconditional in this
repository as `OsinComponents.relBall_inv_of_isolated_of_closed`: *an isolated
`H_λ`-component of a cycle of length `C` has `d̂_λ ≤ C`.*  Choosing `h ∈ H` with
`h⁻¹` outside the ball of radius `R` makes every cycle carrying an isolated copy
of the letter `h` longer than `R`, and that alone forces `(a h)^n` to be long,
for `n` up to about `R/3`.  A separate dyadic argument, in
`GGT.DGOCorollary612Unconditional`, upgrades a bound valid on one long window to
genuine loxodromy.

The inverse span is the form Lemma 4.6 proves without any hypothesis on `X`;
turning it into the span itself needs `X` symmetric.  Nothing here needs that,
because the letter placed in the cycle is chosen: to bound `(a h)^n` with `h⁻¹`
far from `1`, read the cycle with the letter `h`.

## The two cycles

Write `g = a h`, `a ∈ X \ H`, `h ∈ H`.

**The first cycle** exists only when some power of `g` returns to `H`.  Let `m`
be least with `g^m ∈ H`.  Then `m ≥ 2`, since `g ∈ H` would give `a = g h⁻¹ ∈ H`.
The cycle is `(a h)^m` closed up by the single `H`-letter `(g^m)⁻¹`, of length
`2m+1`, and in it the *first* `h`-letter is isolated: another `h`-letter of the
alternating part would force `g^s ∈ H` for some `0 < s < m`, against minimality,
and the closing letter is not the start of a component at all --- the letter
before it is the last `h`.  So `h⁻¹` lies in the ball of radius `2m+1`, and
`inv_mem_relBall_of_minimal_pow_mem_fam` says so.  Contrapositively
`lt_two_mul_add_one_of_pow_mem_fam`: if `h⁻¹` is outside the ball of radius `R`
then every `d ≥ 1` with `g^d ∈ H` has `2d + 1 > R`.

**The second cycle** is `(a h)^n` closed up by a geodesic word for `(g^n)⁻¹`, of
length `2n + L` with `L = |g^n|`.  If `2n + L ≤ R` then no `h`-letter of the
alternating part is isolated in it, so each is connected to some other
component; by the first cycle it cannot be another `h`-letter of the alternating
part, so it is a component of the geodesic side, and distinct `h`-letters reach
distinct components.  Counting gives `L ≥ n - 1`.

`sub_one_le_wordDist` puts the two cases together: for `3n ≤ R + 1` the bound
`n - 1 ≤ |g^n|` holds, whether or not `2n + L ≤ R`.

## Where `a ∉ H` is spent

In exactly one place, and it is the place Dahmani--Guirardel--Osin spend their
condition `(W3)`: `g ∈ H` would make consecutive `h`-letters connected.  Their
Theorem 6.11 as printed omits `a ∉ H_λ` from its hypotheses, and without it the
statement is false --- take `H = G` finite with `X` a proper subset, so that
`d̂` is unbounded while nothing at all is loxodromic.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-! ## Connectedness along the alternating word -/

section Connected

variable {G : Type u} [Group G]

/-- **Conjugating by `a` is conjugating by `h⁻¹`, on powers of `a h`.**  For
`Y` commuting with `a h` --- which every power of `a h` does --- the two
conjugations agree.  This is what turns `Connected` at two `h`-letters of
`altWord a h n` into a statement about a power of `a h` lying in `H`. -/
theorem conj_inv_eq_conj_of_commute (a h Y : G)
    (hY : Y * (a * h) = (a * h) * Y) : a⁻¹ * Y * a = h * Y * h⁻¹ := by
  have hstep : a⁻¹ * Y * a * h = h * Y := by
    calc a⁻¹ * Y * a * h = a⁻¹ * (Y * (a * h)) := by group
      _ = a⁻¹ * ((a * h) * Y) := by rw [hY]
      _ = h * Y := by group
  rw [← hstep]
  group

/-- **Two `h`-letters of the alternating word are connected exactly when the
power of `a h` between them lies in `H`.**  The two initial vertices are
`(ah)^t a` and `(ah)^{t+d} a`, whose ratio is `a⁻¹ (ah)^d a = h (ah)^d h⁻¹`. -/
theorem connected_altWordAppend_iff (D : RelGenSet G Unit) {a h : G}
    (hh : h ∈ D.fam ()) (u : List (RelLetter G Unit)) {n t d : ℕ}
    (ht : t < n) (htd : t + d < n) :
    Connected D.fam () 1 (altWord a h n ++ u) (2 * t + 1) (2 * (t + d) + 1)
      ↔ (a * h) ^ d ∈ D.fam () := by
  have hv1 : vertex (1 : G) (altWord a h n ++ u) (2 * t + 1) = (a * h) ^ t * a := by
    rw [vertex_altWordAppend_two_mul_succ a h 1 u ht, one_mul]
  have hv2 : vertex (1 : G) (altWord a h n ++ u) (2 * (t + d) + 1)
      = (a * h) ^ (t + d) * a := by
    rw [vertex_altWordAppend_two_mul_succ a h 1 u htd, one_mul]
  show (vertex (1 : G) (altWord a h n ++ u) (2 * t + 1))⁻¹ *
      vertex (1 : G) (altWord a h n ++ u) (2 * (t + d) + 1) ∈ D.fam () ↔ _
  rw [hv1, hv2]
  have hcancel : ∀ X Y c : G, (X * c)⁻¹ * (X * Y * c) = c⁻¹ * Y * c := by
    intro X Y c
    group
  have hexp : ((a * h) ^ t * a)⁻¹ * ((a * h) ^ (t + d) * a)
      = a⁻¹ * (a * h) ^ d * a := by
    rw [pow_add]
    exact hcancel _ _ _
  have hconj : a⁻¹ * (a * h) ^ d * a = h * (a * h) ^ d * h⁻¹ :=
    conj_inv_eq_conj_of_commute a h ((a * h) ^ d)
      ((Commute.refl (a * h)).pow_left d).eq
  rw [hexp, hconj]
  constructor
  · intro hm
    have haux : ∀ Y : G, h⁻¹ * (h * Y * h⁻¹) * h = Y := by
      intro Y
      group
    have hmem := mul_mem (mul_mem (inv_mem hh) hm) hh
    rwa [haux] at hmem
  · intro hm
    exact mul_mem (mul_mem hh hm) (inv_mem hh)

end Connected

/-! ## The first cycle: a returning power is a long one -/

section FirstCycle

variable {G : Type u} [Group G]

/-- **The least returning power puts `h⁻¹` in a ball of radius `2m+1`.**

If `m` is least with `(a h)^m ∈ H`, the word `(a h)^m` closed up by the single
`H`-letter `((a h)^m)⁻¹` is a cycle of length `2m+1` in which the first
`h`-letter is isolated, and Dahmani--Guirardel--Osin's Lemma 4.6 converts that
into `d̂(1, h⁻¹) ≤ 2m+1`.

`a ∉ H` is what makes `m ≥ 2`, hence what makes the first `h`-letter a component
of its own inside the alternating part. -/
theorem inv_mem_relBall_of_minimal_pow_mem_fam (D : RelGenSet G Unit) {a h : G}
    (ha : a ∈ D.base) (haH : a ∉ D.fam ()) (hh : h ∈ D.fam ())
    {m : ℕ} (hmem : (a * h) ^ m ∈ D.fam ())
    (hmin : ∀ d : ℕ, 1 ≤ d → d < m → (a * h) ^ d ∉ D.fam ()) (hm1 : 1 ≤ m) :
    h⁻¹ ∈ D.relBall () (2 * m + 1) := by
  -- `m = 1` would put `a` in `H`
  have hm2 : 2 ≤ m := by
    by_contra hcon
    have hm : m = 1 := by omega
    subst hm
    rw [pow_one] at hmem
    have hain : a * h * h⁻¹ ∈ D.fam () := mul_mem hmem (inv_mem hh)
    rw [mul_inv_cancel_right] at hain
    exact haH hain
  set uu : List (RelLetter G Unit) := [RelLetter.comp () (((a * h) ^ m)⁻¹)] with huu
  set c : List (RelLetter G Unit) := altWord a h m ++ uu with hcdef
  have hlen : c.length = 2 * m + 1 := by
    rw [hcdef, List.length_append, length_altWord, huu]
    simp
  have hlet : ∀ x ∈ c, D.IsLetter x := by
    intro x hx
    rw [hcdef] at hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact isLetter_of_mem_altWord D ha hh m x hx'
    · rw [huu] at hx'
      rw [List.eq_of_mem_singleton hx']
      exact inv_mem hmem
  have hcl : RelLetter.listVal c = 1 := by
    rw [hcdef, listVal_append, listVal_altWord, huu]
    simp [RelLetter.listVal, RelLetter.val]
  have hcomp0 := isComp_altWordAppend a h uu (n := m) (t := 0) (by omega)
  have hcomp : IsComp () c 1 2 := by
    rw [hcdef]
    simpa using hcomp0
  have hv1 : vertex (1 : G) c 1 = a := by
    have hv := vertex_altWordAppend_two_mul_succ a h 1 uu (n := m) (t := 0) (by omega)
    rw [hcdef]
    simpa using hv
  have hv2 : vertex (1 : G) c 2 = a * h := by
    have hv := vertex_altWordAppend_two_mul a h 1 uu (n := m) (t := 1) (by omega)
    rw [hcdef]
    simpa using hv
  have hiso : IsIsolated D.fam () 1 c 1 := by
    refine ⟨⟨2, hcomp⟩, ?_⟩
    intro j hj hstart hconn
    have hjlen : j < c.length := by
      obtain ⟨k, hk⟩ := hstart
      have h1 := hk.1
      have h2 := hk.2.1
      omega
    rcases Nat.lt_or_ge j (2 * m) with hlt | hge
    · -- inside the alternating part: `j` is odd, and connectedness returns a power
      have hodd : j % 2 = 1 := by
        rw [hcdef] at hstart
        exact odd_of_isCompStart_lt a h uu hlt hstart
      set s : ℕ := j / 2 with hs
      have hjs : j = 2 * s + 1 := by omega
      have hs1 : 1 ≤ s := by omega
      have hsm : s < m := by omega
      have hconn' : Connected D.fam () 1 (altWord a h m ++ uu)
          (2 * 0 + 1) (2 * (0 + s) + 1) := by
        rw [hcdef] at hconn
        have hidx : 2 * (0 + s) + 1 = j := by omega
        have hidx0 : 2 * 0 + 1 = 1 := by omega
        rw [hidx, hidx0]
        exact hconn
      exact hmin s hs1 hsm
        ((connected_altWordAppend_iff D hh uu (n := m) (t := 0) (d := s)
          (by omega) (by omega)).mp hconn')
    · -- the closing letter is not a component start
      have hj2m : j = 2 * m := by omega
      subst hj2m
      rw [hcdef] at hstart
      exact not_isCompStart_of_even_pos a h uu (n := m) (j := 2 * m)
        (by omega) (le_refl _) (by omega) hstart
  have hball := relBall_inv_of_isolated_of_closed D () (1 : G) hlet hcl hcomp hiso
  rw [hv1, hv2, hlen] at hball
  have hspan : a⁻¹ * (a * h) = h := by group
  rwa [hspan] at hball

/-- **If `h` is far, every returning power is late.**  Contrapositive of the
first cycle, at the least returning power. -/
theorem lt_two_mul_add_one_of_pow_mem_fam (D : RelGenSet G Unit) {a h : G}
    (ha : a ∈ D.base) (haH : a ∉ D.fam ()) (hh : h ∈ D.fam ())
    {R : ℕ} (hnb : h⁻¹ ∉ D.relBall () R) {d : ℕ} (hd1 : 1 ≤ d)
    (hd : (a * h) ^ d ∈ D.fam ()) : R < 2 * d + 1 := by
  classical
  have hex : ∃ m : ℕ, 1 ≤ m ∧ (a * h) ^ m ∈ D.fam () := ⟨d, hd1, hd⟩
  have hspec := Nat.find_spec hex
  have hmd : Nat.find hex ≤ d := Nat.find_le ⟨hd1, hd⟩
  have hmin : ∀ k : ℕ, 1 ≤ k → k < Nat.find hex → (a * h) ^ k ∉ D.fam () := by
    intro k hk1 hk2 hkm
    exact Nat.find_min hex hk2 ⟨hk1, hkm⟩
  have hball := inv_mem_relBall_of_minimal_pow_mem_fam D ha haH hh hspec.2 hmin hspec.1
  by_contra hcon
  have hle : 2 * Nat.find hex + 1 ≤ R := by omega
  exact hnb (relBall_mono_radius D () hle hball)

end FirstCycle

/-! ## The second cycle: `(a h)^n` is long -/

section SecondCycle

variable {G : Type u} [Group G]

/-- **The alternating word is long, on the window `h` is far enough to cover.**

For `3n ≤ R + 1` the word `(a h)^n` has length at least `n - 1` in
`Γ(G, X ⊔ ℋ)`.  Either the cycle `(a h)^n · u` --- with `u` a geodesic word for
`((a h)^n)⁻¹` --- is longer than `R`, and then `|(a h)^n| ≥ n` outright; or it is
not, and then no `h`-letter of the alternating part can be isolated in it, so
each is connected to a distinct component of `u`. -/
theorem sub_one_le_wordDist (D : RelGenSet G Unit) {a h : G}
    (ha : a ∈ D.base) (haH : a ∉ D.fam ()) (hh : h ∈ D.fam ())
    {R : ℕ} (hnb : h⁻¹ ∉ D.relBall () R) {n : ℕ} (hn : 3 * n ≤ R + 1) :
    n - 1 ≤ wordDist D.alphabet.carrier 1 ((a * h) ^ n) := by
  set L : ℕ := wordDist D.alphabet.carrier 1 ((a * h) ^ n) with hL
  rcases Nat.lt_or_ge R (2 * n + L) with hbig | hle
  · omega
  -- the geodesic word for `((a h)^n)⁻¹`, spelled by admissible letters
  obtain ⟨l, hl, hllen⟩ :=
    exists_isWord_length_eq D.alphabet.symmetricGenerating (((a * h) ^ n)⁻¹)
  obtain ⟨u, hulet, huval, hulen⟩ := exists_relWord D l hl.letters
  have hlL : l.length = L := by
    rw [hllen, wordNorm_inv D.alphabet.symmetricGenerating, hL, wordDist_one_left]
  have huL : u.length = L := by rw [hulen, hlL]
  have huprod : RelLetter.listVal u = ((a * h) ^ n)⁻¹ := by
    rw [huval, hl.prod_eq]
  set c : List (RelLetter G Unit) := altWord a h n ++ u with hcdef
  have hclen : c.length = 2 * n + L := by
    rw [hcdef, List.length_append, length_altWord, huL]
  have hlet : ∀ x ∈ c, D.IsLetter x := by
    intro x hx
    rw [hcdef] at hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact isLetter_of_mem_altWord D ha hh n x hx'
    · exact hulet x hx'
  have hcl : RelLetter.listVal c = 1 := by
    rw [hcdef, listVal_append, listVal_altWord, huprod, mul_inv_cancel]
  -- two `h`-letters of the alternating part are never connected
  have hnotconn : ∀ t s : ℕ, t < n → s < n → t ≠ s →
      ¬ Connected D.fam () 1 c (2 * t + 1) (2 * s + 1) := by
    have hkey : ∀ t s : ℕ, t < n → s < n → t < s →
        ¬ Connected D.fam () 1 c (2 * t + 1) (2 * s + 1) := by
      intro t s ht hs hts hconn
      have hidx : 2 * (t + (s - t)) + 1 = 2 * s + 1 := by omega
      rw [hcdef, ← hidx] at hconn
      have hpow : (a * h) ^ (s - t) ∈ D.fam () :=
        (connected_altWordAppend_iff D hh u (n := n) (t := t) (d := s - t) ht
          (by omega)).mp hconn
      have hlt := lt_two_mul_add_one_of_pow_mem_fam D ha haH hh hnb
        (d := s - t) (by omega) hpow
      omega
    intro t s ht hs hne hconn
    rcases Nat.lt_or_ge t s with hts | hst
    · exact hkey t s ht hs hts hconn
    · exact hkey s t hs ht (by omega) (connected_symm hconn)
  -- no `h`-letter of the alternating part is isolated in the cycle
  have hall : ∀ t : ℕ, ∃ j : ℕ, t + 1 < n →
      (2 * n ≤ j ∧ j < 2 * n + L) ∧ Connected D.fam () 1 c (2 * t + 1) j := by
    intro t
    by_cases htn : t + 1 < n
    · have hcomp : IsComp () c (2 * t + 1) (2 * t + 2) := by
        rw [hcdef]
        exact isComp_altWordAppend a h u htn
      have hnotiso : ¬ IsIsolated D.fam () 1 c (2 * t + 1) := by
        intro hiso
        have hball := relBall_inv_of_isolated_of_closed D () (1 : G) hlet hcl hcomp hiso
        have hv1 : vertex (1 : G) c (2 * t + 1) = (a * h) ^ t * a := by
          rw [hcdef, vertex_altWordAppend_two_mul_succ a h 1 u (by omega), one_mul]
        have hv2 : vertex (1 : G) c (2 * t + 2) = (a * h) ^ (t + 1) := by
          have hidx : 2 * t + 2 = 2 * (t + 1) := by ring
          rw [hcdef, hidx, vertex_altWordAppend_two_mul a h 1 u (by omega), one_mul]
        have hspan : ((a * h) ^ t * a)⁻¹ * (a * h) ^ (t + 1) = h := by
          have haux : ∀ Y : G, (Y * a)⁻¹ * (Y * (a * h)) = h := by
            intro Y
            group
          rw [pow_succ]
          exact haux _
        rw [hv1, hv2, hspan, hclen] at hball
        exact hnb (relBall_mono_radius D () hle hball)
      have hex : ∃ j : ℕ, j ≠ 2 * t + 1 ∧ IsCompStart () c j ∧
          Connected D.fam () 1 c (2 * t + 1) j := by
        by_contra hno
        push Not at hno
        exact hnotiso ⟨⟨2 * t + 2, hcomp⟩, fun j hj hjst => hno j hj hjst⟩
      obtain ⟨j, hjne, hjstart, hjconn⟩ := hex
      refine ⟨j, fun _ => ⟨⟨?_, ?_⟩, hjconn⟩⟩
      · by_contra hjlt
        have hodd : j % 2 = 1 := by
          rw [hcdef] at hjstart
          exact odd_of_isCompStart_lt a h u (by omega) hjstart
        have hjs : j = 2 * (j / 2) + 1 := by omega
        refine hnotconn t (j / 2) (by omega) (by omega) (by omega) ?_
        rw [← hjs]
        exact hjconn
      · obtain ⟨kk, hk⟩ := hjstart
        have h1 := hk.1
        have h2 := hk.2.1
        omega
    · exact ⟨0, fun hc => absurd hc htn⟩
  choose F hF using hall
  -- distinct `h`-letters reach distinct components of the geodesic side
  have hcard : (Finset.range (n - 1)).card
      ≤ (Finset.Ico (2 * n) (2 * n + L)).card := by
    refine Finset.card_le_card_of_injOn F ?_ ?_
    · intro t ht
      simp only [Finset.coe_range, Set.mem_Iio] at ht
      simp only [Finset.coe_Ico, Set.mem_Ico]
      exact (hF t (by omega)).1
    · intro t ht t' ht' heq
      simp only [Finset.coe_range, Set.mem_Iio] at ht ht'
      by_contra hne
      refine hnotconn t t' (by omega) (by omega) hne ?_
      have h1 := (hF t (by omega)).2
      have h2 := (hF t' (by omega)).2
      rw [heq] at h1
      exact connected_trans h1 (connected_symm h2)
  rw [Finset.card_range, Nat.card_Ico] at hcard
  omega

end SecondCycle

end OsinComponents
end GGT
end GroupApproximation
