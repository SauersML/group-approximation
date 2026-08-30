import GroupApproximation.GGT.DGOBlockWord
import GroupApproximation.GGT.DGOWWordConditions

/-!
# Dahmani--Guirardel--Osin's Lemma 4.21: the `W`-words and both clauses

Lemma 4.21 is the gate under every remaining clause of the Hull route --- WPD of
the elements Corollary 6.12 manufactures, their pairwise non-commensurability,
`yi`'s own main step, and `nonelsub`'s `E_G(f) = E_G⁺(f)`.  Both of its clauses
are proved from Proposition 4.14 with the constant uniform in the number of
sides, which is what the 4.14 campaign is building.  This module is the
statement layer: the class of words the lemma is about, and clause (a).

## The class `W`, verbatim (p. 42)

> Let `W` be the set consisting of all words `U` in `X ⊔ H` such that:
> **(W1)** `U` contains no subwords of type `xy`, where `x, y ∈ X`.
> **(W2)** If `U` contains a letter `h ∈ H_λ` for some `λ ∈ Λ`, then
> `d̂_λ(1,h) > 50D`, where `D = D(1,0)` is given by Proposition 4.14.
> **(W3)** If `h₁ x h₂` (respectively, `h₁ h₂`) is a subword of `U`, where
> `x ∈ X`, `h₁ ∈ H_λ`, `h₂ ∈ H_μ`, then either `λ ≠ μ` or the element
> represented by `x` in `G` does not belong to `H_λ` (respectively, `λ ≠ μ`).

The class itself is **not defined here**.  `GGT.WWord.IsWOne`, `IsWTwo` and
`IsWThree` (`GGT/DGOWWordConditions.lean`) are the three conditions, indexed by
position and phrased with `getElem?`, and this module states Lemma 4.21 against
them.  I had written a competing bundled `IsWWord` in this file and retired it:
two encodings of one class is the rot both lanes have been guarding against, and
theirs is the better encoding --- `w[i]? = some (RelLetter.base x)` carries no
bound proof, so it needs none of the `Nat.lt_of_succ_lt` plumbing a
`getElem`-with-proof form drags into every clause, and splitting the three
conditions lets a consumer take only what it needs.

The lemma assumes only weak relative hyperbolicity, encoded below by the
existence of a hyperbolicity constant for `Cayley D.alphabet`.  In particular,
neither clause asks for `D.IsHyperbolicallyEmbedded.locallyFinite`; requiring
that second field would strengthen the printed hypothesis for no reason.

(W2) is ball non-membership rather than metric, because `d̂_λ` takes the value
`∞` (their Remark 6.10) and the metric form would be wrong here for the same
reason it is wrong in `GGT.DGOTheorem611`.  The threshold is a parameter, not
`50D`, because `D` is exactly what the 4.14 campaign has not landed.

## Which words in this repository are `W`-words

`GGT.DGOBlockWord.blockWord lam w h n` is the word `(w h)^n`, and whether it
lies in `W` depends entirely on the spelling `w`:

* `w = [base a]`, one `X`-letter --- **yes**, and this is
  Dahmani--Guirardel--Osin's own case, the word `(ah)^N` of their Theorem 6.11.
  The three `blockWord_singleBase` lemmas below prove it, from `a ∉ H lam`
  and `h` deep.
* `w` a word of `μ`-letters with `μ ≠ lam` throughout and consecutive indices
  distinct --- **yes**, vacuously for (W1), since such a word has no `X`-letters
  at all.  This is Hull's `yi`, whose `g = a₁ ⋯ a_{k-1}` is spelled by letters
  of distinct peripheral factors.
* `w` a word of **two or more `X`-letters** --- **no**.  (W1) fails outright at
  the first adjacent pair.  This is Hull's `nonelsub`, whose `g` is an arbitrary
  element of `⟨𝒜⟩`.

That third line is a real obstruction and not a technicality, so it is recorded
here rather than discovered later.  Dahmani--Guirardel--Osin never meet it
because their Corollary 4.27 lets them enlarge `X` by the finitely many letters
they need and so assume `a ∈ X` outright; `GGT.DGOCorollary427` is that
statement, and it is an unproved citation in this repository.  The alternative
is to relax (W1) to *runs of `X`-letters of length at most `r`*, which should
cost only the quasi-geodesic constant --- `(4,1)` becoming roughly
`(4(1+r), 1)`, since their normal form `p = r₀p₁r₁ ⋯ pₘrₘ` would carry `rᵢ` of
length up to `r` instead of at most one --- but that relaxation is not in the
paper and would have to be redone rather than cited.

So a consumer wanting WPD or non-commensurability for `g h` with `g` spelled by
several `X`-letters needs one of those two, over and above the 4.14 campaign.
Nothing in `GGT.DGOCorollary612Threshold` depends on this: its loxodromy clause
is proved without 4.21 at all.

## The route past (W1): enlarge `X`, do not relax the condition

Both escapes were costed and the enlargement wins.  `GGT.DGOCorollary427`
quantifies over the **base** with the **family fixed** --- its statement is
`D₁.fam = D₂.fam → (D₁.base △ D₂.base).Finite → (↪_h ↔ ↪_h)` --- so applying it
at a cone-off is not a special case: the cone-off *is* the family, and it does
not move.  Taking `X₂ = X ∪ {g^{±1}}` makes `g` a single letter, the word
becomes Dahmani--Guirardel--Osin's own `(a h)^N`, and the three
`blockWord_singleBase` lemmas apply.  Loxodromy comes back down to the original alphabet by Hull's
Lemma A1, `GGT.HullYiAlphabetTransfer.isLoxodromic_base_of_subset`.

That is the source's own move --- *"By Corollary 4.27 we can assume that `t ∈ X`
without loss of generality"* (p. 51), and again for a finite set at p. 96 --- so
it is cited rather than redone, and the same citation is owed elsewhere in the
tree.  Relaxing (W1) would instead prove a variant and call it 4.21.

The relaxation was priced before being rejected, and one thing found in the
pricing is worth keeping in case anyone revisits it: **relaxing (W1) forces
relaxing (W3) too.**  (W3) covers only `h₁h₂` and `h₁xh₂`, so with two or more
`X`-letters between two `H`-letters no clause of it applies at all, and
"no two consecutive components of `p` are connected" --- which their proof
asserts from (W3) --- would have nothing under it.

## Clause (b), and one form it must not be confused with

`DGOLemma421b` is stated in the shape its consumers use.  Three encodings were
settled by asking rather than guessing, and the first of them is *printed*:
"consecutive" is not left to the reader, since (b)'s conclusion is the
decomposition `p = x₀a₁ ⋯ x_{K-1}a_Kx_K` with the `xᵢ` *"edges labelled by
elements of `X` or trivial paths"*.  `BaseEdgeOrTrivial` below records this
exact disjunction.  The connection is a **coset identity across
two words read from two basepoints**, stated at the component *starts* because
Hull's `yi` names the connecting element; and the indices are functions rather
than a `Finset`, because the pairing `aᵢ ↔ bᵢ` is consumed index by index.
They are `ℕ → ℕ` guarded by `t < K` rather than `Fin K → ℕ`, so that the
consecutiveness clause needs no `Fin` successor arithmetic at any consumption
site; `lt_of_isComp_of_baseEdgeOrTrivial` supplies the strict ordering the
`Fin K` form would have asserted, and composing with `Fin.val` recovers that
form for a consumer who prefers it.

Merely requiring `kp t ≤ ip (t+1) ≤ kp t + 1` would be a genuine weakening:
it would also permit the intervening letter to be an `H_ν`-letter.  The
statement below excludes that case, as the printed decomposition does.

**The end form follows from the start form** and is not stated: a component's
span lies in its own family member (`OsinComponents.span_mem_fam_of_isComp`), so
`(vertex vp p (kp t))⁻¹ * vertex vq q (kq t)` is the product of that span's
inverse, the start-form element, and the other span --- three elements of
`D.fam (lam t)`.

**This is not the refuted start-to-start form.**
`GGT.DGOIsolatedComponentCut` shows that no bound on `d̂` holds for the element
between two connected component *starts* --- of **one** word, and as a *bound*.
Clause (b) asserts something different twice over: its two components lie in
**two different words read from different basepoints**, and what it asserts is
**membership in `H λ`**, not a relative-ball bound.  The two are one `rw` apart
in appearance and a theorem apart in truth.

## The three `open` lines are load-bearing

`IsHyperbolicSpace` lives in `GroupApproximation.HullGeometry` and `Cayley` in
`GroupApproximation.Manuscript.NonMF.TorsionFree`.  Both modules are already in
this file's import closure, so the `unknownIdentifier` errors their absence
produces are a **name** out of scope, not a **module** missing: the cure is an
`open`, and adding an import instead buys an edge the closure already has.
Lean reports only the first such identifier per elaboration, so the second one
costs another probe unless every new name is checked in one pass.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section WWords

variable {G : Type u} [Group G] {Λ : Type w}

/-- The separator between two consecutive distinguished components in
Lemma 4.21(b): a trivial path, or exactly one edge labelled by an element of
the relative base `X`. -/
def BaseEdgeOrTrivial (w : List (RelLetter G Λ)) (k i : ℕ) : Prop :=
  i = k ∨ ∃ x : G, i = k + 1 ∧ w[k]? = some (RelLetter.base x)

/-- **Lemma 4.21(a)**: every path labelled by a word of `W` is
`(4,1)`-quasi-geodesic.

Stated over `ℕ` on the vertex metric, `(4,1)` reading `(j - i)/4 - 1 ≤ d`, i.e.
`j - i ≤ 4d + 4`.  The threshold `C` is existentially bound and depends on `D`
alone, being their `50 D(1,0)`.

This is *not* free once the words are known to satisfy `(W1)`--`(W3)`: its proof
counts the components of the path that are isolated in the geodesic
`(2m+2)`-gon obtained by closing the path with a geodesic, and bounds their
number by Proposition 4.14 with the constant uniform in the side count.  So
clause (a) is blocked on the same input as clause (b). -/
def DGOLemma421a : Prop :=
  ∀ (G : Type u) [Group G] (Λ : Type w) (D : RelGenSet G Λ),
    (∃ δ : ℝ, IsHyperbolicSpace δ (Cayley D.alphabet)) → ∃ C : ℕ,
      ∀ (v : G) (u : List (RelLetter G Λ)), (∀ a ∈ u, D.IsLetter a) →
        WWord.IsWOne u → WWord.IsWTwo D C u → WWord.IsWThree D u →
          ∀ i j : ℕ, i ≤ j → j ≤ u.length →
          j - i ≤ 4 * wordDist D.alphabet.carrier
            (vertex v u i) (vertex v u j) + 4

/-- **Lemma 4.21(b)**: two long `W`-labelled paths that fellow-travel have `K`
consecutive components connected in pairs.

> For every `ε > 0` and every integer `K > 0`, there exists `R = R(ε,K) > 0`
> satisfying the following condition.  Let `p, q` be two paths in
> `Γ(G, X ⊔ H)` such that `ℓ(p) ≥ R`, `Lab(p), Lab(q) ∈ W`, and `p, q` are
> oriented `ε`-close.  Then there exist `K` consecutive components of `p` which
> are connected to `K` consecutive components of `q`.

`ip t` and `kp t` bracket the `t`-th distinguished component of `p`, and
`iq t`, `kq t` that of `q`.  `BaseEdgeOrTrivial p (kp t) (ip (t+1))` is
Dahmani--Guirardel--Osin's `xᵢ` being an `X`-edge or a trivial path.  Strict
monotonicity of `ip` is a consequence rather than a hypothesis, since `IsComp`
already gives `ip t < kp t`.

The connection is stated at the starts, as a coset identity between the two
words read from their own basepoints.  The corresponding identity at the ends
follows, a component's two endpoints differing by its own label, which lies in
`H (lam t)`. -/
def DGOLemma421b : Prop :=
  ∀ (G : Type u) [Group G] (Λ : Type w) (D : RelGenSet G Λ),
    (∃ δ : ℝ, IsHyperbolicSpace δ (Cayley D.alphabet)) →
      ∃ C : ℕ, ∀ (eps : ℝ) (K : ℕ),
      0 < eps → 0 < K → ∃ R : ℕ, 0 < R ∧
      ∀ (vp vq : G) (p q : List (RelLetter G Λ)),
        (∀ c ∈ p, D.IsLetter c) → (∀ c ∈ q, D.IsLetter c) →
        WWord.IsWOne p → WWord.IsWTwo D C p → WWord.IsWThree D p →
        WWord.IsWOne q → WWord.IsWTwo D C q → WWord.IsWThree D q →
        R ≤ p.length →
        (wordDist D.alphabet.carrier vp vq : ℝ) ≤ eps →
        (wordDist D.alphabet.carrier (vertex vp p p.length)
          (vertex vq q q.length) : ℝ) ≤ eps →
        ∃ (ip kp iq kq : ℕ → ℕ) (lam : ℕ → Λ),
          (∀ t : ℕ, t < K → IsComp (lam t) p (ip t) (kp t)) ∧
          (∀ t : ℕ, t < K → IsComp (lam t) q (iq t) (kq t)) ∧
          (∀ t : ℕ, t + 1 < K → BaseEdgeOrTrivial p (kp t) (ip (t + 1))) ∧
          (∀ t : ℕ, t + 1 < K → BaseEdgeOrTrivial q (kq t) (iq (t + 1))) ∧
          (∀ t : ℕ, t < K →
            (vertex vp p (ip t))⁻¹ * vertex vq q (iq t) ∈ D.fam (lam t))

omit [Group G] in
/-- An `X`-edge-or-trivial separator begins no earlier than the preceding
component endpoint. -/
theorem BaseEdgeOrTrivial.le {w : List (RelLetter G Λ)} {k i : ℕ}
    (h : BaseEdgeOrTrivial w k i) : k ≤ i := by
  rcases h with rfl | ⟨_, rfl, -⟩
  · exact le_rfl
  · omega

omit [Group G] in
/-- **Strict monotonicity of the index functions is a consequence, not a
clause.**  `IsComp` already gives `ip t < kp t`, and the printed separator
condition gives `kp t ≤ ip (t+1)`; together they order the distinguished
components strictly.

Stated separately so that `DGOLemma421b` need not assert it --- a named `Prop`
that will one day be proved should carry no redundant conjunct, and a consumer
that wants the ordering should not have to derive it.  Consumers wanting the
`Fin K`-indexed form get it by composing with `Fin.val`. -/
theorem lt_of_isComp_of_baseEdgeOrTrivial
    {p : List (RelLetter G Λ)} {lam : ℕ → Λ}
    {ip kp : ℕ → ℕ} {K : ℕ}
    (hcomp : ∀ t : ℕ, t < K → IsComp (lam t) p (ip t) (kp t))
    (hstep : ∀ t : ℕ, t + 1 < K →
      BaseEdgeOrTrivial p (kp t) (ip (t + 1))) :
    ∀ t s : ℕ, t < s → s < K → ip t < ip s := by
  intro t s hts hsK
  induction s with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge t n with hlt | hge
      · have hn : ip t < ip n := ih hlt (by omega)
        have h1 : ip n < kp n := (hcomp n (by omega)).1
        have h2 : kp n ≤ ip (n + 1) := (hstep n (by omega)).le
        omega
      · have htn : t = n := by omega
        subst htn
        have h1 : ip t < kp t := (hcomp t (by omega)).1
        have h2 : kp t ≤ ip (t + 1) := (hstep t (by omega)).le
        omega

omit [Group G] in
/-- **The converter between the two encodings of a letter, and the only one.**
`IsComp` is stated with `getElem`-with-proof, since a component's positions come
with the bounds that produced them; `(W1)`--`(W3)` are stated with `getElem?`,
so that no clause carries a bound proof.  Every consumer that holds a component
and wants a condition -- or holds a condition and wants a component -- crosses
that seam here.

Use this rather than inlining the `cases` on the letter.  There is one seam and
there should be one bridge over it: a second converter would be provable, would
be phrased slightly differently, and the two would drift. -/
theorem getElem?_comp_of_isCompOf {w : List (RelLetter G Λ)} {lam : Λ} {j : ℕ}
    (hj : j < w.length) (h : (w[j]'hj).IsCompOf lam) :
    ∃ g : G, w[j]? = some (RelLetter.comp lam g) := by
  have hg : w[j]? = some (w[j]'hj) := List.getElem?_eq_getElem hj
  cases hcase : w[j]'hj with
  | base x =>
      rw [hcase] at h
      simp [RelLetter.IsCompOf] at h
  | comp mu g =>
      rw [hcase] at h
      simp only [RelLetter.IsCompOf] at h
      exact ⟨g, by rw [hg, hcase, h]⟩

/-- **Every component of a `(W3)` word is a single letter.**  Two adjacent
letters of one `H lam` are exactly what the first half of (W3) forbids, so a
maximal run of `lam`-letters can never reach length two.

This is why a consumer of Proposition 4.14 on the 4.21 route never has to
discharge the single-edge clause on the distinguished sides: the components
Lemma 4.21 hands to the polygon are single edges already. -/
theorem isComp_succ_of_isWThree {D : RelGenSet G Λ} {w : List (RelLetter G Λ)}
    (hw : WWord.IsWThree D w) {lam : Λ} {i k : ℕ} (h : IsComp lam w i k) :
    k = i + 1 := by
  obtain ⟨hik, hkw, hall, -, -⟩ := h
  by_contra hne
  have hi : i < w.length := by omega
  have hi1 : i + 1 < w.length := by omega
  obtain ⟨g₁, hg₁⟩ := getElem?_comp_of_isCompOf hi (hall i le_rfl (by omega) hi)
  obtain ⟨g₂, hg₂⟩ :=
    getElem?_comp_of_isCompOf hi1 (hall (i + 1) (by omega) (by omega) hi1)
  exact hw.1 i lam lam g₁ g₂ hg₁ hg₂ rfl

end WWords

/-! ## The alternating word is a `W`-word -/

section BridgeCombinatorics

variable {G : Type u} {Λ : Type w}

/-- The bound implicit in a `getElem?` that is `some`. -/
theorem lt_length_of_getElem?_eq_some {α : Type u} {l : List α} {i : ℕ} {x : α}
    (hx : l[i]? = some x) : i < l.length := by
  by_contra hcon
  rw [List.getElem?_eq_none (by omega)] at hx
  simp at hx

theorem getElem?_singleBase_even (lam : Λ) (a h : G) (n j : ℕ)
    (hjn : j < 2 * n) (hj : j % 2 = 0) :
    (blockWord lam [RelLetter.base a] h n)[j]? = some (RelLetter.base a) := by
  obtain ⟨t, rfl⟩ : ∃ t, j = t * 2 := ⟨j / 2, by omega⟩
  have htn : t < n := by omega
  have hg := getElem?_blockWord_pre lam ([RelLetter.base a] : List (RelLetter G Λ))
    h (n := n) (t := t) (j := 0) htn (by simp)
  simpa using hg

theorem getElem?_singleBase_odd (lam : Λ) (a h : G) (n j : ℕ)
    (hjn : j < 2 * n) (hj : j % 2 = 1) :
    (blockWord lam [RelLetter.base a] h n)[j]? = some (RelLetter.comp lam h) := by
  obtain ⟨t, rfl⟩ : ∃ t, j = t * 2 + 1 := ⟨j / 2, by omega⟩
  have htn : t < n := by omega
  have hg := getElem?_blockWord_comp lam
    ([RelLetter.base a] : List (RelLetter G Λ)) h (n := n) (t := t) htn
  simpa using hg

theorem getElem_singleBase_even (lam : Λ) (a h : G) (n j : ℕ)
    (hjn : j < 2 * n) (hj : j % 2 = 0)
    (hlt : j < (blockWord lam [RelLetter.base a] h n).length) :
    (blockWord lam [RelLetter.base a] h n)[j]'hlt = RelLetter.base a :=
  getElem_eq_of_getElem?_eq hlt (getElem?_singleBase_even lam a h n j hjn hj)

theorem getElem_singleBase_odd (lam : Λ) (a h : G) (n j : ℕ)
    (hjn : j < 2 * n) (hj : j % 2 = 1)
    (hlt : j < (blockWord lam [RelLetter.base a] h n).length) :
    (blockWord lam [RelLetter.base a] h n)[j]'hlt = RelLetter.comp lam h :=
  getElem_eq_of_getElem?_eq hlt (getElem?_singleBase_odd lam a h n j hjn hj)

end BridgeCombinatorics

section Bridge

variable {G : Type u} [Group G] {Λ : Type w}

omit [Group G] in
/-- **The word `(a h)^n` satisfies (W1)** --- its letters alternate, so no two
consecutive positions both carry `X`-letters. -/
theorem isWOne_blockWord_singleBase (lam : Λ) (a h : G) (n : ℕ) :
    WWord.IsWOne (blockWord lam [RelLetter.base a] h n) := by
  intro i x y hx hy
  have hlen : (blockWord lam [RelLetter.base a] h n).length = 2 * n := by
    rw [length_blockWord, List.length_singleton]
    ring
  have hi1 : i + 1 < 2 * n := by
    have hb := lt_length_of_getElem?_eq_some hy
    omega
  have h2 : i % 2 = 0 ∨ i % 2 = 1 := by omega
  rcases h2 with h2 | h2
  · rw [getElem?_singleBase_odd lam a h n (i + 1) (by omega) (by omega)] at hy
    simp at hy
  · rw [getElem?_singleBase_odd lam a h n i (by omega) h2] at hx
    simp at hx

/-- **The word `(a h)^n` satisfies (W2)** when `h` is deep: its only `H`-letter
is `h`. -/
theorem isWTwo_blockWord_singleBase (D : RelGenSet G Λ) (lam : Λ) {a h : G}
    {C : ℕ} (hh : h ∉ D.relBall lam C) (n : ℕ) :
    WWord.IsWTwo D C (blockWord lam [RelLetter.base a] h n) := by
  intro i mu h' hx
  have hlen : (blockWord lam [RelLetter.base a] h n).length = 2 * n := by
    rw [length_blockWord, List.length_singleton]
    ring
  have hi : i < 2 * n := by
    have hb := lt_length_of_getElem?_eq_some hx
    omega
  have h2 : i % 2 = 0 ∨ i % 2 = 1 := by omega
  rcases h2 with h2 | h2
  · rw [getElem?_singleBase_even lam a h n i hi h2] at hx
    simp at hx
  · rw [getElem?_singleBase_odd lam a h n i hi h2] at hx
    simp only [Option.some.injEq, RelLetter.comp.injEq] at hx
    rw [← hx.1, ← hx.2]
    exact hh

/-- **The word `(a h)^n` satisfies (W3)** when `a ∉ H lam`.  The adjacent case is
vacuous, the letters alternating; the separated case is the hypothesis, the
intervening `X`-letter being `a` --- which is the clause
`GGT.DGOTheorem611Refutation` shows cannot be dropped. -/
theorem isWThree_blockWord_singleBase (D : RelGenSet G Λ) (lam : Λ) {a h : G}
    (haH : a ∉ D.fam lam) (n : ℕ) :
    WWord.IsWThree D (blockWord lam [RelLetter.base a] h n) := by
  have hlen : (blockWord lam [RelLetter.base a] h n).length = 2 * n := by
    rw [length_blockWord, List.length_singleton]
    ring
  constructor
  · intro i mu nu h₁ h₂ hx hy
    have hi1 : i + 1 < 2 * n := by
      have hb := lt_length_of_getElem?_eq_some hy
      omega
    have h2 : i % 2 = 0 ∨ i % 2 = 1 := by omega
    rcases h2 with h2 | h2
    · rw [getElem?_singleBase_even lam a h n i (by omega) h2] at hx
      simp at hx
    · rw [getElem?_singleBase_even lam a h n (i + 1) (by omega) (by omega)] at hy
      simp at hy
  · intro i mu nu h₁ h₂ x hx hy hz
    have hi2 : i + 2 < 2 * n := by
      have hb := lt_length_of_getElem?_eq_some hz
      omega
    have h2 : i % 2 = 0 ∨ i % 2 = 1 := by omega
    rcases h2 with h2 | h2
    · rw [getElem?_singleBase_even lam a h n i (by omega) h2] at hx
      simp at hx
    · refine Or.inr ?_
      have hml : lam = mu := by
        rw [getElem?_singleBase_odd lam a h n i (by omega) h2] at hx
        simp only [Option.some.injEq, RelLetter.comp.injEq] at hx
        exact hx.1
      have hxa : x = a := by
        rw [getElem?_singleBase_even lam a h n (i + 1) (by omega) (by omega)] at hy
        simp only [Option.some.injEq, RelLetter.base.injEq] at hy
        exact hy.symm
      rw [hxa, ← hml]
      exact haH

/-! ## The alternating word at a subgroup prefix: Hull's `yi`

`blockWord lam pre h n` with `pre` a list of *subgroup* letters is Hull's word
`(a₁ ⋯ a_k)^n`, each `aᵢ` a letter of a different peripheral factor: `pre`
carries `a₁, …, a_{k-1}` and the block's closing letter is `a_k`.  The three
conditions come out of four hypotheses on `pre` and one on `h`, and (W1) is
free rather than assumed --- a word with no `X`-letters at all cannot contain
two of them in a row, which is why `yi` never meets the obstruction that stops
`nonelsub`.

The cyclic hypotheses are the load-bearing ones: consecutive indices must
differ **inside** `pre`, at the seam from `pre`'s last letter to `h`, and at the
wrap from `h` back to `pre`'s first letter.  `pre ≠ []` cannot be dropped: at
`pre = []` the word is `h^n`, whose adjacent letters share the index `lam`, and
(W3) is false for `n ≥ 2`. -/

/-- A position of a block word decomposes as a block index and an offset. -/
theorem exists_block_decomp (m : ℕ) {n i : ℕ} (hi : i < n * (m + 1)) :
    ∃ t r : ℕ, i = t * (m + 1) + r ∧ t < n ∧ r < m + 1 :=
  ⟨i / (m + 1), i % (m + 1), (Nat.div_add_mod' i (m + 1)).symm,
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi),
    Nat.mod_lt _ (Nat.succ_pos m)⟩

omit [Group G] in
/-- **A block word over a subgroup prefix has no `X`-letters.**  Every position
is either a letter of `pre` or the block's closing subgroup letter. -/
theorem getElem?_blockWord_ne_base (lam : Λ) {pre : List (RelLetter G Λ)}
    (hbase : ∀ (j : ℕ) (y : G), pre[j]? ≠ some (RelLetter.base y))
    (h : G) (n i : ℕ) (x : G) :
    (blockWord lam pre h n)[i]? ≠ some (RelLetter.base x) := by
  intro hx
  have hi : i < (blockWord lam pre h n).length :=
    lt_length_of_getElem?_eq_some hx
  rw [length_blockWord] at hi
  obtain ⟨t, r, rfl, htn, hrm⟩ := exists_block_decomp pre.length hi
  rcases Nat.lt_or_ge r pre.length with hr | hr
  · rw [getElem?_blockWord_pre lam pre h htn hr] at hx
    exact hbase r x hx
  · have hrm' : r = pre.length := by omega
    subst hrm'
    rw [getElem?_blockWord_comp lam pre h htn] at hx
    simp at hx

omit [Group G] in
/-- **(W1) is free at a subgroup prefix.** -/
theorem isWOne_blockWord_of_noBase (lam : Λ) {pre : List (RelLetter G Λ)}
    (hbase : ∀ (j : ℕ) (y : G), pre[j]? ≠ some (RelLetter.base y))
    (h : G) (n : ℕ) : WWord.IsWOne (blockWord lam pre h n) := by
  intro i x _ hx _
  exact getElem?_blockWord_ne_base lam hbase h n i x hx

/-- **(W2) at a subgroup prefix**: each letter of `pre` deep in its own factor,
and `h` deep in `H lam`. -/
theorem isWTwo_blockWord_of_deep (D : RelGenSet G Λ) (lam : Λ)
    {pre : List (RelLetter G Λ)} {C : ℕ}
    (hdeepPre : ∀ (j : ℕ) (mu : Λ) (g : G),
      pre[j]? = some (RelLetter.comp mu g) → g ∉ D.relBall mu C)
    {h : G} (hh : h ∉ D.relBall lam C) (n : ℕ) :
    WWord.IsWTwo D C (blockWord lam pre h n) := by
  intro i mu g hx
  have hi : i < (blockWord lam pre h n).length :=
    lt_length_of_getElem?_eq_some hx
  rw [length_blockWord] at hi
  obtain ⟨t, r, rfl, htn, hrm⟩ := exists_block_decomp pre.length hi
  rcases Nat.lt_or_ge r pre.length with hr | hr
  · rw [getElem?_blockWord_pre lam pre h htn hr] at hx
    exact hdeepPre r mu g hx
  · have hrm' : r = pre.length := by omega
    subst hrm'
    rw [getElem?_blockWord_comp lam pre h htn] at hx
    simp only [Option.some.injEq, RelLetter.comp.injEq] at hx
    rw [← hx.1, ← hx.2]
    exact hh

/-- **(W3) at a subgroup prefix**: consecutive indices differ inside `pre`, at
the seam to `h`, and at the wrap back to `pre`.  The separated case is vacuous,
the word having no `X`-letter to separate with. -/
theorem isWThree_blockWord_of_cyclic (D : RelGenSet G Λ) (lam : Λ)
    {pre : List (RelLetter G Λ)} (hne : pre ≠ [])
    (hbase : ∀ (j : ℕ) (y : G), pre[j]? ≠ some (RelLetter.base y))
    (hadj : ∀ (j : ℕ) (mu nu : Λ) (g₁ g₂ : G),
      pre[j]? = some (RelLetter.comp mu g₁) →
        pre[j + 1]? = some (RelLetter.comp nu g₂) → mu ≠ nu)
    (hseam : ∀ (j : ℕ) (mu : Λ) (g : G), j + 1 = pre.length →
      pre[j]? = some (RelLetter.comp mu g) → mu ≠ lam)
    (hwrap : ∀ (mu : Λ) (g : G),
      pre[0]? = some (RelLetter.comp mu g) → lam ≠ mu)
    (h : G) (n : ℕ) : WWord.IsWThree D (blockWord lam pre h n) := by
  constructor
  · intro i mu nu g₁ g₂ hx hy
    have hi1 : i + 1 < (blockWord lam pre h n).length :=
      lt_length_of_getElem?_eq_some hy
    rw [length_blockWord] at hi1
    obtain ⟨t, r, rfl, htn, hrm⟩ :=
      exists_block_decomp pre.length (show i < n * (pre.length + 1) by omega)
    rcases Nat.lt_or_ge r pre.length with hr | hr
    · rw [getElem?_blockWord_pre lam pre h htn hr] at hx
      rcases Nat.lt_or_ge (r + 1) pre.length with hr1 | hr1
      · have hidx : t * (pre.length + 1) + r + 1
            = t * (pre.length + 1) + (r + 1) := by omega
        rw [hidx, getElem?_blockWord_pre lam pre h htn hr1] at hy
        exact hadj r mu nu g₁ g₂ hx hy
      · have hr1' : r + 1 = pre.length := by omega
        have hidx : t * (pre.length + 1) + r + 1
            = t * (pre.length + 1) + pre.length := by omega
        rw [hidx, getElem?_blockWord_comp lam pre h htn] at hy
        simp only [Option.some.injEq, RelLetter.comp.injEq] at hy
        rw [← hy.1]
        exact hseam r mu g₁ hr1' hx
    · have hrm' : r = pre.length := by omega
      subst hrm'
      rw [getElem?_blockWord_comp lam pre h htn] at hx
      simp only [Option.some.injEq, RelLetter.comp.injEq] at hx
      have hm : 0 < pre.length := List.length_pos_of_ne_nil hne
      have htn1 : t + 1 < n := by
        by_contra hcon
        push Not at hcon
        have hmul : n * (pre.length + 1) ≤ (t + 1) * (pre.length + 1) :=
          Nat.mul_le_mul_right _ hcon
        have he : (t + 1) * (pre.length + 1)
            = t * (pre.length + 1) + pre.length + 1 := by ring
        omega
      have hidx : t * (pre.length + 1) + pre.length + 1
          = (t + 1) * (pre.length + 1) + 0 := by ring
      rw [hidx, getElem?_blockWord_pre lam pre h htn1 hm] at hy
      rw [← hx.1]
      exact hwrap nu g₂ hy
  · intro i _ _ _ _ y _ hy _
    exact absurd hy (getElem?_blockWord_ne_base lam hbase h n (i + 1) y)

end Bridge

end OsinComponents
end GGT
end GroupApproximation
