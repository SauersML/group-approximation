import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionVanishExt

/-!
# The rank-defect obstruction: `K₀` of the matrix trace kernel is not divisible

Lane `TWWSchafhauser-3d2`, work order `WO-TWWSchafhauser-3d-2(b)`.
Manuscript: `non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378). That
theorem cites Tikuisis--White--Winter, Ann. of Math. 185 (2017), Theorem A, through
C. Schafhauser, J. reine angew. Math. 759 (2020), §4--5.

## The route text this corrects

The route file `FK/orders/TWWSchafhauser3d.md` has two lines at issue:

* l.17 (WO-3d-1) takes the pullback of
  "0→J_ω→∏_ω M_k→∏^ω M_k→0 along θ";
* l.26--28 (WO-3d-2(b)) asks for a separable `D ⊆ ∏_ω M_k` with
  "J_D := D ∩ J, preserving K_1(J_D)=0 and K_0(J_D) torsion-free divisible (Schafhauser §4)".

For the **matrix** coefficients `∏_ω M_k` this is false, and no separable reduction can fix it.

Let `e = (e_k)` be the class of a rank-one projection in each `M_k`. It lies in `J_ω`, because
`tr_k(e_k) = 1/k → 0`. Pointwise rank gives a homomorphism
`d : K₀(J_ω) →+ (ℕ → ℤ) ⧸ {ω-null}` with `d [e] = 1` (work order (viii), sent to main).
Here `1` is not `2`-divisible. A preimage `f` of `[e]/2` would satisfy `2 f(k) = 1` for
`ω`-almost every `k`, which no integer does.

The same `d` restricted to `K₀(J_D)` for any `D ∋ e` shows that the separable version fails too.
Schafhauser's actual coefficients are `∏_ω Q` for the universal UHF algebra `Q`, where
`K₀(Q) = ℚ` and ranks are rational. The route was amended accordingly (WO-3d2-Q1/Q2/Q3).

## Contents

* `nullSubgroup l`: the integer sequences vanishing `l`-eventually;
* `RankDefectGroup l := (ℕ → ℤ) ⧸ nullSubgroup l`, and `rankOne l`, the class of the constant `1`;
* `not_exists_two_zsmul_eq_rankOne`: `rankOne l` is not `2`-divisible when `l ≠ ⊥`;
* `not_isDivisibleGroup_of_addMonoidHom`: a group that maps some element to a
  non-`2`-divisible element is not divisible;
* `not_isDivisibleGroup_of_rankDefect`: any `K` with `d : K →+ RankDefectGroup l` and
  `d e = rankOne l` is not divisible. This is the counterexample theorem; `K = K₀(J_ω)` is the
  instance from l.26--28 of the route;
* `not_isDivisibleGroup_rankDefectGroup`: the rank-defect group itself is not divisible.
-/

namespace GroupApproximation.Full.TWWSchafhauser

noncomputable section

/-- Integer sequences that vanish `l`-eventually. -/
def nullSubgroup (l : Filter ℕ) : AddSubgroup (ℕ → ℤ) where
  carrier := {f | ∀ᶠ n in l, f n = 0}
  zero_mem' := show ∀ᶠ n in l, (0 : ℕ → ℤ) n = 0 from Filter.Eventually.of_forall fun _ => rfl
  add_mem' {f g} hf hg := show ∀ᶠ n in l, (f + g) n = 0 from
    (Filter.Eventually.and (show ∀ᶠ n in l, f n = 0 from hf)
      (show ∀ᶠ n in l, g n = 0 from hg)).mono fun n h =>
        show f n + g n = 0 by rw [h.1, h.2, add_zero]
  neg_mem' {f} hf := show ∀ᶠ n in l, (-f) n = 0 from
    (show ∀ᶠ n in l, f n = 0 from hf).mono fun n h => show -f n = 0 by rw [h, neg_zero]

theorem mem_nullSubgroup {l : Filter ℕ} {f : ℕ → ℤ} :
    f ∈ nullSubgroup l ↔ ∀ᶠ n in l, f n = 0 :=
  Iff.rfl

/-- The **rank-defect group** `∏_l ℤ`: integer sequences modulo `l`-null sequences. Pointwise
rank maps `K₀` of the matrix trace kernel `J_ω ⊆ ∏_ω M_k` into it. -/
abbrev RankDefectGroup (l : Filter ℕ) : Type := (ℕ → ℤ) ⧸ nullSubgroup l

/-- The class of the constant sequence `1`, i.e. the rank of a rank-one projection. -/
def rankOne (l : Filter ℕ) : RankDefectGroup l :=
  QuotientAddGroup.mk (fun _ => (1 : ℤ))

/-- `rankOne l` has no half: no sequence `f` has `2 f(n) = 1` on an `l`-large set. -/
theorem not_exists_two_zsmul_eq_rankOne (l : Filter ℕ) [l.NeBot] :
    ¬ ∃ b : RankDefectGroup l, (2 : ℤ) • b = rankOne l := by
  rintro ⟨b, hb⟩
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective b
  have hb' : (QuotientAddGroup.mk ((2 : ℤ) • f) : RankDefectGroup l) =
      QuotientAddGroup.mk (fun _ => (1 : ℤ)) := hb
  have h : -((2 : ℤ) • f) + (fun _ => (1 : ℤ)) ∈ nullSubgroup l := QuotientAddGroup.eq.mp hb'
  obtain ⟨n, hn⟩ := Filter.Eventually.exists
    (show ∀ᶠ n in l, (-((2 : ℤ) • f) + fun _ => (1 : ℤ)) n = 0 from h)
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at hn
  omega

/-- If some element of `K` maps under a homomorphism to a non-`2`-divisible element, then `K` is
not divisible. -/
theorem not_isDivisibleGroup_of_addMonoidHom {K G : Type*} [AddCommGroup K] [AddCommGroup G]
    (d : K →+ G) {x : K} (hx : ¬ ∃ b : G, (2 : ℤ) • b = d x) : ¬ IsDivisibleGroup K := by
  intro hK
  obtain ⟨b, hb⟩ := hK 2 two_ne_zero x
  exact hx ⟨d b, by rw [← hb, map_zsmul]⟩

/-- **Counterexample to route l.26--28 (`FK/orders/TWWSchafhauser3d.md`, WO-3d-2(b)).**
If a group `K` has a rank-defect homomorphism `d : K →+ ∏_l ℤ` sending some class `e` to the
rank `1`, then `K` is not divisible. The case `K = K₀(J_ω)` with `J_ω ⊆ ∏_ω M_k` and `e` a
rank-one projection refutes "K_0(J_D) torsion-free divisible" for matrix coefficients.
The same holds for every `K₀(J_D)` with `e ∈ D`. -/
theorem not_isDivisibleGroup_of_rankDefect {K : Type*} [AddCommGroup K] (l : Filter ℕ)
    [l.NeBot] (d : K →+ RankDefectGroup l) {e : K} (he : d e = rankOne l) :
    ¬ IsDivisibleGroup K :=
  not_isDivisibleGroup_of_addMonoidHom d (x := e) (by
    rw [he]
    exact not_exists_two_zsmul_eq_rankOne l)

/-- The rank-defect group `∏_l ℤ` is not divisible for `l ≠ ⊥`. -/
theorem not_isDivisibleGroup_rankDefectGroup (l : Filter ℕ) [l.NeBot] :
    ¬ IsDivisibleGroup (RankDefectGroup l) :=
  not_isDivisibleGroup_of_rankDefect l (AddMonoidHom.id _) (e := rankOne l) rfl

/-- The ultrafilter case, i.e. the norm ultraproduct index from route l.17. -/
theorem not_isDivisibleGroup_of_rankDefect_ultrafilter {K : Type*} [AddCommGroup K]
    (ω : Ultrafilter ℕ) (d : K →+ RankDefectGroup (ω : Filter ℕ)) {e : K}
    (he : d e = rankOne (ω : Filter ℕ)) : ¬ IsDivisibleGroup K :=
  not_isDivisibleGroup_of_rankDefect (ω : Filter ℕ) d he

end

end GroupApproximation.Full.TWWSchafhauser
