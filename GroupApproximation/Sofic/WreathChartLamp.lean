import GroupApproximation.Algebra.PermutationalWreath
import GroupApproximation.Sofic.SoficAction

/-!
# Lamps transported along an orbit chart

Section 29.6 of the dossier reads a lamp configuration through the charts of a
sofic action model: at a good model point `s` the chart `π_s` embeds the tested
window `E ⊆ X` into the finite set `B`, and the lamp is transported to a
configuration in `K^B`, trivial off the image of the window.

Two facts about this transport carry the wreath argument.

* `chartLamp_congr` — **equation (29.3)**.  If two charts are related by the
  model identity `π_s(x) = π_r(h⁻¹ x)` and the lamp's support together with its
  `h`-translate lies in the window, the transported translate at `s` equals the
  transported lamp at `r`.  Injectivity of the charts on the window is what
  turns a statement about support coordinates into an identity at *every*
  coordinate of `B`.
* `chartLamp_ne` — lamps differing inside the window stay different after
  transport, which is the separation input of the wreath model.
-/

namespace GroupApproximation

namespace WreathChart

universe u v w

variable {K : Type u} [Group K] {X : Type v} {B : Type v}

open scoped Classical in
/-- The lamp configuration read through a chart: at a chart value coming from
the window, the lamp's value at the (unique) window preimage; trivial
elsewhere. -/
noncomputable def chartLamp (E : Finset X) (π : X → B) (f : Lamp K X) : B → K :=
  fun b => if h : ∃ x ∈ E, π x = b then f.toFun h.choose else 1

theorem chartLamp_mul (E : Finset X) (π : X → B) (f g : Lamp K X) :
    chartLamp E π (f * g) = chartLamp E π f * chartLamp E π g := by
  funext b
  by_cases h : ∃ x ∈ E, π x = b
  · simp only [chartLamp, dif_pos h, Pi.mul_apply, Lamp.mul_apply]
  · simp only [chartLamp, dif_neg h, Pi.mul_apply, one_mul]

@[simp] theorem chartLamp_one (E : Finset X) (π : X → B) :
    chartLamp E π (1 : Lamp K X) = 1 := by
  funext b
  by_cases h : ∃ x ∈ E, π x = b
  · simp only [chartLamp, dif_pos h, Lamp.one_apply, Pi.one_apply]
  · simp only [chartLamp, dif_neg h, Pi.one_apply]

/-- Reading the transported lamp at a chart value of a window point returns the
original value, provided the chart is injective on the window. -/
theorem chartLamp_apply_chart {E : Finset X} {π : X → B} (hinj : Set.InjOn π E)
    (f : Lamp K X) {x : X} (hx : x ∈ E) :
    chartLamp E π f (π x) = f.toFun x := by
  have hex : ∃ y ∈ E, π y = π x := ⟨x, hx, rfl⟩
  rw [chartLamp, dif_pos hex]
  obtain ⟨hmem, hval⟩ := hex.choose_spec
  rw [hinj hmem hx hval]

/-- A nontrivial transported coordinate comes from a nontrivial window
coordinate. -/
theorem exists_of_chartLamp_ne_one {E : Finset X} {π : X → B} {f : Lamp K X}
    {b : B} (hb : chartLamp E π f b ≠ 1) :
    ∃ x ∈ E, π x = b ∧ f.toFun x ≠ 1 := by
  by_cases h : ∃ x ∈ E, π x = b
  · obtain ⟨hmem, hval⟩ := h.choose_spec
    refine ⟨h.choose, hmem, hval, ?_⟩
    rw [chartLamp, dif_pos h] at hb
    exact hb
  · rw [chartLamp, dif_neg h] at hb
    exact absurd rfl hb

variable {G : Type w} [Group G] [MulAction G X]

/-- **Equation (29.3).**  Transporting the translated lamp at the moved base
point is the same as transporting the lamp at the original base point. -/
theorem chartLamp_congr {E : Finset X} {πs πr : X → B} {h : G} {f : Lamp K X}
    (hinjs : Set.InjOn πs E) (hinjr : Set.InjOn πr E)
    (hsupp : ∀ x : X, f.toFun x ≠ 1 → x ∈ E ∧ h • x ∈ E)
    (hchart : ∀ x ∈ E, h⁻¹ • x ∈ E → πs x = πr (h⁻¹ • x)) :
    chartLamp E πs (lampAut h f) = chartLamp (K := K) E πr f := by
  funext b
  by_cases hL : chartLamp E πs (lampAut h f) b = 1
  · by_cases hR : chartLamp (K := K) E πr f b = 1
    · rw [hL, hR]
    · -- a nontrivial value at `r` forces one at `s`
      obtain ⟨y, hyE, hyb, hyne⟩ := exists_of_chartLamp_ne_one hR
      obtain ⟨-, hhy⟩ := hsupp y hyne
      have hback : h⁻¹ • (h • y) = y := inv_smul_smul h y
      have hcs : πs (h • y) = b := by
        rw [hchart (h • y) hhy (by rw [hback]; exact hyE), hback, hyb]
      have hval : chartLamp E πs (lampAut h f) b = f.toFun y := by
        rw [← hcs, chartLamp_apply_chart hinjs _ hhy, lampAut_apply, hback]
      rw [hval] at hL
      exact absurd hL hyne
  · obtain ⟨x, hxE, hxb, hxne⟩ := exists_of_chartLamp_ne_one hL
    rw [lampAut_apply] at hxne
    obtain ⟨hmem, hsmul⟩ := hsupp (h⁻¹ • x) hxne
    have hxback : h • (h⁻¹ • x) = x := smul_inv_smul h x
    have hcr : πr (h⁻¹ • x) = b := by
      rw [← hchart x hxE hmem, hxb]
    have hLval : chartLamp E πs (lampAut h f) b = f.toFun (h⁻¹ • x) := by
      rw [← hxb, chartLamp_apply_chart hinjs _ hxE, lampAut_apply]
    have hRval : chartLamp (K := K) E πr f b = f.toFun (h⁻¹ • x) := by
      rw [← hcr, chartLamp_apply_chart hinjr _ hmem]
    rw [hLval, hRval]

/-- Lamps that differ inside the window differ after transport. -/
theorem chartLamp_ne {E : Finset X} {π : X → B} (hinj : Set.InjOn π E)
    {f g : Lamp K X} {x : X} (hx : x ∈ E) (hne : f.toFun x ≠ g.toFun x) :
    chartLamp E π f ≠ chartLamp E π g := by
  intro hcon
  apply hne
  rw [← chartLamp_apply_chart hinj f hx, ← chartLamp_apply_chart hinj g hx,
    hcon]

end WreathChart

end GroupApproximation
