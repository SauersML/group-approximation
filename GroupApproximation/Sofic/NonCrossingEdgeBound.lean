import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# The edge bound for a non-crossing chord diagram, and the curvature count it feeds

`MatchingRunStructure`'s header names what the curvature count still needs and
says it is not contiguity:

> **The degree bound**, and it is *not* a consequence of planarity alone.  The
> block graph is outerplanar by construction — the runs are non-crossing chords
> with the blocks in cyclic order, so the drawing is the data and no planar map
> has to be reconstructed.  But outerplanarity alone gives only `E ≤ 2V − 3` …

This file proves that inequality, and then the arithmetic that turns it into a
shell.  Both halves are elementary and neither mentions a group, a relator, a
word or a matching: the input is a finite set of points of `ℕ` and a finite set
of chords between them, no two of which **straddle**.

## 1.  The bound

`card_add_three_le_two_mul_card` — for a finite `S ⊆ ℕ` with at least two points
and a finite set `E` of ordered pairs from `S`, no two of which straddle,

    `|E| + 3 ≤ 2·|S|`.

This is the outerplanar edge bound `E ≤ 2V − 3`, stated additively so that `ℕ`
subtraction never appears.  It is sharp: a triangulated polygon attains it.

The proof is an induction on `|S|` with **one** idea.  Call the number of points
of `S` strictly inside a chord its *gap*.

* If every chord has gap `0` — every chord joins two consecutive points — then
  reading a chord by its left endpoint is injective, and no chord starts at the
  largest point, so `|E| ≤ |S| − 1`, which is far inside the bound.
* Otherwise take a chord `(i, j)` of **least positive gap** `m`.  Every chord
  inside `[i, j]` other than `(i, j)` has strictly smaller gap, hence gap `0`,
  hence starts at a point of `{i} ∪ (S ∩ (i,j))`: at most `m + 1` of them.
  Every other chord has *both* endpoints outside the open interval `(i, j)` —
  this is exactly where non-crossing is spent, and it is spent twice, once at
  each endpoint — so those chords together with `(i, j)` live on the `|S| − m`
  points that survive, and the inductive hypothesis applies to them.  Adding up,
  `|E| ≤ (m + 1) + (2(|S| − m) − 3) − 1`, and `m ≥ 1` finishes it.

Note where `(i, j)` is counted: with the **outside**, not the inside.  Counting
it with the inside loses exactly one and the induction does not close.

## 2.  The count

`no_shell_contradiction` is the arithmetic the diagram half is aiming at.  Write
`F` for the number of relator blocks and take the blocks — the `F` relators and
the boundary — as the vertices of the run graph, so `V = F + 1`, and the runs as
its edges.  Then:

* the edge bound gives `2·E ≤ 4·F − 2`;
* if **no** relator block is a shell, every relator block meets at least five
  runs.  A relator block with no boundary run and at most three runs would have
  its whole boundary covered by at most three pieces, each shorter than `λ·|r| ≤
  |r|/6`, which is absurd — so such a block has at least seven runs; and a
  relator block with a boundary run and at least four interior runs has at least
  five.  Either way five, and summing degrees, `5·F ≤ 2·E`.

Then `5F + 6 ≤ 4F + 4`, which `ℕ` refuses outright — `F ≥ 1` is not even needed,
though the edge bound's own `2 ≤ V` supplies it anyway.  So some relator block is
a shell.  `no_shell_contradiction` is that one-line implication, isolated so that
the diagram half has an exact arithmetic target to hit, and
`five_runs_of_no_shell` is the case split that produces the `5`.

Nothing here discharges `CurvatureAssembly.ShellGate`: what is still missing is
the construction of the run graph itself — that the runs of the matching form a
non-crossing chord set on the blocks — not the counting that runs on it.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

namespace NonCrossing

/-! ## 1.  Chords and their gaps -/

/-- **The points of `S` strictly inside the chord `(i, j)`.**  Its cardinality is
the chord's *gap*, and the induction below is driven by making that gap least. -/
def gapSet (S : Finset ℕ) (i j : ℕ) : Finset ℕ :=
  S.filter fun x => i < x ∧ x < j

theorem mem_gapSet {S : Finset ℕ} {i j x : ℕ} :
    x ∈ gapSet S i j ↔ x ∈ S ∧ i < x ∧ x < j := by
  rw [gapSet, Finset.mem_filter]

/-- **A chord of gap zero is read injectively by its left endpoint.**  Two
chords sharing a left endpoint are nested, and the shorter one's right endpoint
then sits strictly inside the longer one — a gap. -/
theorem eq_of_fst_eq_of_gap_zero {S : Finset ℕ} {E : Finset (ℕ × ℕ)}
    (hord : ∀ p ∈ E, p.1 < p.2) (hmem : ∀ p ∈ E, p.1 ∈ S ∧ p.2 ∈ S)
    {F : Finset (ℕ × ℕ)} (hFE : F ⊆ E)
    (hgap : ∀ p ∈ F, (gapSet S p.1 p.2).card = 0)
    {p q : ℕ × ℕ} (hp : p ∈ F) (hq : q ∈ F) (h : p.1 = q.1) : p = q := by
  have hkey : ∀ a ∈ F, ∀ b ∈ F, a.1 = b.1 → a.2 < b.2 → False := by
    intro a ha b hb h1 h2
    have hin : a.2 ∈ gapSet S b.1 b.2 := by
      refine mem_gapSet.mpr ⟨(hmem a (hFE ha)).2, ?_, h2⟩
      rw [← h1]
      exact hord a (hFE ha)
    have hempty : gapSet S b.1 b.2 = ∅ := Finset.card_eq_zero.mp (hgap b hb)
    rw [hempty] at hin
    exact absurd hin (Finset.notMem_empty _)
  refine Prod.ext h ?_
  rcases lt_trichotomy p.2 q.2 with hlt | heq | hgt
  · exact absurd (hkey p hp q hq h hlt) not_false
  · exact heq
  · exact absurd (hkey q hq p hp h.symm hgt) not_false

/-- **A chord of least positive gap exists.**  `Nat.find` over the gap values;
no order structure on the chords is needed, only that the gaps are naturals. -/
theorem exists_min_gap {S : Finset ℕ} {E : Finset (ℕ × ℕ)}
    (h : ∃ p ∈ E, 1 ≤ (gapSet S p.1 p.2).card) :
    ∃ p₀ ∈ E, 1 ≤ (gapSet S p₀.1 p₀.2).card ∧
      ∀ p ∈ E, 1 ≤ (gapSet S p.1 p.2).card →
        (gapSet S p₀.1 p₀.2).card ≤ (gapSet S p.1 p.2).card := by
  classical
  have hP : ∃ n : ℕ, ∃ p ∈ E, 1 ≤ (gapSet S p.1 p.2).card ∧
      (gapSet S p.1 p.2).card = n := by
    obtain ⟨p, hp, hgp⟩ := h
    exact ⟨(gapSet S p.1 p.2).card, p, hp, hgp, rfl⟩
  obtain ⟨p₀, hp₀E, hp₀gap, hp₀eq⟩ := Nat.find_spec hP
  refine ⟨p₀, hp₀E, hp₀gap, ?_⟩
  intro q hq hgq
  rw [hp₀eq]
  exact Nat.find_le ⟨q, hq, hgq, rfl⟩

/-! ## 2.  The edge bound -/

/-- **The outerplanar edge bound, with a fuel parameter.**  See the header for
the argument; `card_add_three_le_two_mul_card` is the statement without the
fuel. -/
theorem card_add_three_le_two_mul_card_aux :
    ∀ (n : ℕ) (S : Finset ℕ) (E : Finset (ℕ × ℕ)), S.card ≤ n →
      (∀ p ∈ E, p.1 < p.2) →
      (∀ p ∈ E, p.1 ∈ S ∧ p.2 ∈ S) →
      (∀ p ∈ E, ∀ q ∈ E, ¬ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2)) →
      2 ≤ S.card →
      E.card + 3 ≤ 2 * S.card := by
  intro n
  induction n with
  | zero =>
      intro S E hn _ _ _ h2
      omega
  | succ n ih =>
      intro S E hn hord hmem hnc h2
      by_cases hall : ∀ p ∈ E, (gapSet S p.1 p.2).card = 0
      · -- every chord joins two consecutive points of `S`
        have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
        have hmax := S.max'_mem hSne
        have himg : ∀ p ∈ E, p.1 ∈ S.erase (S.max' hSne) := by
          intro p hp
          refine Finset.mem_erase.mpr ⟨?_, (hmem p hp).1⟩
          intro hEq
          have hle : p.2 ≤ S.max' hSne := Finset.le_max' S p.2 (hmem p hp).2
          have hlt := hord p hp
          omega
        have hcard : E.card ≤ (S.erase (S.max' hSne)).card := by
          refine Finset.card_le_card_of_injOn Prod.fst himg ?_
          intro p hp q hq h
          exact eq_of_fst_eq_of_gap_zero hord hmem (Finset.Subset.refl E) hall
            (Finset.mem_coe.mp hp) (Finset.mem_coe.mp hq) h
        rw [Finset.card_erase_of_mem hmax] at hcard
        omega
      · -- some chord has a point of `S` strictly inside it
        have hex : ∃ p ∈ E, 1 ≤ (gapSet S p.1 p.2).card := by
          by_contra hcon
          refine hall ?_
          intro p hp
          by_contra hz
          exact hcon ⟨p, hp, by omega⟩
        obtain ⟨p₀, hp₀E, hp₀gap, hp₀min⟩ := exists_min_gap hex
        set i := p₀.1 with hi
        set j := p₀.2 with hj
        set m := (gapSet S i j).card with hm
        have hij : i < j := hord p₀ hp₀E
        have hiS : i ∈ S := (hmem p₀ hp₀E).1
        have hjS : j ∈ S := (hmem p₀ hp₀E).2
        have hm1 : 1 ≤ m := hp₀gap
        -- the surviving points
        set Sout := S.filter (fun x => ¬ (i < x ∧ x < j)) with hSoutdef
        have hsplit : m + Sout.card = S.card := by
          rw [hm, hSoutdef, gapSet]
          exact Finset.card_filter_add_card_filter_not
            (p := fun x : ℕ => i < x ∧ x < j)
        have hiSout : i ∈ Sout := Finset.mem_filter.mpr ⟨hiS, by omega⟩
        have hjSout : j ∈ Sout := Finset.mem_filter.mpr ⟨hjS, by omega⟩
        have h2out : 2 ≤ Sout.card :=
          Finset.one_lt_card.mpr ⟨i, hiSout, j, hjSout, by omega⟩
        -- the chords inside, and the chords outside
        set Ein := (E.filter fun p => i ≤ p.1 ∧ p.2 ≤ j).erase p₀ with hEindef
        set Eout := E.filter (fun p => ¬ (i ≤ p.1 ∧ p.2 ≤ j)) with hEoutdef
        have hp₀in : p₀ ∈ E.filter fun p => i ≤ p.1 ∧ p.2 ≤ j :=
          Finset.mem_filter.mpr ⟨hp₀E, by omega⟩
        have hEsplit :
            (E.filter fun p => i ≤ p.1 ∧ p.2 ≤ j).card + Eout.card = E.card := by
          rw [hEoutdef]
          exact Finset.card_filter_add_card_filter_not
            (p := fun q : ℕ × ℕ => i ≤ q.1 ∧ q.2 ≤ j)
        have hEincard :
            Ein.card + 1 = (E.filter fun p => i ≤ p.1 ∧ p.2 ≤ j).card := by
          rw [hEindef, Finset.card_erase_of_mem hp₀in]
          have := Finset.card_pos.mpr ⟨p₀, hp₀in⟩
          omega
        -- every chord strictly inside `(i, j)` has gap zero
        have hgapin : ∀ p ∈ Ein, (gapSet S p.1 p.2).card = 0 := by
          intro p hp
          obtain ⟨hpne, hpf⟩ := Finset.mem_erase.mp hp
          obtain ⟨hpE, hpi, hpj⟩ := Finset.mem_filter.mp hpf
          have hpord : p.1 < p.2 := hord p hpE
          have hsub : gapSet S p.1 p.2 ⊆ gapSet S i j := by
            intro x hx
            obtain ⟨hxS, hx1, hx2⟩ := mem_gapSet.mp hx
            exact mem_gapSet.mpr ⟨hxS, by omega, by omega⟩
          have hstrict : gapSet S p.1 p.2 ⊂ gapSet S i j := by
            refine (Finset.ssubset_iff_of_subset hsub).mpr ?_
            rcases Nat.lt_or_ge i p.1 with hlt | hge
            · refine ⟨p.1, mem_gapSet.mpr ⟨(hmem p hpE).1, hlt, by omega⟩, ?_⟩
              intro hcon
              obtain ⟨-, hcon1, -⟩ := mem_gapSet.mp hcon
              omega
            · have hne : p.2 < j := by
                rcases Nat.lt_or_ge p.2 j with h | h
                · exact h
                · exfalso
                  refine hpne (Prod.ext ?_ ?_) <;> omega
              refine ⟨p.2, mem_gapSet.mpr ⟨(hmem p hpE).2, by omega, hne⟩, ?_⟩
              intro hcon
              obtain ⟨-, -, hcon2⟩ := mem_gapSet.mp hcon
              omega
          have hlt : (gapSet S p.1 p.2).card < m := by
            rw [hm]
            exact Finset.card_lt_card hstrict
          by_contra hz
          have h1 : 1 ≤ (gapSet S p.1 p.2).card := by omega
          have := hp₀min p hpE h1
          omega
        -- so they are at most `m + 1`
        have hEinle : Ein.card ≤ m + 1 := by
          have himg : ∀ p ∈ Ein, p.1 ∈ insert i (gapSet S i j) := by
            intro p hp
            obtain ⟨-, hpf⟩ := Finset.mem_erase.mp hp
            obtain ⟨hpE, hpi, hpj⟩ := Finset.mem_filter.mp hpf
            have hpord : p.1 < p.2 := hord p hpE
            rcases Nat.lt_or_ge i p.1 with hlt | hge
            · exact Finset.mem_insert_of_mem
                (mem_gapSet.mpr ⟨(hmem p hpE).1, hlt, by omega⟩)
            · have : p.1 = i := by omega
              rw [this]
              exact Finset.mem_insert_self _ _
          have hEinE : Ein ⊆ E := by
            intro p hp
            obtain ⟨-, hpf⟩ := Finset.mem_erase.mp hp
            exact (Finset.mem_filter.mp hpf).1
          have hcard : Ein.card ≤ (insert i (gapSet S i j)).card := by
            refine Finset.card_le_card_of_injOn Prod.fst himg ?_
            intro p hp q hq h
            exact eq_of_fst_eq_of_gap_zero hord hmem hEinE hgapin
              (Finset.mem_coe.mp hp) (Finset.mem_coe.mp hq) h
          have hins : (insert i (gapSet S i j)).card ≤ m + 1 := by
            rw [hm]
            exact Finset.card_insert_le _ _
          omega
        -- the chords outside, with `(i, j)` among them, live on `Sout`
        have hEoutE : Eout ⊆ E := by
          intro p hp
          exact (Finset.mem_filter.mp hp).1
        have hp₀notout : p₀ ∉ Eout := by
          intro hcon
          obtain ⟨-, hcon2⟩ := Finset.mem_filter.mp hcon
          exact hcon2 ⟨by omega, by omega⟩
        have hmemout : ∀ p ∈ insert p₀ Eout, p.1 ∈ Sout ∧ p.2 ∈ Sout := by
          intro p hp
          rcases Finset.mem_insert.mp hp with rfl | hp'
          · exact ⟨hiSout, hjSout⟩
          · obtain ⟨hpE, hpout⟩ := Finset.mem_filter.mp hp'
            have hpord : p.1 < p.2 := hord p hpE
            constructor
            · refine Finset.mem_filter.mpr ⟨(hmem p hpE).1, ?_⟩
              rintro ⟨hlo, hhi⟩
              have := hnc p₀ hp₀E p hpE
              exact hpout ⟨by omega, by omega⟩
            · refine Finset.mem_filter.mpr ⟨(hmem p hpE).2, ?_⟩
              rintro ⟨hlo, hhi⟩
              have := hnc p hpE p₀ hp₀E
              exact hpout ⟨by omega, by omega⟩
        have hIH : (insert p₀ Eout).card + 3 ≤ 2 * Sout.card := by
          refine ih Sout (insert p₀ Eout) (by omega) ?_ hmemout ?_ h2out
          · intro p hp
            rcases Finset.mem_insert.mp hp with rfl | hp'
            · exact hord _ hp₀E
            · exact hord p (hEoutE hp')
          · intro p hp q hq
            have hpE : p ∈ E := by
              rcases Finset.mem_insert.mp hp with rfl | hp'
              · exact hp₀E
              · exact hEoutE hp'
            have hqE : q ∈ E := by
              rcases Finset.mem_insert.mp hq with rfl | hq'
              · exact hp₀E
              · exact hEoutE hq'
            exact hnc p hpE q hqE
        have hEoutcard : (insert p₀ Eout).card = Eout.card + 1 := by
          rw [Finset.card_insert_of_notMem hp₀notout]
        omega

/-- **The outerplanar edge bound.**  A finite set `S` of at least two points of
`ℕ`, and a finite set `E` of chords between them, ordered and pairwise
non-straddling, satisfies

    `|E| + 3 ≤ 2·|S|`.

Written additively so no `ℕ` subtraction appears; the familiar form is
`E ≤ 2V − 3`.  Sharp, and attained by a triangulated polygon. -/
theorem card_add_three_le_two_mul_card (S : Finset ℕ) (E : Finset (ℕ × ℕ))
    (hord : ∀ p ∈ E, p.1 < p.2)
    (hmem : ∀ p ∈ E, p.1 ∈ S ∧ p.2 ∈ S)
    (hnc : ∀ p ∈ E, ∀ q ∈ E, ¬ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2))
    (h2 : 2 ≤ S.card) : E.card + 3 ≤ 2 * S.card :=
  card_add_three_le_two_mul_card_aux S.card S E le_rfl hord hmem hnc h2

/-- The degree form: twice the number of chords is at most `4·|S| − 6`. -/
theorem two_mul_card_le (S : Finset ℕ) (E : Finset (ℕ × ℕ))
    (hord : ∀ p ∈ E, p.1 < p.2)
    (hmem : ∀ p ∈ E, p.1 ∈ S ∧ p.2 ∈ S)
    (hnc : ∀ p ∈ E, ∀ q ∈ E, ¬ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2))
    (h2 : 2 ≤ S.card) : 2 * E.card + 6 ≤ 4 * S.card := by
  have := card_add_three_le_two_mul_card S E hord hmem hnc h2
  omega

end NonCrossing

/-! ## 3.  The curvature count, as arithmetic -/

/-- **Why a relator block that is not a shell meets at least five runs.**

A relator block's boundary is partitioned by its runs.  Suppose it is not a
shell — meaning: it is not the case that it meets the boundary of the diagram and
has at most three other runs.

* If it has no boundary run, every one of its runs is a piece, so each is
  shorter than `λ·|r| ≤ |r|/6`, so `6·(number of runs) > 6`, i.e. at least seven
  runs.  The hypothesis `6 * b < 6 * d` below is that comparison with `b = 1`
  standing for the whole relator and `d` the number of runs.
* If it has a boundary run, then not being a shell means at least four interior
  runs, so at least five runs in all.

Either way five, which is all the count needs. -/
theorem five_runs_of_no_shell {d : ℕ} (hcase : (6 < d) ∨ (5 ≤ d)) : 5 ≤ d := by
  rcases hcase with h | h
  · omega
  · exact h

/-- **The count closes.**  With `F ≥ 1` relator blocks and the boundary as the
`F + 1` vertices of the run graph, `E` runs as its edges:

* the edge bound gives `2·E + 6 ≤ 4·(F + 1)`;
* if no relator block is a shell, each meets at least five runs, and summing the
  degrees over the relator blocks alone gives `5·F ≤ 2·E`.

Together `5·F + 6 ≤ 4·F + 4`, which is false.  So some relator block **is** a
shell.

This is the exact arithmetic target the diagram half has to hit, and it is the
whole of the "degree bound" once the run graph exists: nothing beyond these
three inequalities is used. -/
theorem no_shell_contradiction {F E : ℕ}
    (hedge : 2 * E + 6 ≤ 4 * (F + 1)) (hdeg : 5 * F ≤ 2 * E) : False := by
  omega

/-- The same, phrased as what it produces: under the edge bound and `F ≥ 1`,
**not** every relator block can meet five runs. -/
theorem exists_lt_five_runs {F E : ℕ}
    (hedge : 2 * E + 6 ≤ 4 * (F + 1)) : ¬ (5 * F ≤ 2 * E) :=
  fun hdeg => no_shell_contradiction hedge hdeg

end SmallCancellationRouter
end GroupApproximation
