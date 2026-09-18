import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Pairing

/-!
# Variable indexing for the sentence `Φ(P,n,c)`

`non_mf_group_notes.tex`, `prop:mf-upper-bound`, printed sentence `9eae4d68673a`
("`Φ(P,n,c)` is a first-order sentence over the reals"), feeding
`thm:mf-arithmetic`.  The real variables of the sentence are the real and
imaginary parts of the matrix entries `U_g(r,s)` and of the coordinates of the
auxiliary vectors.  A variable is indexed by a tag and three coordinates plus a
part `p` (`0` for the real part, `1` for the imaginary part):

* tag `0`: `(g, r, s)`, the entry `(r,s)` of the `g`-th unitary;
* tag `1`: `(t, r, 0)`, coordinate `r` of the unit vector witnessing the lower
  bound for the `t`-th `S`-word;
* tag `2`: `(t, r, 0)`, coordinate `r` of the test vector of the upper bound for
  the `t`-th relator.

`encIdx` packs the index with `Nat.pair`; `encBlock` lists a rectangular block of
variables of one tag; `encDecode` reads a complex family back off an index.
-/

namespace GroupApproximation.Full.NN11b

/-- The index of the variable with tag `tag`, coordinates `(a, b, c)` and part `p`. -/
def encIdx (tag a b c p : ℕ) : ℕ := Nat.pair tag (Nat.pair a (Nat.pair b (Nat.pair c p)))

theorem encIdx_tag (tag a b c p : ℕ) : (Nat.unpair (encIdx tag a b c p)).1 = tag := by
  show (Nat.unpair (Nat.pair tag (Nat.pair a (Nat.pair b (Nat.pair c p))))).1 = tag
  rw [Nat.unpair_pair]

/-- The variables `encIdx tag a b c p` with `a < A`, `b < B`, `c < C`, `p < 2`. -/
def encBlock (tag A B C : ℕ) : List ℕ :=
  (List.range A).flatMap fun a => (List.range B).flatMap fun b =>
    (List.range C).flatMap fun c => (List.range 2).map fun p => encIdx tag a b c p

theorem encIdx_mem_encBlock {tag A B C a b c p : ℕ} (ha : a < A) (hb : b < B) (hc : c < C)
    (hp : p < 2) : encIdx tag a b c p ∈ encBlock tag A B C :=
  List.mem_flatMap.2 ⟨a, List.mem_range.2 ha, List.mem_flatMap.2 ⟨b, List.mem_range.2 hb,
    List.mem_flatMap.2 ⟨c, List.mem_range.2 hc, List.mem_map.2 ⟨p, List.mem_range.2 hp, rfl⟩⟩⟩⟩

theorem tag_of_mem_encBlock {tag A B C j : ℕ} (h : j ∈ encBlock tag A B C) :
    (Nat.unpair j).1 = tag := by
  obtain ⟨a, _, h1⟩ := List.mem_flatMap.1 h
  obtain ⟨b, _, h2⟩ := List.mem_flatMap.1 h1
  obtain ⟨c, _, h3⟩ := List.mem_flatMap.1 h2
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 h3
  exact encIdx_tag tag a b c p

theorem encIdx_not_mem_encBlock {tag tag' A B C a b c p : ℕ} (h : tag ≠ tag') :
    encIdx tag a b c p ∉ encBlock tag' A B C := fun hm =>
  h ((encIdx_tag tag a b c p).symm.trans (tag_of_mem_encBlock hm))

/-- The part `p` of a complex number: the real part for `p = 0`, the imaginary part
otherwise. -/
def encPart (p : ℕ) (z : ℂ) : ℝ := if p = 0 then z.re else z.im

theorem encPart_zero (z : ℂ) : encPart 0 z = z.re := if_pos rfl

theorem encPart_one (z : ℂ) : encPart 1 z = z.im := if_neg Nat.one_ne_zero

/-- The assignment reading the family `F tag a b c` off the variable indices. -/
def encDecode (F : ℕ → ℕ → ℕ → ℕ → ℂ) (j : ℕ) : ℝ :=
  encPart (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair j).2).2).2).2
    (F (Nat.unpair j).1 (Nat.unpair (Nat.unpair j).2).1
      (Nat.unpair (Nat.unpair (Nat.unpair j).2).2).1
      (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair j).2).2).2).1)

theorem encDecode_encIdx (F : ℕ → ℕ → ℕ → ℕ → ℂ) (tag a b c p : ℕ) :
    encDecode F (encIdx tag a b c p) = encPart p (F tag a b c) := by
  simp only [encDecode, encIdx, Nat.unpair_pair]

end GroupApproximation.Full.NN11b
