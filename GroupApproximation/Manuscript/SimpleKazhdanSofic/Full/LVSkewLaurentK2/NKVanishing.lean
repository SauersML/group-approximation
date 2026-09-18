import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.NKAugmentation
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.DirectedUnion

/-!
# Twisted nil-`K₂`: formal reductions (lane LVNKVanishing)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii; work orders
WO-LVSkewLaurentK2-3b-1/2.  Ara–Brustenga–Cortiñas (*K-theory of Leavitt path algebras*, Münster
J. Math. 2 (2009), `thm:skewyao`, Steps 1-2, `yaoseq6.tex` l.574-640) split
`K₂(S[t^ε;φ^ε]) = K₂(S) ⊕ NK₂(S,φ)_ε`. The second summand vanishes for regular supercoherent `S`
(`yaoseq6.tex` l.1169ff). That is a Quillen–Waldhausen input: already for the trivial action on
`S = 𝔽₂` it is `K₂(𝔽₂[t]) = K₂(𝔽₂)`.

This file proves the formal parts:

* `nilK2Trivial_of_stableK2Trivial`: stable `K₂ = 0` of the half ring kills the nil part;
* `nilK2Trivial_of_halfK2Statement`, `halfK2Statement_iff_nilK2Trivial`: given stable
  `K₂(S) = 0`, `HalfK2Statement S` is *equivalent* to `NilK2Trivial S (±1)`.  So
  `nilK2Trivial_of_ultramatricial` is exactly as hard as `halfK2Statement_of_ultramatricial`;
* `comapSubtypeEquiv`: a subring `T ≤ H`, pulled back to `H`, is isomorphic to `T`;
* `stableK2Trivial_skewHalf_of_subrings`: if every finite subset of `S[t^ε;φ^ε]` lies in a subring
  `T ≤ S[t^ε;φ^ε]` with stable `K₂(T) = 0`, then the half ring has stable `K₂ = 0`;
* `halfK2Statement_of_subrings`: the same for both halves.

The last two are the route for the manuscript's ring. There `S = φ̂⁻¹C₀` is the ABC Step 3
colimit (`yaoseq6.tex` l.640-688), with `C₀` the degree-zero part of `C₂(𝔽₂)` and
`φ(a) = x₀ a y₀`. The pieces `A_k = φ̂⁻ᵏ(C₀)` satisfy `φ̂(A_k) ⊆ A_k`, so `A_k[t;φ̂]` is a subring
of `S[t;φ̂]`, isomorphic to `C_{≥0} = span{x_μ y_ν : |μ| ≥ |ν|} ⊆ C₂(𝔽₂)`. That ring is the union of
the triangular pieces `F_n = 𝔽₂⟨x₀,x₁⟩ · C_{0,n}`. By contrast, no nonzero finite-dimensional
subalgebra of `S` is `φ̂`-stable (`φ̂_* = 1/2` on `K₀`), so no filtration by matricial `φ̂`-stable
pieces exists.
-/

namespace GroupApproximation.Full.LVSkewLaurentK2

section Formal

variable {S : Type*} [Ring S] [MulSemiringAction (Multiplicative ℤ) S]

/-- Stable `K₂(S[t^ε;φ^ε]) = 0` implies vanishing of twisted nil-`K₂`: the augmentation
hypothesis is not even needed.  (`yaoseq6.tex` `thm:skewyao`, Step 1;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem nilK2Trivial_of_stableK2Trivial (ε : ℤ) (hε : ε ≠ 0)
    (h : LVH2GL3.StableK2Trivial (skewHalf S ε)) : NilK2Trivial S ε hε := by
  intro n k hk _
  exact h n k hk

/-- `HalfK2Statement S` implies twisted nil-`K₂ = 0` for both signs.
(`yaoseq6.tex` `thm:skewyao`, Step 1; `simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem nilK2Trivial_of_halfK2Statement (h : HalfK2Statement S) :
    NilK2Trivial S 1 one_ne_zero ∧ NilK2Trivial S (-1) (by decide) := by
  have h' : LVH2GL3.StableK2Trivial (skewHalf S 1) ∧
      LVH2GL3.StableK2Trivial (skewHalf S (-1)) := h
  exact ⟨nilK2Trivial_of_stableK2Trivial 1 one_ne_zero h'.1,
    nilK2Trivial_of_stableK2Trivial (-1) (by decide) h'.2⟩

/-- **The nil part is the whole difficulty.**  Given stable `K₂(S) = 0`, stable `K₂ = 0` of both
half rings is equivalent to vanishing of twisted nil-`K₂` for both signs.
(`yaoseq6.tex` `thm:skewyao`, Steps 1-2; `simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem halfK2Statement_iff_nilK2Trivial (hK2 : LVH2GL3.StableK2Trivial S) :
    HalfK2Statement S ↔
      NilK2Trivial S 1 one_ne_zero ∧ NilK2Trivial S (-1) (by decide) :=
  ⟨nilK2Trivial_of_halfK2Statement,
    fun h => halfK2Statement_of_nilK2Trivial S hK2 h.1 h.2⟩

end Formal

section Subrings

/-- A subring `T ≤ H` of `R`, pulled back along `H ↪ R`, is isomorphic to `T`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def comapSubtypeEquiv {R : Type*} [Ring R] (H T : Subring R) (hTH : T ≤ H) :
    T.comap H.subtype ≃+* T where
  toFun x := ⟨x.1.1, Subring.mem_comap.mp x.2⟩
  invFun y := ⟨⟨y.1, hTH y.2⟩, Subring.mem_comap.mpr y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

variable {S : Type*} [Ring S] [MulSemiringAction (Multiplicative ℤ) S]

/-- **Filtrations of a half ring.**  If every finite subset of `S[t^ε;φ^ε]` lies in a subring
`T ≤ S[t^ε;φ^ε]` with stable `K₂(T) = 0`, then `S[t^ε;φ^ε]` has stable `K₂ = 0` (continuity of
`K₂` under directed unions).  For the manuscript's ring the pieces are the triangular algebras
`F_n = 𝔽₂⟨x₀,x₁⟩ · C_{0,n}` inside `A_k[t;φ̂] ≅ C_{≥0}`.  (Ara–Brustenga–Cortiñas 2009, proof of
Thm 3.6 and `thm:skewyao`, `yaoseq6.tex` l.574-688; `simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem stableK2Trivial_skewHalf_of_subrings (ε : ℤ)
    (h : ∀ s : Finset (SkewLaurent S), (s : Set (SkewLaurent S)) ⊆ (skewHalf S ε : Set _) →
      ∃ T : Subring (SkewLaurent S), T ≤ skewHalf S ε ∧
        (s : Set (SkewLaurent S)) ⊆ (T : Set (SkewLaurent S)) ∧ LVH2GL3.StableK2Trivial T) :
    LVH2GL3.StableK2Trivial (skewHalf S ε) := by
  refine LVCohnK2.stableK2Trivial_of_subrings fun s => ?_
  obtain ⟨T, hTH, hsT, hT⟩ := h (s.map (Function.Embedding.subtype _)) (by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
    exact y.2)
  refine ⟨T.comap (skewHalf S ε).subtype, ?_,
    LVCohnK2.stableK2Trivial_of_ringEquiv (comapSubtypeEquiv _ T hTH).symm hT⟩
  intro y hy
  rw [SetLike.mem_coe, Subring.mem_comap]
  exact SetLike.mem_coe.mp
    (hsT (Finset.mem_coe.mpr (Finset.mem_map_of_mem _ (Finset.mem_coe.mp hy))))

/-- `HalfK2Statement S` from filtrations of both half rings by subrings with stable `K₂ = 0`.
(Ara–Brustenga–Cortiñas 2009, `thm:skewyao`, `yaoseq6.tex` l.574-688;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem halfK2Statement_of_subrings
    (h : ∀ ε : ℤ, (ε = 1 ∨ ε = -1) →
      ∀ s : Finset (SkewLaurent S), (s : Set (SkewLaurent S)) ⊆ (skewHalf S ε : Set _) →
        ∃ T : Subring (SkewLaurent S), T ≤ skewHalf S ε ∧
          (s : Set (SkewLaurent S)) ⊆ (T : Set (SkewLaurent S)) ∧ LVH2GL3.StableK2Trivial T) :
    HalfK2Statement S := by
  show LVH2GL3.StableK2Trivial (skewHalf S 1) ∧ LVH2GL3.StableK2Trivial (skewHalf S (-1))
  exact ⟨stableK2Trivial_skewHalf_of_subrings 1 (h 1 (Or.inl rfl)),
    stableK2Trivial_skewHalf_of_subrings (-1) (h (-1) (Or.inr rfl))⟩

end Subrings

end GroupApproximation.Full.LVSkewLaurentK2
