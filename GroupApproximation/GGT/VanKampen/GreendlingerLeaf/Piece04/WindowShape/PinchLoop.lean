import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94JunctionPocket
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shape: the planar pinch loop

Notation: `σ = sigma`, `α = alpha`, `φ = facePerm = σ ∘ α`, so `φ (α x) = σ x`.

Let `γ = g₀, …, g_l` be darts with `σ g_{i+1} = α g_i` (a backward chain), and let `d`, `t` be
darts with `σ g₀ = α d`, `φ d = t` and `σ t = α g_l`.  In a planar map with
`faceOf (α d) ≠ faceOf d` and `d ∉ γ`, no dart of `γ` lies on the face of `d`.

**Truth check.** Without `d ∉ γ` this is false: one vertex, one loop edge `{d, α d}`, `σ = α`,
`φ = id`, `γ = [d]`, `t = d`.  All three pinch equations hold, yet `faceOf g = faceOf d`.
The lane statement (`gl-p04-09`) carries `(d :: (γ ++ [t])).Nodup`; the proof only uses its
consequence `d ∉ γ`.

**Proof.** Put `a = α t`, `b = α d` and `m = l + 1 = γ.length`.
* The reversals of `γ` form a face chain run backwards: `φ (α g_{i+1}) = σ g_{i+1} = α g_i`.
  By induction on `γ` (`chain_facePerm_pow`): `φ^l (α g_l) = α g₀`, every `α g` with `g ∈ γ` is
  `φ^n (α g_l)` for some `n ≤ l`, and conversely every `φ^n (α g_l)` with `n ≤ l` is `α g` for
  some `g ∈ γ`.
* `φ a = σ t = α g_l`, so `φ^(n+1) a = φ^n (α g_l)` (`hshift`), and
  `φ^(m+1) a = φ (α g₀) = σ g₀ = α d = b`.
* `σ b = σ (α d) = φ d = t = α a`: the corner at the pinch vertex.
* Leastness: `φ^(s+1) a = α g` for some `g ∈ γ` when `s < m`; it is not `b = α d` because
  `d ∉ γ`.
* `faceOf (α b) = faceOf d ≠ faceOf (α d) = faceOf (φ^(m+1) a) = faceOf a`.
* Now `JunctionPocket.gap_alpha_faceOf_ne` (planar junction splitting, Euler characteristic)
  gives `faceOf (α (φ^(n+1) a)) ≠ faceOf (α b)` for `n < m`, that is
  `faceOf g ≠ faceOf d` for every `g ∈ γ`.

Hypotheses actually used: planarity, `d ∉ γ` (from the nodup hypothesis), the chain, the three
pinch equations, and `faceOf (α d) ≠ faceOf d`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.PinchLoop

open Equiv

universe v

/-- Along a backward chain `g :: l` (`σ b = α a` for consecutive `a, b`), the face permutation
walks the reversals from the last dart back to the first, and the first `l + 1` powers are
exactly the reversals of the chain. -/
theorem chain_facePerm_pow {M : CombMap.{v}} (l : List M.Dart) (g : M.Dart)
    (hchain : (g :: l).IsChain fun a b => M.sigma b = M.alpha a) :
    (M.facePerm ^ l.length) (M.alpha ((g :: l).getLast (List.cons_ne_nil g l))) = M.alpha g ∧
      (∀ x ∈ g :: l, ∃ n, n ≤ l.length ∧
        (M.facePerm ^ n) (M.alpha ((g :: l).getLast (List.cons_ne_nil g l))) = M.alpha x) ∧
      ∀ n, n ≤ l.length → ∃ x ∈ g :: l,
        (M.facePerm ^ n) (M.alpha ((g :: l).getLast (List.cons_ne_nil g l))) = M.alpha x := by
  induction l generalizing g with
  | nil =>
      refine ⟨?_, ?_, ?_⟩
      · rw [List.getLast_singleton, List.length_nil, pow_zero, Perm.one_apply]
      · intro x hx
        rw [List.mem_singleton] at hx
        subst hx
        refine ⟨0, Nat.zero_le _, ?_⟩
        rw [pow_zero, Perm.one_apply, List.getLast_singleton]
      · intro n hn
        obtain rfl : n = 0 := Nat.le_zero.mp hn
        refine ⟨g, List.mem_singleton_self g, ?_⟩
        rw [pow_zero, Perm.one_apply, List.getLast_singleton]
  | cons g' l' ih =>
      obtain ⟨hr, hchain'⟩ := List.isChain_cons_cons.mp hchain
      obtain ⟨hpow, hmem, hcover⟩ := ih g' hchain'
      have hL : (g :: g' :: l').getLast (List.cons_ne_nil g (g' :: l')) =
          (g' :: l').getLast (List.cons_ne_nil g' l') := rfl
      have hstep : M.facePerm (M.alpha g') = M.alpha g := by
        show M.sigma (M.alpha (M.alpha g')) = M.alpha g
        rw [M.alpha_involutive g']
        exact hr
      have hpow' : (M.facePerm ^ (l'.length + 1))
          (M.alpha ((g' :: l').getLast (List.cons_ne_nil g' l'))) = M.alpha g := by
        rw [pow_succ', Perm.mul_apply, hpow, hstep]
      rw [hL, List.length_cons]
      refine ⟨hpow', ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨l'.length + 1, le_refl _, hpow'⟩
        · obtain ⟨n, hn, hxe⟩ := hmem x hx'
          exact ⟨n, Nat.le_succ_of_le hn, hxe⟩
      · intro n hn
        rcases Nat.lt_or_ge n (l'.length + 1) with hlt | hge
        · obtain ⟨x, hx, hxe⟩ := hcover n (Nat.le_of_lt_succ hlt)
          exact ⟨x, List.mem_cons_of_mem g hx, hxe⟩
        · obtain rfl : n = l'.length + 1 := Nat.le_antisymm hn hge
          exact ⟨g, List.mem_cons_self, hpow'⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.PinchLoop.chain_facePerm_pow

/-- **Planar pinch loop.**  If a backward chain `γ` closes up at a pinch vertex through `d` and
`t = φ d` (`σ (head γ) = α d`, `σ t = α (last γ)`), the map is planar, `d` is off `γ` and the face
across `d` differs from the face of `d`, then no dart of `γ` lies on the face of `d`. -/
theorem faceOf_ne (M : CombMap.{v}) (hM : M.IsPlanar) (γ : List M.Dart) (d t : M.Dart)
    (hγ : γ ≠ []) (hnodup : (d :: (γ ++ [t])).Nodup)
    (hchain : γ.IsChain fun a b => M.sigma b = M.alpha a)
    (hhead : M.sigma (γ.head hγ) = M.alpha d) (hdt : M.facePerm d = t)
    (hlast : M.sigma t = M.alpha (γ.getLast hγ))
    (hface : M.faceOf (M.alpha d) ≠ M.faceOf d) :
    ∀ g ∈ γ, M.faceOf g ≠ M.faceOf d := by
  classical
  obtain ⟨g₀, l, rfl⟩ := List.exists_cons_of_ne_nil hγ
  obtain ⟨hpow, hmem, hcover⟩ := chain_facePerm_pow l g₀ hchain
  have hdnot : d ∉ g₀ :: l := fun hd =>
    (List.nodup_cons.mp hnodup).1 (List.mem_append_left [t] hd)
  have h1 : M.facePerm (M.alpha t) = M.alpha ((g₀ :: l).getLast (List.cons_ne_nil g₀ l)) := by
    show M.sigma (M.alpha (M.alpha t)) = M.alpha ((g₀ :: l).getLast (List.cons_ne_nil g₀ l))
    rw [M.alpha_involutive t]
    exact hlast
  have hshift : ∀ n : ℕ, (M.facePerm ^ (n + 1)) (M.alpha t) =
      (M.facePerm ^ n) (M.alpha ((g₀ :: l).getLast (List.cons_ne_nil g₀ l))) := by
    intro n
    rw [pow_succ, Perm.mul_apply, h1]
  have hb : M.sigma (M.alpha d) = M.alpha (M.alpha t) := by
    rw [M.alpha_involutive t]
    exact hdt
  have hab : (M.facePerm ^ (l.length + 1 + 1)) (M.alpha t) = M.alpha d := by
    rw [hshift, pow_succ', Perm.mul_apply, hpow]
    show M.sigma (M.alpha (M.alpha g₀)) = M.alpha d
    rw [M.alpha_involutive g₀]
    exact hhead
  have hleast : ∀ s < l.length + 1, (M.facePerm ^ (s + 1)) (M.alpha t) ≠ M.alpha d := by
    intro s hs h
    obtain ⟨x, hx, hxe⟩ := hcover s (Nat.le_of_lt_succ hs)
    rw [hshift, hxe] at h
    obtain rfl := M.alpha.injective h
    exact hdnot hx
  have hface' : M.faceOf (M.alpha (M.alpha d)) ≠ M.faceOf (M.alpha t) := by
    rw [M.alpha_involutive d,
      ← JunctionPocket.faceOf_pow_apply (M.alpha t) (l.length + 1 + 1), hab]
    exact hface.symm
  intro g hg
  obtain ⟨n, hn, hne⟩ := hmem g hg
  have key := JunctionPocket.gap_alpha_faceOf_ne hM (Nat.succ_ne_zero l.length) hb hab hleast
    hface' (t := n) (Nat.lt_succ_of_le hn)
  rw [hshift, hne, M.alpha_involutive g, M.alpha_involutive d] at key
  exact key

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.PinchLoop.faceOf_ne

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.PinchLoop
