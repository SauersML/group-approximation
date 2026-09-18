import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauHopF2Cand
import GroupApproximation.Meta.AxiomGuard

/-!
# Hop family F2: the one-letter hop (lane bh-met-92n)

Family F2 with `x = a b c z₀ z'` and `y = [a']`, `a' ≠ a`.  With `u := [a, b, c]` the swap
`(R, S) = ([a'], u)` fixes `p` and `q` and carries `(x, y)` to `(x₁, u)`, `x₁ = a' z₀ z'`.
* `Easy ([a'], u; (x, y) → (x₁, u))` by the flexible square B with pair `([a, b'], u)`;
* `Easy (p, q; (x₁, u) → (x₁, u))` by the flexible square B with pair `([a', e], u)`,
  `e ≠ z₀`;
* `Easy ([a'], u; (x₁, u) → (x, y))` by the first square read from the other side.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **The one-letter hop.**  The level-`n` instance `(p, q; (a b c z₀ z', [a']) → itself)`
with `|p| = |q| = 3` incomparable with `[a']` and `[a, b, c]` has a `HopC` witness. -/
theorem higmanVCTauHop_hopC1 {d n : ℕ} {p q : List (Fin d)} {a b c a' b' z0 e : Fin d}
    {z' : List (Fin d)} (ha : a' ≠ a) (hb : b' ≠ b) (he : e ≠ z0)
    (hp3 : p.length = 3) (hq3 : q.length = 3)
    (hpy : higmanVCTauUnif_Inc p [a']) (hqy : higmanVCTauUnif_Inc q [a'])
    (hpu : higmanVCTauUnif_Inc p [a, b, c]) (hqu : higmanVCTauUnif_Inc q [a, b, c])
    (hn : z'.length + 5 = n) :
    higmanVCTauLevel_HopC d n p q (a :: b :: c :: z0 :: z') [a']
      (a :: b :: c :: z0 :: z') [a'] := by
  have hi : higmanVCTauUnif_Inc [a'] [a, b, c] := higmanVCTauUnif_inc_cons ha [] [b, c]
  have hj : higmanVCTauUnif_Inc [a, b'] [a, b, c] :=
    higmanVCTauClassify_inc_cons2 a (higmanVCTauUnif_inc_cons hb [] [c])
  have hk : higmanVCTauUnif_Inc [a', e] [a, b, c] := higmanVCTauUnif_inc_cons ha [e] [b, c]
  have L1 : (a :: b :: c :: z0 :: z').length = z'.length + 1 + 1 + 1 + 1 := rfl
  have L2 : ([a'] : List (Fin d)).length = 1 := rfl
  have L3 : (a' :: z0 :: z').length = z'.length + 1 + 1 := rfl
  have L4 : ([a, b, c] : List (Fin d)).length = 3 := rfl
  have L5 : (a :: b' :: z0 :: z').length = z'.length + 1 + 1 + 1 := rfl
  have L6 : ([a, b'] : List (Fin d)).length = 2 := rfl
  have L7 : ([a', e] : List (Fin d)).length = 2 := rfl
  -- the hop `([a'], u)`
  have sx : MapsCone (coneSwap [a'] [a, b, c] hi.1 hi.2) (a :: b :: c :: z0 :: z')
      (a' :: z0 :: z') := (mapsCone_coneSwap_right hi.1 hi.2).append (z0 :: z')
  have sy : MapsCone (coneSwap [a'] [a, b, c] hi.1 hi.2) [a'] [a, b, c] :=
    mapsCone_coneSwap_left hi.1 hi.2
  -- incomparabilities
  have ta : higmanVCTauUnif_Inc [a'] [a, b'] := higmanVCTauUnif_inc_cons ha [] [b']
  have tx : higmanVCTauUnif_Inc (a' :: z0 :: z') [a, b'] :=
    higmanVCTauUnif_inc_cons ha (z0 :: z') [b']
  have tx' : higmanVCTauUnif_Inc (a' :: z0 :: z') [a, b, c] :=
    higmanVCTauUnif_inc_cons ha (z0 :: z') [b, c]
  have tz : higmanVCTauUnif_Inc (a' :: z0 :: z') [a', e] :=
    higmanVCTauClassify_inc_cons2 a' (higmanVCTauUnif_inc_cons (Ne.symm he) z' [])
  have tp : higmanVCTauUnif_Inc p [a', e] :=
    higmanVCTauHop_incLen (by omega)
      (fun h => hpy.2 ((⟨[e], rfl⟩ : [a'] <+: [a', e]).trans h))
  have tq : higmanVCTauUnif_Inc q [a', e] :=
    higmanVCTauHop_incLen (by omega)
      (fun h => hqy.2 ((⟨[e], rfl⟩ : [a'] <+: [a', e]).trans h))
  -- the first flexible square: pair `([a, b'], u)`
  have hX1 : MapsCone (coneSwap [a, b'] [a, b, c] hj.1 hj.2) (a :: b :: c :: z0 :: z')
      (a :: b' :: z0 :: z') := (mapsCone_coneSwap_right hj.1 hj.2).append (z0 :: z')
  have hY1 : MapsCone (coneSwap [a, b'] [a, b, c] hj.1 hj.2) [a'] [a'] :=
    higmanVCTauUnif_fix hj.1 hj.2 ta hi
  have hQ1 : MapsCone (coneSwap [a, b'] [a, b, c] hj.1 hj.2) [a, b, c] [a, b'] :=
    mapsCone_coneSwap_right hj.1 hj.2
  have hD1 : MapsCone (coneSwap [a, b'] [a, b, c] hj.1 hj.2) (a' :: z0 :: z')
      (a' :: z0 :: z') := higmanVCTauUnif_fix hj.1 hj.2 tx tx'
  have FB1 : higmanVCTauComm_FlexB d [a'] [a, b, c] (a :: b :: c :: z0 :: z') [a']
      (a' :: z0 :: z') [a, b, c] :=
    higmanVCTauHop_flexB_mk hj.1 hj.2 (by omega) (by omega) hX1 hY1 (by omega) hY1 hQ1
      (by omega) (by omega) hD1 hQ1 (by omega)
  -- the second flexible square: pair `([a', e], u)`
  have hX2 : MapsCone (coneSwap [a', e] [a, b, c] hk.1 hk.2) (a' :: z0 :: z')
      (a' :: z0 :: z') := higmanVCTauUnif_fix hk.1 hk.2 tz tx'
  have hY2 : MapsCone (coneSwap [a', e] [a, b, c] hk.1 hk.2) [a, b, c] [a', e] :=
    mapsCone_coneSwap_right hk.1 hk.2
  have FB2 : higmanVCTauComm_FlexB d p q (a' :: z0 :: z') [a, b, c] (a' :: z0 :: z')
      [a, b, c] :=
    higmanVCTauHop_flexB_mk hk.1 hk.2 (by omega) (by omega) hX2 hY2 (by omega)
      (higmanVCTauUnif_fix hk.1 hk.2 tp hpu) (higmanVCTauUnif_fix hk.1 hk.2 tq hqu)
      hp3.le hq3.le hX2 hY2 (by omega)
  have le1 : (a :: b :: c :: z0 :: z').length + ([a'] : List (Fin d)).length ≤ n := by
    omega
  have le2 : (a' :: z0 :: z').length + ([a, b, c] : List (Fin d)).length ≤ n := by omega
  exact ⟨[a'], [a, b, c], p, q, a' :: z0 :: z', [a, b, c], a' :: z0 :: z', [a, b, c],
    hi.1, hi.2, by omega, by omega, higmanVCTauUnif_fix hi.1 hi.2 hpy hpu,
    higmanVCTauUnif_fix hi.1 hi.2 hqy hqu, hp3.le, hq3.le, sx, sy, sx, sy,
    ⟨le1, le2, Or.inr (Or.inr (Or.inr (Or.inl FB1)))⟩,
    ⟨le2, le2, Or.inr (Or.inr (Or.inr (Or.inl FB2)))⟩,
    ⟨le2, le1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr FB1))))⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_hopC1

end GroupApproximation.BooneHigman.Metabelian.Envelope
