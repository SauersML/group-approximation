import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenConj
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenWords
import GroupApproximation.Meta.AxiomGuard

/-!
# Shortening cone swaps by conjugation

`VGenSwapIn G v w` says that the cone swap of `v` and `w` lies in `G` (whenever `v` and `w` are
incomparable).  Three conjugation steps shorten a word of a cone swap by one letter.

* `vgen_shorten_left`: from `(p, u)` and `(u ++ [x], w)` to `(p ++ [x], w)`, when `u` is
  incomparable with `p` and `w` is incomparable with both;
* `vgen_shorten_right`: the mirror image, shortening the second word;
* `vgen_shorten_both`: from `(p, u)` and `(u ++ [x], u ++ [y])` to `(p ++ [x], p ++ [y])`.

In each case the conjugator is `coneSwap p u`, which carries `cone (u ++ c)` onto `cone (p ++ c)`
and fixes the cones incomparable with `p` and `u` (`vgen_conj_coneSwap`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {X : Type*}

/-- The cone swap of `v` and `w` lies in `G`. -/
def VGenSwapIn (G : Subgroup (Equiv.Perm (Cantor X))) (v w : List X) : Prop :=
  ∀ (h1 : ¬ v <+: w) (h2 : ¬ w <+: v), coneSwap v w h1 h2 ∈ G

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.VGenSwapIn

/-- Shorten the first word of a cone swap. -/
theorem vgen_shorten_left {G : Subgroup (Equiv.Perm (Cantor X))} {p u w : List X} (x : X)
    (hpu : ¬ p <+: u) (hup : ¬ u <+: p) (hpw : ¬ p <+: w) (hwp : ¬ w <+: p)
    (huw : ¬ u <+: w) (hwu : ¬ w <+: u) (h1 : VGenSwapIn G p u)
    (h2 : VGenSwapIn G (u ++ [x]) w) : VGenSwapIn G (p ++ [x]) w := by
  intro hvw hwv
  have hm1 : MapsCone (coneSwap p u hpu hup) (u ++ [x]) (p ++ [x]) :=
    (mapsCone_coneSwap_right hpu hup).append [x]
  have hm2 : MapsCone (coneSwap p u hpu hup) w w :=
    vgen_mapsCone_coneSwap_fix hpu hup hwp hpw hwu huw
  rw [← vgen_conj_coneSwap hvw hwv (vgen_not_prefix_append_left [x] huw)
    (vgen_not_prefix_append_right [x] huw hwu) hm1 hm2]
  exact G.mul_mem (G.mul_mem (h1 hpu hup) (h2 _ _)) (G.inv_mem (h1 hpu hup))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vgen_shorten_left

/-- Shorten the second word of a cone swap. -/
theorem vgen_shorten_right {G : Subgroup (Equiv.Perm (Cantor X))} {p u v : List X} (x : X)
    (hpu : ¬ p <+: u) (hup : ¬ u <+: p) (hpv : ¬ p <+: v) (hvp : ¬ v <+: p)
    (huv : ¬ u <+: v) (hvu : ¬ v <+: u) (h1 : VGenSwapIn G p u)
    (h2 : VGenSwapIn G v (u ++ [x])) : VGenSwapIn G v (p ++ [x]) := by
  intro hvw hwv
  have hm1 : MapsCone (coneSwap p u hpu hup) (u ++ [x]) (p ++ [x]) :=
    (mapsCone_coneSwap_right hpu hup).append [x]
  have hm2 : MapsCone (coneSwap p u hpu hup) v v :=
    vgen_mapsCone_coneSwap_fix hpu hup hvp hpv hvu huv
  rw [← vgen_conj_coneSwap hvw hwv (vgen_not_prefix_append_right [x] huv hvu)
    (vgen_not_prefix_append_left [x] huv) hm2 hm1]
  exact G.mul_mem (G.mul_mem (h1 hpu hup) (h2 _ _)) (G.inv_mem (h1 hpu hup))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vgen_shorten_right

/-- Shorten both words of a cone swap with a common parent. -/
theorem vgen_shorten_both {G : Subgroup (Equiv.Perm (Cantor X))} {p u : List X} (x y : X)
    (hpu : ¬ p <+: u) (hup : ¬ u <+: p) (h1 : VGenSwapIn G p u)
    (h2 : VGenSwapIn G (u ++ [x]) (u ++ [y])) : VGenSwapIn G (p ++ [x]) (p ++ [y]) := by
  intro hvw hwv
  have hm1 : MapsCone (coneSwap p u hpu hup) (u ++ [x]) (p ++ [x]) :=
    (mapsCone_coneSwap_right hpu hup).append [x]
  have hm2 : MapsCone (coneSwap p u hpu hup) (u ++ [y]) (p ++ [y]) :=
    (mapsCone_coneSwap_right hpu hup).append [y]
  rw [← vgen_conj_coneSwap hvw hwv (vgen_not_prefix_append_swap hvw)
    (vgen_not_prefix_append_swap hwv) hm1 hm2]
  exact G.mul_mem (G.mul_mem (h1 hpu hup) (h2 _ _)) (G.inv_mem (h1 hpu hup))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vgen_shorten_both

end GroupApproximation.BooneHigman.Metabelian.Envelope
