---
rg: 2
id: mod-s2-quasirep-windings-vanish-on-fixed-window
kind: claim
title: Every quasi-representation of Mod(S_2) with defect below one on a fixed window has zero winding on every 2-cycle, so Voiculescu pairs and virtual windings never extend to Mod(S_2)
distinct_from:
  sp4-winding-ratio-sharp-constant-is-gromov-dual: that computes windings of Sp_4(Z) quasi-representations as determinant-cocycle pairings and shows they can be linear in the defect; this uses the same local-cocycle mechanism on Mod(S_2), where H_2 is torsion, to show every winding is exactly zero at defect below one.
  dadarlat-linear-groups-have-nonzero-h2-windings: that produces nonzero windings from non-torsion H_2 classes; this is the converse regime, a group whose H_2 is torsion, where windings vanish identically and uniformly in the dimension.
  mod-s2-is-point-norm-matricially-stable: that is the open stability claim; this proves that the degree-two winding obstruction, the only rational almost-flat obstruction available in degrees at most three, is inert on Mod(S_2) and on restrictions to all finite-index subgroups.
  sp4-quasirep-windings-budget-and-saturation: that bounds and saturates windings of Sp_4(Z) at the Maslov relator; this shows that after pulling back to Mod(S_2) no relator cycle carries any winding at all.
---

**ESTABLISHED** (route `mod-s2-quasirep-windings-vanish-on-fixed-window-proof`).

**Setting.** `M = Mod(S_2)`. For a unital map `pi : M -> U(d)` put `D(g,h) = pi(g) pi(h) pi(gh)^*`. The map has
*defect below `c` on* a finite set `W` of pairs if `||D(g,h) - I|| < c` for `(g,h)` in `W`. Put

```text
beta_pi(g,h) = (1/(2 pi i d)) Tr log D(g,h)      (principal branch; defined when -1 is not in spec D(g,h)).
```

For a finite integral 2-cycle `z = sum n_j [g_j | h_j]` of the bar complex of a group containing the `g_j, h_j`,
the *winding* of `pi` on `z` is `kappa_z(pi) = d <beta_pi, z> = (1/(2 pi i)) sum n_j Tr log D(g_j,h_j)`. It is an
integer (step 2 of the route).

**Theorem.**

1. **(W1) Windings vanish.** For every finite real 2-cycle `z` of `M` there is a finite set `W(z)` of pairs,
   containing the support of `z`, such that every unital `pi : M -> U(d)` with defect below `1` on `W(z)` has
   `<beta_pi, z> = 0`. The set `W(z)` does not depend on `d`.
2. **(W2) Commuting pairs.** Let `a, b` in `M` commute, for instance Dehn twists about disjoint curves. There is a
   finite `W_(a,b)` such that every unital `pi` with defect below `1` on `W_(a,b)` satisfies
   - `-1` is not in the spectrum of `[pi(a), pi(b)] = pi(a) pi(b) pi(a)^* pi(b)^*`;
   - `Tr log [pi(a), pi(b)] = 0`, so the Exel--Loring/Voiculescu winding of the pair `(pi(a), pi(b))` is zero.
3. **(W3) Virtual windings never extend.** Let `H <= M` be any subgroup (for example of finite index), let `z` be
   a finite integral 2-cycle of `H`, and let `F` be the finite set of elements `g, h, gh` over the pairs `[g|h]` of
   `z`. Let
   `phi : H -> U(d)` be unital with defect at most `1/2` on the support of `z` and `kappa_z(phi) != 0`. Then every
   unital `pi : M -> U(d)` with defect at most `1/2` on `W(z)` satisfies

   ```text
   max_{h in F} || pi(h) - phi(h) ||  >=  1/12 .
   ```

   The constant does not depend on `d`, on `H`, or on `z`.
4. **(W4) Induced models.** Let `H` be normal of finite index with left coset representatives
   `g_1 = e, g_2, ..., g_m`. For unital `phi : H -> U(d)`, let `Ind phi : M -> U(dm)` be the block matrix whose
   `(i,j)` block is `phi(g_i^-1 g g_j)` when that element is in `H`, and `0` otherwise. If `Ind phi` has defect below
   `1` on `W(z)`, then

   ```text
   sum_i kappa_(g_i^-1 z g_i)(phi) = 0 ,
   ```

   where `g^-1 z g` is the conjugated cycle.

   So inducing a virtual winding to `M` always cancels it.

**What this changes.**

- *For `mod-s2-is-point-norm-matricially-stable`.* That node lists "Voiculescu pairs on commuting twists" as the
  thing any proof must explain. (W2) explains the winding half: no model of `M` with defect below one on a
  fixed window carries a nonzero Voiculescu winding on any commuting pair. The node's suggested refutation test,
  a non-torsion class on a finite-index subgroup, is well posed: `M[2]/<iota> ~= PMod(S_(0,6))` has
  `b_2 = 26` (remark R1 of the route; not pinned). By (W3) and (W4) that test is dead: a quasi-representation of
  `H` whose instability is detected by a winding stays at distance at least `1/12` from every restriction of a
  `1/2`-model of `M`, and its induction to `M` has total winding zero.
- *Class kill (refutation side).* Every attempt to refute matricial stability of `M` by exhibiting a winding
  obstruction dies at the identity `<beta_pi, z> = <delta beta_pi, u>/N = 0`, where `N z = d u` in the bar complex
  of `M`. This covers windings on `M`, on commuting pairs, and on restrictions to, or inductions from, finite-index
  subgroups. Since the virtual cohomological dimension of `M` is 3, degree two is the only positive even rational
  degree (not pinned). So a refutation must use a torsion or non-cohomological invariant.
- *For the flagship `deligne-triple-cover-exact-mf-radical`.* Under the untwisting of
  `mod-s2-real-untwisting-identifies-deligne-norm-parameters`, the Maslov winding that drives
  `sp4-quasirep-windings-budget-and-saturation` becomes a coboundary on `M`. (W1) shows no winding survives on `M`.
  So on the Mod(S_2) side of the dictionary, no determinant or winding invariant of point-norm models can
  distinguish `t_s -> omega` from `t_s -> 1`. The flagship's `M`-side gate must be decided by the traceless part of
  the defects, which is the same place where `sp4-winding-ratio-sharp-constant-is-gromov-dual` located the
  obstruction on the `Sp_4(Z)` side.

DERIVATION
mod-s2-quasirep-windings-vanish-on-fixed-window-proof
