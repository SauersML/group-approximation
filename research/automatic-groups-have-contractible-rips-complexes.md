---
rg: 2
id: automatic-groups-have-contractible-rips-complexes
kind: claim
title: Every automatic group has a contractible Vietoris–Rips complex for some finite generating set and scale
distinct_from:
  amenable-automatic-groups-have-contractible-rips-complexes: that is the affirmative answer to Zaremsky Problem 4.1, for amenable automatic groups only; this drops amenability and asks it of every automatic group, so it implies that claim
  torsion-free-automatic-groups-have-finite-cd: that asks only for finite cohomological dimension of torsion-free automatic groups; this asks for an actual contractible Rips complex, which implies it for torsion-free groups
  thompson-f-has-no-contractible-rips-complex: that is the established fact that no Rips complex of F is contractible; this is an open universal statement about automatic groups
---

**OPEN.** If `G` is automatic, there are a finite generating set `S` and a scale
`d` such that the Vietoris–Rips complex `P_d(G, S)` is contractible.

This is Zaremsky Problem 4.1 ("If a group is amenable and automatic, does it have
a contractible Rips complex?") without the amenability hypothesis. It implies
`amenable-automatic-groups-have-contractible-rips-complexes` (route
`amenable-automatic-rips-from-all-automatic-groups`) and
`torsion-free-automatic-groups-have-finite-cd` (route
`torsion-free-automatic-finite-cd-via-rips`).

## Attempts

- **Rips's argument for hyperbolic groups.** Push a finite subcomplex toward a
  basepoint using thin triangles, staying inside `P_d` once `d` is large compared
  to the hyperbolicity constant. For an automatic group the combing lines
  `K`-fellow travel, so the push stays only inside `P_(Kd)`. That proves coarse
  contractibility, which gives type `F_∞`. Dies at the change of scale. A
  structure whose fellow travelling constant for endpoints at distance `<= d` is
  itself `<= d` (additive rather than multiplicative control) would be enough.
  Finding which automatic groups carry one is open.
- **Known cases.** Hyperbolic groups (Rips; `hyperbolic-rips-complex-models-proper-actions`)
  and `Z^n` with standard generators (`rips-complexes-of-integer-lattices-are-contractible`,
  Virk). Both are automatic.
- **Consequence to keep in view.** With `thompson-f-has-no-contractible-rips-complex`
  and `contractible-rips-complex-gives-finite-classifying-space`, this claim implies
  that `F` is not automatic. It is at least as hard as the negative answer to
  Zaremsky Problem 2.2.
- 2026-09-17 (swarm-0917-w4-z-rips): **decomposition into two independent
  necessary conditions.** By `contractible-rips-conjugates-p-subgroups-into-balls`
  (Smith fixed point theorem applied to an invariant simplex), a contractible
  `P_d(G,S)` with `N = |B_S(d)|` forces:
  - dimension: `cd H <= N - 1` for every torsion-free `H <= G`, which is
    `torsion-free-automatic-groups-have-finite-cd`;
  - torsion: every finite `p`-subgroup is conjugate into `B_S(d)`, which is
    `automatic-groups-conjugate-finite-p-subgroups-into-a-ball` (route
    `automatic-p-subgroup-ball-via-rips`).
  So a refutation needs no infinite-dimensional group. An automatic group with
  finite 2-subgroups of unbounded order would already refute this claim. The
  biautomatic centring argument (Gersten–Short, from memory) does not transfer,
  because a left-acting finite subgroup is not controlled by an automatic structure.
  Still open.
- 2026-09-17 (swarm-0917-w4-z-rips): **weak automaticity is not enough.**
  `weak-automaticity-does-not-give-contractible-rips-complexes` is established.
  `F` is autostackable, of type `F_∞` and quadratic, and `T` is asynchronously
  combable, yet neither has a contractible Rips complex. For `T` the proof uses
  both invariants above: `F <= T`, and `Z/2^k <= T` for every `k`. So a proof built
  on stacking flows, prefix rewriting, finiteness properties, isoperimetry or an
  asynchronous combing is refuted. Any proof must use the synchronous fellow
  traveller property at the fixed-scale step, which is where the Rips attempt above
  dies.
- 2026-09-17 (swarm-0917-w5-z-rips): **the torsion half is not independent; the
  finite-extension torsion counterexamples are dead.** This is established as
  `automatic-finite-vcd-groups-have-few-p-subgroup-classes`, using Brown's
  Lemma IX.13.2, imported as `brown-finite-p-subgroup-classes-from-finite-mod-p-cohomology`.
  An automatic group with a torsion-free finite-index subgroup of finite cd has finitely many
  conjugacy classes of `p`-subgroups, all conjugate into one ball. The proof takes the normal
  core `H`. `H` is `FP_∞`, so each `H^n(H;F_p)` is finite. Finite cd makes the total finite, and
  Brown's lemma gives the count. Route `automatic-p-subgroup-ball-via-brown` then derives the
  torsion condition from `automatic-groups-are-virtually-torsion-free` (new, OPEN, containing the
  hyperbolic VTF root) together with the dimension condition.
  **Obstruction to a class of approaches.** Take any refutation of this claim through the torsion
  condition: an automatic `G` with infinitely many conjugacy classes of `p`-subgroups.
  - The invariant is the total mod-p cohomology `⊕_n H^n(H;F_p)` of a finite-index torsion-free
    normal subgroup `H`.
  - Every candidate of the form "torsion-free `FP_∞` group of finite cd, extended by a finite
    group" dies at the step "infinitely many `p`-classes", because that invariant is finite. This
    covers the Leary–Nucinkis `H_L ⋊ Q` groups and Morse-kernel groups with a finite symmetry.
  - The surviving torsion candidates are non-VTF automatic groups. Such a group would already
    answer `automatic-groups-are-virtually-torsion-free` negatively. `T` has the same shape (infinite simple,
    hence not VTF, with `Z/2^k ≤ T` for all `k`), but it is not known to be automatic.
  - Every other torsion candidate already fails the dimension condition.
  **Calibration.** `FP_∞` cannot be weakened to `F_n`. Leary–Nucinkis, Example 8, verbatim: "this
  gives rise to a group ~H = HL ⋊ Cp which is of type Fn and contains infinitely many conjugacy
  classes of elements of order p". Also, Brown's lemma cannot be extended from `p`-groups to all
  finite groups (Leary, G&T 2005). So contractible Rips complexes, like Smith theory, constrain
  only prime-power torsion. Still open.
