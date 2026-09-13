---
rg: 2
id: radu-second-prime-frame-dynamics-admit-microstates
kind: claim
title: The arithmetic quotient of Radu's lattice, acting through its second place on compact quotients of PGL_2(Q_2), admits topological microstates
distinct_from:
  dyadic-homogeneous-quotient-admits-topological-microstates: that is PSL_2(Z[1/2]) acting on PSL_2(Q_2)/Lambda, with one inverted prime and modular vertex groups; this is the quaternionic lattice Q, a cocompact lattice in a product of two trees, acting through its second factor
  f2xf2-in-paunescu-class: that asks for soficity of every p.m.p. action of F2 x F2; this asks for one essentially free algebraic action of one lattice commensurable-up-to-measure-equivalence with it
---

**OPEN.** Let `Q` be the cocompact arithmetic lattice of `radu-horizontal-quotient-is-arithmetic-lattice`,
embedded in `L = PB^×(F_(𝔮')) ≅ PGL_2(Q_2)` by `ρ` at the second place. The claim: for every
torsion-free cocompact lattice `Λ ≤ L`, the action `Q ↷ L/Λ` by left translation admits `(F,ε)`-
microstates `(HV1)`, as defined in `homogeneous-quotient-soficity-gives-vertex-soficity`, for all
finite `F ∋ 1` and `ε > 0`.

**Stakes.**
* Through `radu-edge-coset-action-sofic-from-frame-dynamics-microstates` this makes the edge coset
  action `Q ↷ Q/C_χ` sofic.
* By `radu-bmw-lattice-sofic-via-slab-coset-actions` it then makes Radu's lattice sofic, and
  `G_2` too.
* So soficity of Radu's non-residually-finite lattice follows from microstates of one compact
  algebraic system of the residually finite lattice `Q`: 2-adic frames acted on by the second
  projection of `Q`.

**Structure.**
* *Freeness and ergodicity.* The action preserves Haar measure and is essentially free, because
  `ρ(Q)` has trivial centre in `L`. If `ρ(Q)` is dense in `L` the action is minimal and uniquely
  ergodic, and microstates are then equivalent to soficity of the p.m.p. action
  (`uniquely-ergodic-action-sofic-iff-topological-microstates`). Density is not checked here.
* *As an amalgam.* `Q = Fix_Q(p) *_(E') Stab_Q(e')` is the Bass–Serre amalgam of `Q ↷ T'`. The
  vertex group is a cocompact lattice on the first tree `T_h`. So on each `K_p`-orbit the action
  is an action of a virtually free lattice through its `𝔮'`-adic congruence quotients. These are the
  same three faces as in the dyadic case, with a vertex group that has the Haagerup property instead
  of `PSL_2(Z)`.

## Attempts

* **Păunescu's class.** Sufficient but much stronger: `radu-frame-dynamics-microstates-from-f2xf2-paunescu-class`.
* **Treeing.** Dead. `Q` is a cocompact lattice in a product of two trees with `χ(Q) = 1/24 > 0`,
  so `β_2^(2)(Q) = χ(Q) > 0`. An essentially free action of `Q` then has a non-treeable orbit relation
  (Gaboriau), so Elek–Lippner soficity of treeable relations does not apply. The same wall is recorded
  for the dyadic system in `sl2-homogeneous-action-is-not-treeable`.
* **Exact common-level cells.** Expected dead, as in the dyadic case. `Fix_Q(p)` permutes the level-`m`
  cells `K(𝔮'^m)\L/Λ` exactly, and so does the adjacent edge group. Gluing them exactly would give a
  genuine finite model of `Q ↷ Q/C_χ`, which `radu-square-lamp-forces-reflections-in-finite-actions`
  excludes. The approximate gluing needs an analogue of `expanding-matchings-need-a-shared-stabilizer`,
  which is not checked here.
* **Converse.** Not proved. In the dyadic case soficity of the vertex action is equivalent to these
  microstates (`dyadic-vertex-soficity-equals-frame-dynamics-soficity`), through a correction lemma
  for `Z/2 * Z/3`. The analogous correction for the virtually free `C_χ ≅ C_2^(*4)` is plausible but
  unwritten.
