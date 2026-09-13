---
rg: 2
id: dyadic-homogeneous-quotient-admits-topological-microstates
kind: claim
title: The dense dyadic action on compact quotients of PSL2(Q2) admits topological microstates
distinct_from:
  sl2-homogeneous-quotient-crossed-product-is-connes-embeddable: that asks for possibly non-Cartan matrix microstates of the crossed product; this asks for permutation microstates of the action itself, which would give Cartan ones and, through the covering label, soficity of the vertex action.
  sl3z-cocompact-quotient-admits-no-topological-microstates: that is the real-place system of the Kazhdan lattice SL3(Z), where return labels live in a rigid lattice; this is the dense 2-adic system, where the return labels live in a free group.
  dyadic-bruhat-tits-vertex-action-is-sofic: that is the countable set-action statement; this is a stronger-looking compact uniquely ergodic statement which implies it through homogeneous-quotient-soficity-gives-vertex-soficity.
---

**OPEN (two-sided).** Let `L = PSL_2(Q_2)` and `A = PSL_2(Z[1/2])`. For every torsion-free
cocompact lattice `Λ <= L`, every finite `F ⊆ A` containing `1`, and every `ε > 0`, there are a
finite set `V` and maps `σ : F → Sym(V)`, `y : V → L/Λ` satisfying `(HV1)` of
`homogeneous-quotient-soficity-gives-vertex-soficity`.

**Equivalent forms.**
* `A` is dense in `L`, so `A ↷ L/Λ` is minimal and uniquely ergodic (checks in
  `homogeneous-quotient-soficity-gives-vertex-soficity-proof`). By
  `uniquely-ergodic-action-sofic-iff-topological-microstates`, the claim for `Λ` is equivalent to
  soficity of the essentially free p.m.p. action `A ↷ (L/Λ, Haar)`. Equidistribution of any
  microstate family is automatic.
* The action is an amalgam of two profinite actions over a profinite action. `PSL_2(Z)` acts on each
  `K`-orbit (a copy of `K = SL_2(Z_2)`) through its `2`-adic congruence quotients. The adjacent
  vertex group acts through the adjacent maximal compact, and the index-three Iwahori edge group acts
  on the edge pieces.

**Stakes.** True ⇒ `dyadic-bruhat-tits-vertex-action-is-sofic` (route
`dyadic-vertex-action-sofic-from-homogeneous-microstates`) ⇒ the centralizer HNN `G_2` is sofic
(`sofic-dyadic-coset-action-makes-hnn-sofic`), killing family D at `n = 2`. False for some `Λ` ⇒
nothing yet about the vertex action, because the converse of the covering-label theorem is open.

## Attempts

- **Exact common-level cells.** `PSL_2(Z)` permutes the level-`m` cells
  `K(2^m)\L/Λ` exactly, and the adjacent vertex group permutes its own cells exactly. Gluing along
  an exact level is excluded by `homogeneous-k-orbit-factor-has-no-finite-a-refinement`, and for
  spheres by `dyadic-radial-shell-couplings-have-one-third-boundary`. Microstates tolerate a scale
  `m` much coarser than the cell level `M`, so this only kills `M = m`.
- **Treeing.** Elek--Lippner soficity of treeable relations is dead:
  `sl2-homogeneous-action-is-not-treeable` (`β_2^(2)(A) > 0`).
- **Weak containment in a known sofic action of `A`.** Soficity passes down weak containment, so a
  sofic action weakly containing `A ↷ L/Λ` would suffice. Two natural candidates are dead.
  *Odd-level profinite actions*: the `K`-orbit indicator `1_P` (measure `1/r`) is `C`-invariant
  and moved off itself by `d`. A weakly containing profinite action would carry almost `C`-invariant
  sets of measure `1/r`. Selberg `(τ)` on odd congruence quotients makes such a set close to
  `C`-invariant, hence to `A`-invariant by co-density, hence almost `d`-invariant. Contradiction.
  *Bernoulli shifts*: `L^2_0` of a Bernoulli shift restricted to `PSL_2(Z)` is a multiple of the
  regular representation, which has no almost invariant vectors, while `1_P − 1/r` is invariant.
  Any candidate must be non-tempered along `C` and non-congruence.
- **Return labels (structure, both signs).** Lift marks to the compact fundamental domain
  `Ω = ⊔_b K g_b`. Below a fixed scale each good edge `v → σ(s)v` carries a unique `λ(v,s) ∈ Λ`
  with `g_(σ(s)v) ∈ U s g_v λ(v,s)`, and products around good relator cycles are exactly `1`, as in
  the real-place SL3 lane. Here `Λ` is a **free group**, so there is no holonomy superrigidity to
  exploit for a negative proof. Honest finite actions stay excluded: on a finite-index `A' <= A`
  the holonomy would be a homomorphism `A' → Λ`, trivial by the Margulis normal subgroup theorem.
  Then `A'` would fix marks up to scale, contradicting density. So a construction must use
  defective holonomy on a vanishing fraction of vertices.
