---
rg: 2
id: piecewise-representative-lifts-are-rigid-under-cheap-moves
kind: claim
title: Piecewise-representative lifts of Out(F_n) are commensurability invariant, glue along graphs of groups exactly when edge restrictions are conjugate by the boundary full group, and are not made easier by profinite blow-ups, which make any lift free but only exist when a finite-index lift does
distinct_from:
  boundary-pushout-of-aut-out-free-splits-mod-every-quotient: that shows every quotient-level obstruction to (PR) vanishes and constrains point stabilizers; this shows three cheap constructive moves (induction, profinite blow-up, splitting) change nothing, so a solution must be a genuine dynamical splitting on an expansive model.
  out-free-acts-on-boundary-by-piecewise-representatives: that is the open statement (PR); this records which reformulations of it are equivalent and which constructions reduce to it.
---

**ESTABLISHED** (lane proof, bh-outfn-2, 2026-09-18; elementary; not reviewed).

**Notation.** As in `out-free-extension-pushed-into-the-boundary-full-group`:
- `M = [[F_n ⋉ ∂F_n]]`, `H = M·Aut(F_n)`, and `q̂M` is the coset of `q ∈ Out(F_n)`.
- A **profinite Γ-space** is an inverse limit `Z = lim Z_k` of finite Γ-sets, for example `Γ̂`. For a finite or profinite Γ-space `Z`, a **(PR) action over `Z`**
  is an action `h` of `Γ` on `∂F_n × Z` such that `h_q` maps each fiber `∂F_n × {z}` to the
  fiber over `qz` by an element `h_{q,z} ∈ q̂M`, locally constant in `z`.
- Plain (PR) is the case `Z = pt`.

## Statement

1. **Commensurability.**
   - For a finite-index `Γ' ≤ Γ`, `Γ'` has (PR) iff `Γ` has (PR) over the finite set `Γ/Γ'`.
   - In particular, (PR) for some finite-index subgroup is the same as (PR) for `Out(F_n)`
     over some finite Out-set.
2. **Profinite blow-ups give nothing.** If `Γ` has (PR) over a profinite `Z`, then some
   finite-index subgroup of `Γ` has plain (PR).
   - Conversely, any (PR) action `h` gives a **free** (PR) action `h × (Γ ↷ Γ̂)` over the
     profinite completion. It satisfies the stabilizer constraints of
     `boundary-pushout-of-aut-out-free-splits-mod-every-quotient` vacuously.
   - So freeness on periodic points, or on all points, can always be bought by a profinite
     factor, but only at the price of an equicontinuous, non-expansive coordinate. That is
     the branch/RF regime. It never helps to *find* a lift.
3. **Gluing.** Let `Γ ≤ Out(F_n)` be the fundamental group of a finite graph of groups with
   vertex groups `Γ_v` and edge groups `Γ_e`. Suppose:
   - each `Γ_v` has a (PR) action `h_v`;
   - for each edge, the two actions of `Γ_e` are conjugate by an element of `M`: one through
     its vertex, the other through the other vertex twisted by a representative of the
     stable letter.

   Then `Γ` has (PR). The obstruction for one edge is an element of the nonabelian
   cohomology `H^1(Γ_e; M)`. For `Γ_e = Z` it is a twisted-conjugacy class in `M`.
4. **Splittings are unavailable where they would matter.**
   - For `n ≥ 4` every finite-index subgroup of `Out(F_n)` has property (T), hence (FA), so
     item 3 has no nontrivial instance.
   - For `n = 3`, finite-index subgroups split, since `Out(F_3)` is large. But the splittings
     come from maps onto `Z` (Bieri–Strebel), and their vertex groups contain the
     corresponding kernels. No splitting with vertex groups already known to have (PR) is
     known.

## Proof

**Item 1.**
- (⇐) Restrict the fiber over the coset `Γ'`: `Γ'` preserves it and acts there by elements
  of `q̂M`.
- (⇒) Choose coset representatives `t_i` and automorphisms `T_i ∈ t_i`. Identify fiber `i`
  with `∂F_n` through `T̂_i`. For `q t_i = t_j γ` with `γ ∈ Γ'`, let `q` act from fiber `i` to
  fiber `j` by `T̂_j h_γ T̂_i^{-1}`.
  - This lies in `(t_jγt_i^{-1})^M = q̂M`, since `M` is normalized by `Aut(F_n)`.
  - Associativity is that of the induced action.

**Item 2.**
- Fix finite generators `S` of `Γ`. Each `z ↦ h_{s,z}` is locally constant on the compact
  `Z` with values in the discrete `H`. So it is constant on the pieces of a finite clopen
  partition.
- Every clopen partition of `Z = lim Z_k` is refined by the fibers of one finite level
  `Z → Z_k`, and that map is Γ-equivariant. Choose one level `k` that serves all of `S`.
- The cocycle identity `h_{sq,z} = h_{s,qz}h_{q,z}` and equivariance of `Z → Z_k` give, by
  induction on word length, that every `h_{q,·}` factors through `Z_k`. So `h` descends to a (PR) action over the finite set `Z_k`. Apply item 1 to a point
  stabilizer.
- The converse and freeness are clear, since `Γ` acts freely on `Γ̂`.

**Item 3.**
- Conjugating a (PR) action by `m ∈ M` gives a (PR) action, since `m q̂M m^{-1} = q̂M`, `M`
  being normal in `H`.
- Along a maximal tree, conjugate vertex actions so that they agree on edge groups. For each
  remaining edge `e` with stable letter `t_e`, let `r_e ∈ Aut(F_n)` represent `t_e`. The
  hypothesis gives `m_e ∈ M` with `m_e r̂_e h(c) r̂_e^{-1} m_e^{-1} = h(θ_e(c))`, and we put
  `h(t_e) = m_e r̂_e`.
- The universal property of the fundamental group gives the homomorphism. Each image lies in
  the right coset.
- Two (PR) lifts of `Γ_e` in the same band class differ by a cocycle `Γ_e → M`, and
  conjugacy by `M` is cohomologous triviality.

**Item 4.**
- Property (T) for `n ≥ 4` is `aut-f4-has-property-t`, passing to the quotient `Out(F_n)` and
  to finite-index subgroups. (T) implies (FA) (Watatani).
- `n = 3`: largeness is Grunewald–Lubotzky, quoted in that node. Bieri–Strebel: an fp group
  mapping onto `Z` is an HNN extension of a finitely generated base inside the kernel. `∎`

## Comparison with the closed-MCG team

`board/major-mcg.md` embeds `Mod(S_g)` directly in `𝒯_m = [[GL_{m+1}(Z) ⋉ Ŝ_m]]`,
`m = 6g − 7`, through its honest action on PML with integral train-track charts. That
route never meets the Birman band `π_1(S_g) → Mod(S_{g,*}) → Mod(S_g)`.

The analogous honest action of `Out(F_n)` is on `\bar{CV_n}`. It has no known integral
piecewise-projective atlas. The obvious analogue of the `9g − 9` curve coordinates fails:
Smillie–Vogtmann (1992; recalled, not re-read) show that no finite set of conjugacy classes
has length functions determining the points of Outer space for `n ≥ 3`.

This is why `Out(F_n)` needs the band route and `Mod(S_g)` does not. **Open, and worth one
lane:** does `Out(F_n)` act faithfully on some compact finite-dimensional polyhedron by
piecewise-integral-projective homeomorphisms? A yes would make the 𝒯-machinery (edge-split
operad, Sync, TD) apply to `Out(F_n)`.

## Lesson for general BH

The section problem for a band is rigid under every cheap move.
- **Commensurability** changes nothing (item 1).
- **Profinite blow-ups** buy freeness at every point, and with it every germ constraint, but
  only by adding an equicontinuous coordinate. That is exactly the non-expansive, branch/RF
  regime, where finite presentation fails, and a lift there exists only if a finite-index
  lift does (item 2).
- **Splittings** are unavailable for Kazhdan inputs (item 4).

So a solution must be a genuine dynamical splitting on an *expansive* model. Two groups with
the same band shape differ exactly in whether they admit an honest action with finite
integral coordinates:
- `Mod(S_g)` has one (PML, train tracks), so its host problem is pure finiteness;
- `Out(F_n)` has none known (Smillie–Vogtmann), so its host problem is strictification plus
  finiteness.

Before building a host for a group with a band, ask first for finite integral coordinates on
an honest compact action.
