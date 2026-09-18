---
rg: 2
id: pgl-q-projective-type-a-extension
kind: claim
title: For infinitely many m, PGL_m(Q) lies in a finitely presented group whose type (A) action contains the projective action on P^(m-1)(Q)
distinct_from:
  gl-n-q-in-permutational-boone-higman-class: that asks for some type (A) overgroup with no constraint on the set acted on; this asks that the action contain the natural 2-transitive action on P^(m-1)(Q) as an orbit, which implies it.
  permutational-host-forms-agree-for-countable-inputs: that gives equivalent host forms for any input; this is one structured sufficient form for PGL_m(Q) with its natural action.
  germ-extensions-omit-standard-gl-n-q: that is an established obstruction for piecewise hosts of the natural action; this is the open target, whose Attempts record that obstruction.
  type-a-orbit-accumulation-forces-fg-nontrivial-germs: that is a general germ lemma for type (A) actions by homeomorphisms; this is the projective target it constrains.
---

**OPEN.** For infinitely many `m >= 2` there are
- a finitely presented group `Γ ≥ PGL_m(Q)`, and
- a faithful action of `Γ` on a set `S` with finitely generated point
  stabilizers and finitely many orbits of two-element subsets (type (A)),
- together with a point `s_0 ∈ S` such that `Stab_(PGL_m(Q))(s_0)` is the
  stabilizer `P(Q)` of a point of `P^(m-1)(Q)`. Then `PGL_m(Q) s_0` is a copy
  of `P^(m-1)(Q)` with its natural action.

**Strong form:** `S = P^(m-1)(Q)` itself, so that
`PGL_m(Q) ≤ Γ ≤ Sym(P^(m-1)(Q))`.

By route `gl-n-q-type-a-via-projective-extension`, the claim gives
`gl-n-q-in-permutational-boone-higman-class`, and so the root
`gl-n-q-embeds-in-fp-simple-group`.

## Reformulations (hand proofs, not independently reviewed)

- **Strong form needs only two conditions.** `PGL_m(Q)` acts faithfully and
  2-transitively on `P^(m-1)(Q)` for `m >= 2`. So any `Γ` with
  `PGL_m(Q) ≤ Γ ≤ Sym(P^(m-1)(Q))` is faithful, transitive, and has exactly one
  orbit of two-element subsets. The strong form is therefore: a finitely
  presented `Γ` with `PGL_m(Q) ≤ Γ ≤ Sym(P^(m-1)(Q))` whose point stabilizer is
  finitely generated.
  - If `Γ` is finitely generated and contains `Alt_fin(P^(m-1)(Q))`, the point
    stabilizers are automatically finitely generated
    (`fp-finitary-alternating-overgroups-have-type-a-actions`).
- **Subgroup form.** The claim for a given `m` is equivalent to the existence of:
  - a finitely presented `Γ ≥ PGL_m(Q)`, with a type (A) action on a set `S_1`
    (which may be empty); and
  - a finitely generated `Λ ≤ Γ` with `P(Q) ≤ Λ`, `PGL_m(Q) ⊄ Λ`, finitely many
    double cosets `ΛgΛ`, and finitely many `Λ`-orbits on `S_1`;
  - such that `Γ` acts faithfully on `S_1 ⊔ Γ/Λ`.

  Take `S = S_1 ⊔ Γ/Λ` and `s_0 = Λ`. The condition `PGL_m(Q) ⊄ Λ` suffices
  because `P(Q)` is maximal in `PGL_m(Q)`: a 2-transitive action is primitive,
  so its point stabilizers are maximal. Hence `Λ ∩ PGL_m(Q) = P(Q)`. Conversely,
  given the claim, take `Λ = Stab_Γ(s_0)` and `S_1 = S \ Γs_0`.
- **What `Λ` must be.** `Λ` is a finitely generated group containing
  `P(Q) ≅ Q^(m-1) x| GL_(m-1)(Q)` (the parabolic modulo scalars). By O1 of the
  root it is not residually finite. For `m = 2`, `Λ` is a finitely generated
  overgroup of `Aff(Q)` that meets `PGL_2(Q)` exactly in `Aff(Q)`.

## Attempts

1. **Natural local hosts: dead.** Suppose `Γ` acts on `RP^(m-1)` (or on
   `P^(m-1)(Q_p)`, or on an adelic model) extending the natural action, and each
   element is piecewise projective with finitely many pieces, or is so outside a
   closed nowhere dense set. Then `Γ` finitely generated forces
   `Γ ∩ PGL_m(Q) ≤ PGL_m(Z[1/N])` for some `N`
   (`germ-extensions-omit-standard-gl-n-q`, identity principle). So no such `Γ`
   contains `PGL_m(Q)`.
2. **Near actions on `P^(m-1)(Q)`: dead** (hand proof, this lane). Suppose every
   `γ ∈ Γ ≤ Sym(P^(m-1)(Q))` agrees with some `h_γ ∈ PGL_m(Q)` outside a finite
   set. This covers `FSym ⋊ PGL_m(Q)` and Houghton-type extensions of the
   natural action.
   - `h_γ` is unique: a cofinite subset contains `m + 1` points in general
     position, and those determine a projective map.
   - `γ ↦ h_γ` is a homomorphism, since `h_γ h_δ` agrees with `γδ` off a finite
     set. It is the identity on `Γ ∩ PGL_m(Q)`.
   - So if `Γ` is finitely generated, `Γ ∩ PGL_m(Q)` lies in the finitely
     generated image, inside some `PGL_m(Z[1/N])`, and misses the unipotent
     `(Q,+)`.

   This is the cofinite-topology case of Attempt 1. That topology is not
   Hausdorff, so it is recorded separately.
3. **Hosts acting by homeomorphisms: difficulty located.** Suppose `Γ` acts by
   homeomorphisms on a Hausdorff space `X` containing `P^(m-1)(Q)` with its
   natural action, where `PGL_m(Q)` acts on `X` with the identity principle
   (such as `RP^(m-1)` or a blow-up), and `s_0` accumulates on its orbit.
   Then `type-a-orbit-accumulation-forces-fg-nontrivial-germs` says the germ
   group of `Stab_Γ(s_0)` at `s_0` is a finitely generated group containing the
   germs of `P(Q)`. By the identity principle these form a copy of `P(Q)`, which
   is not finitely generated. So the germ group at a rational point must strictly
   contain the projective germs. It must be finitely generated and, by O1 of the
   root, not residually finite. That is the
   same problem one level down, for `P(Q) ≥ Aff(Q)`-type groups at a point.
4. **What is left.** A host for the strong form must permute `P^(m-1)(Q)` by
   maps that are neither locally projective in any Hausdorff topology where
   `PGL_m(Q)` has the identity principle (Attempt 1), nor almost projective
   (Attempt 2). If they are homeomorphisms, the germs at rational points must
   carry a finitely generated overgroup of `P(Q)` (Attempt 3). No candidate is
   known. The central-lift mechanism behind `Q ≤ T-bar` gives no unipotent
   divisibility (`lifts-add-no-unipotent-divisibility`). Whether the Kojima--Sheng
   mechanism for `Q ≤ nV` can carry `Aff(Q)` is open (lane gq-bt-kojima).
