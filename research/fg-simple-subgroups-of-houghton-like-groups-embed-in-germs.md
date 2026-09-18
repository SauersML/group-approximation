---
rg: 2
id: fg-simple-subgroups-of-houghton-like-groups-embed-in-germs
kind: claim
title: Every finitely generated infinite simple subgroup of a Houghton-like group H_n(G) embeds in the germ group G/FSym(N), so Houghton-like envelopes create no new simple subgroups, and free-shift envelopes contain no simple FA group outside the input
distinct_from:
  houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group: that computes H_n(G)/FSym as the index-zero part of Ĝ^n and decides when it is finitely presented; this uses that computation to locate every finitely generated simple subgroup of H_n(G) inside one factor Germs(G).
  simple-kazhdan-in-germ-extension-of-v-sits-in-one-germ-group: that confines a simple Kazhdan subgroup of a finite germ extension of V to one singular germ group; this is the analogous confinement for Houghton-like groups, and it needs no Kazhdan hypothesis, only finite generation and simplicity.
  normal-germ-extensions-of-v-have-only-finite-kazhdan-subgroups: that kills infinite Kazhdan subgroups in a whole regime of germ extensions of V; this shows Houghton-like groups do not kill them (they keep every simple subgroup of the germ group) but also do not create any.
  free-shift-houghton-like-envelopes-are-not-fp: that proves free-shift envelopes are not finitely presented; this shows that, independently of finite presentation, their simple FA subgroups are exactly the conjugates of simple FA subgroups of the input P.
---

**ESTABLISHED** (lane proof, elementary, not independently reviewed; no priority claimed).
Inputs: item 1 of `houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group` (refereed by
referee a) and Serre's fixed-point theorem for FA groups acting on the Bass--Serre tree of a free
product.

## Statement

Let `G <= Sym(N)` be an infinite strongly shift-similar group, `n >= 1`, `X = [n] x N`, and
`H = H_n(G)`. Write `Germs(G) = G/FSym(N)`, `Ĝ = Germs(G) ⋊ <s̄>` and `eta : Ĝ -> Z` for the near
index, as in `houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group`.

1. **Confinement.** Let `S <= H` be finitely generated, infinite and simple. Then
   `S ∩ FSym(X) = 1`, and for some ray `k` the germ on ray `k` is an injective homomorphism
   `S -> Germs(G)`.
2. **Mallery--Zaremsky envelopes.** Let `G = E_nu(P)`, with near shift group `R_nu = <lambda(P), s>`.
   Every finitely generated infinite simple subgroup of `H_n(E_nu(P))` embeds in `R_nu`.
3. **Free-shift enumerations.** If moreover `R_nu ≅ P * Z` (the generic enumerations of
   `regular-enumerations-can-make-near-shift-free-product`) and `S` has property FA (for instance
   property (T)), then `S` embeds in `P`: its image in each factor `R_nu` is conjugate into
   `lambda(P)`.
4. **Houghton calibration.** The Houghton groups `H_n = H_n(FSym(N))` contain no finitely generated
   infinite simple subgroup.

## Proof

1. `FSym(X)` is locally finite: a finitely generated group of finitely supported permutations
   moves only finitely many points, so it is finite. `S ∩ FSym(X)` is normal in `S`. If it were
   all of `S`, the finitely generated group `S` would be finite. So by simplicity
   `S ∩ FSym(X) = 1`.
   Hence `S` embeds in `H/FSym(X)`. By item 1 of the germ-group node this is `Q_n(Ĝ)`, the
   index-zero part of `Ĝ^n`, the isomorphism recording the germ on each ray. Let
   `p_k : S -> Ĝ` be the germ on ray `k`.
   - `S` is nonabelian simple, hence perfect, so `eta ∘ p_k : S -> Z` is trivial and
     `p_k(S) <= ker(eta)`. In `Ĝ = Germs(G) ⋊ <s̄>` with `eta(s̄) = 1` and `eta(Germs(G)) = 0`
     (elements of `G` are genuine permutations), `ker(eta) = Germs(G)`.
   - The product of the `p_k` is injective on `S`, so some `p_k` is nontrivial. Its kernel is a
     proper normal subgroup of `S`, hence trivial. So `p_k : S -> Germs(G)` is injective.
2. For `G = E_nu(P)`, item 3 of the germ-group node gives `Ĝ ≅ (R_nu x R_nu) ⋊ C_2`. By item 1,
   `S` embeds in `Ĝ`. Its intersection with `R_nu x R_nu` has index at most 2 and is normal in
   `S`, so it is all of `S` (an infinite simple group has no subgroup of index 2). One of the two
   coordinate projections `S -> R_nu` is nontrivial, and it is injective by simplicity.
3. Let `R_nu = P * Z` act on its Bass--Serre tree. A group with property FA fixes a vertex in every
   action on a tree, and property (T) implies FA (Watatani). The image of `S` in `R_nu` is a
   quotient of `S`, hence has FA, hence fixes a vertex. So it is conjugate into `P` or into `Z`.
   It is nonabelian, so it is conjugate into `lambda(P) ≅ P`. Combined with item 2, `S` embeds in
   `P`.
4. For `G = FSym(N)`, `Germs(G) = 1`, so item 1 leaves no room for `S`.

## What this says about the Kazhdan reduction

`boone-higman-iff-simple-kazhdan-decidable-inputs` reduces Boone--Higman to infinite finitely
generated simple Kazhdan inputs `S`. Several host families on main contain no infinite Kazhdan
subgroup at all (for example `normal-germ-extensions-of-v-have-only-finite-kazhdan-subgroups`,
`kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf`,
`kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`), so those routes cannot prove the
conjecture.
- **The Houghton-like route passes this filter.** Item 1 shows `H_n(E_nu(P))` keeps every simple
  subgroup of its germ group, and `S <= P` sits in `lambda(P) <= Germs(E_nu(P))`.
- **It gains nothing from (T).** Items 2–3 show the envelope creates no simple subgroups beyond those
  already in `R_nu`, or in `P` for free-shift enumerations. The gate that remains, near relations
  pinning `nu` down (`free-shift-houghton-like-envelopes-are-not-fp`), concerns the chosen finitely
  presented overgroup `P`, not `S`.
- **Advice to route builders.** The overgroup `P` can always be replaced by a non-FW overgroup such as
  `P * Z`, so the FW exclusions of twisted shell normalizations
  (`fw-inputs-admit-no-twisted-shell-normalization`) never have to bind on the input side of this
  route. (Hand remark.)
