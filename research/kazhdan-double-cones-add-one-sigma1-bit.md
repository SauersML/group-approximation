---
rg: 2
id: kazhdan-double-cones-add-one-sigma1-bit
kind: claim
title: Assembly edges are transparent, and Kun-Thom double cones add only one Sigma-zero-one conjunct to soficity, so neither a KMS edge nor a Kazhdan double cone is a one-way propagator for finite presentations
distinct_from:
  amenable-edge-assemblies-have-delta2-sofic-locus: that is the Delta-zero-two ceiling for assemblies over Noetherian decidable amenable edges; this shows the edge class never enters the presented group at all (so a KMS edge is not a new object), and kills the non-amenable Kazhdan-edge escape in its cone form.
  finitely-generated-centralizer-switches-are-sigma1: that is about amenability of centralizing HNN switches over amenable bases; this is about soficity of commutation cones with a non-amenable Kazhdan subgroup, where nonsoficity comes from an embedded Kun-Thom double.
  kazhdan-lamp-amplifier-for-machine-center: that seeks a lamp-module amplifier (wreath form, killed at finite presentation by the Cornulier obstruction); this is the matching finite-presentation obstruction for the double form of the same Kun-Thom mechanism.
  kt-pair-group-double-is-nonsofic: that is the literature input (the double G *_Gamma G is nonsofic); this uses it as a gadget and computes the exact arithmetic content the gadget can carry.
  sofic-fp-hard-for-every-finite-difference-level: that realises the lower bound with Z-edge kill and collapse gadgets; the Kazhdan cone here is a new collapse-type gadget with a Kazhdan edge, and the theorem shows it adds nothing beyond one Sigma-zero-one conjunct.
  sofic-recognition-finite-presentations-is-pi2-complete: that is the open completeness statement; this is an obstruction ruling out two proposed routes to it and naming the construction that survives.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `kazhdan-double-cones-add-one-sigma1-bit-proof`.

## Part E: assembly edges are transparent

Let `P_e` be the group presented by an assembly in the sense of
[[amenable-edge-assemblies-have-delta2-sofic-locus]] (vertex presentations `V_v`, edge groups `E_eps` with
generator tuples `iota_(eps,o)`, `iota_(eps,t)`).  The presentation of `P_e` uses only the **generators** of
each `E_eps` and never its relations.  Hence:

- `P_e` is unchanged if every `E_eps` is replaced by the free group on its generating tuple;
- the only way an edge group enters is through the **soficity certificate**: permanence needs the images
  `iota_(eps,*)(E_eps) ≤ V*_v` to be amenable.

So a "KMS machine-group edge" is not a new presented object.  Whatever one-way propagation it carries must be
carried by the vertex groups and the subgroups their words generate.  The brief's step "a KMS edge as a
one-way propagator" is **equivalent** to a vertex-side statement: vertex groups `V_v` together with finitely
generated amenable subgroups `U_eps ≤ V_v` (the edge images) such that the normalised vertex quotients
`V*_v = V_v/<<kills propagated along the edges>>` are sofic exactly on `INF`.  The failure of (N2) in a KMS
edge only removes the oracle algorithm of that node's part (B); it adds no group-theoretic mechanism.

## Part K: Kun-Thom double cones

Fix a **double pair** `Gamma ≤ G`: `G` finitely presented and sofic, `Gamma ≠ 1` finitely generated, and
`G *_Gamma G` nonsofic.  (The Theorem E pairs of [[kt-pair-group-double-is-nonsofic]] give the last condition;
the obstruction below holds for every double pair, whichever exist.)

For a group `H` and a subgroup `C ≤ H`, the **Kazhdan cone** is

```text
X(H, C) = (H * G) / << [c, g] : c in C, g in Gamma >>  =  H *_C (C x Gamma) *_Gamma G .
```

**(K1) Double embedding.**  If `Y ⊇ Gamma` is any group and `y ∈ Y \ Gamma` centralises `Gamma`, then
`G *_Gamma G` embeds in `Y *_Gamma G` (first copy `g ↦ g`, second copy `g ↦ y g y^-1`).  So `Y *_Gamma G` is
nonsofic.

**(K2) Dichotomy.**  `H` and `G` embed in `X(H,C)`, and `C_X(Gamma) ∩ H = C`.  Moreover

```text
X(H, C) is sofic   <=>   H is sofic  and  C = 1 .
```

If `C = 1` then `X = H * G`.  If `C ≠ 1`, apply (K1) with `Y = H *_C (C x Gamma)` and `y ∈ C \ 1`.

**(K3) Finite presentation pins the cone.**  If `H` is finitely presented, then `X(H,C)` is finitely presented
**iff** `C` is finitely generated.

**(K4) One Sigma-zero-one conjunct.**  Let `(H_e, k_e)` be computable, with `H_e` finitely presented and
`k_e` a finite tuple of words, and put `X_e = X(H_e, <k_e>)`.  Then

```text
SOFIC(X_e)  <=>  SOFIC(H_e)  and  [ every word of k_e is 1 in H_e ] ,
```

and the bracket is `Sigma^0_1`.  By induction, any computable family built from base finite presentations by
free products and computably many cone steps (nested in any order, with cone subgroups drawn from anywhere in
the group built so far) has sofic locus `L ∩ S`, where `L` is the intersection of the base families' loci and `S` is
`Sigma^0_1`.

**Corollary.**
- Kazhdan cones over a base family with a `Delta^0_2` sofic locus keep a `Delta^0_2` locus.  In particular,
  cones over the amenable-edge assemblies of [[amenable-edge-assemblies-have-delta2-sofic-locus]] stay below
  the ceiling of that node.
- Kazhdan cones never reduce `INF` to `SOFIC_fp` on their own.  They are collapse gadgets, with the same
  polarity as `C(P,w)` of [[sofic-fp-hard-for-every-finite-difference-level]].

## Calibration: recursive presentations

Drop finite presentation.  Take `H = G(M)`, the finitely presented solvable (hence sofic) Minsky machine group
of [[sofic-fp-hard-for-every-finite-difference-level]], with words `w_n = 1` iff `n` is accepted, and let `M`
accept `A = {<e,m> : |W_e| > m}`.  Put `C_e = <w_(<e,m>) : m ∈ N>`.  Then `X(G(M), C_e)` is recursively
presented and is sofic **iff** `e ∈ INF`.  This reproduces the known `Pi^0_2`-completeness for recursive
presentations by a new mechanism, a Kazhdan double instead of a nonsofic seed.

(K3) is exactly the step that fails for finite presentations.  The cone subgroup must be infinitely
generated for the `Pi^0_2` event "every generator of `C_e` dies" to be expressible, and then `X` is not
finitely presented.  For the double this is the counterpart of the Cornulier double-coset obstruction that
kills the wreath amplifier A3 of [[kazhdan-lamp-amplifier-for-machine-center]].  Taking `C = Phi_e`, the
central machine subgroup of [[machine-center-vanishes-exactly-on-inf]], gives a group that is sofic iff
`e ∈ INF` (when `G_e` is sofic), but it is finitely presented only when `Phi_e` is finitely generated.

## What survives

Only constructions in which the centraliser of the Kazhdan subgroup is infinitely generated **without**
being imposed by relations:

1. **Twisted-diagonal cones.**  Take `Y = H x Gamma` and the graph `Gamma_psi = {(psi(g), g)}` of a
   homomorphism `psi : Gamma -> H`.  Then `X = Y *_(Gamma_psi) G` is finitely presented whenever `H` and
   `Gamma` are, and `C_Y(Gamma_psi) = C_H(psi(Gamma)) x Z(Gamma)`, which may be infinitely generated.  By (K1)
   it is nonsofic as soon as `C_H(psi(Gamma)) ≠ 1`.  **Missing statement:** a soficity theorem for amalgams
   `Y *_Gamma G` over a Kazhdan `Gamma` in which `Gamma` is **not** a free factor of `Y`.  Every soficity
   certificate currently available for amalgams over a Kun-Thom subgroup is a free-product splitting
   `Y = Gamma * A`.  Without such a theorem the positive (INF) branch cannot be certified.
2. **Non-colimit constructions**, such as lamp modules or Higman ropes, which this theorem does not touch.
