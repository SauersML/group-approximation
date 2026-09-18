---
rg: 2
id: leavitt-mf-survivor-yields-jacobson-regular-character
kind: claim
title: A surviving MF representation of St_20 of the binary Leavitt ring pulls back to the regular MF character of EL_5 of the Jacobson ring
distinct_from:
  property-t-free-el20-full-mf-radical: its regular-character route reaches the regular character of the simple group EL_20(R) itself; this treats the Steinberg group St_20(R), which need not be simple, and lands on the regular character of the embedded Jacobson group EL_5(J), where the possibly nontrivial scalar kernel of the Leavitt character is invisible.
  leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity: that is the Connes-embeddable all-or-nothing statement for characters of EL_n(J) alone; this transports an operator-norm MF character of the Leavitt Steinberg group down to EL_5(J) and keeps operator-norm provenance.
  torsion-normal-generator-mf-character-criterion: that produces some nontrivial MF character; this identifies one specific MF character, the regular character of EL_5(J), that any failure of the full radical must produce.
  binary-jacobson-head-retaining-homomorphisms-are-faithful: that is the all-or-nothing statement for homomorphisms of EL_5(J); this applies it to the scalar-kernel quotient of a Diracized Leavitt character.
artifacts:
  - research/leavitt-mf-survivor-yields-jacobson-regular-character-proof.md
---

**ESTABLISHED (swarm-0917 w8, agent-verified, no referee).**  No property
`(T)`, Kazhdan projection or spectral-gap input is used.

**Setting.**
* `R=L_(F_2)(1,2)`, `Delta=St_20(R)`, `q=s_1t_1`, `z=x_13(q)`.
* `J=F_2<S,T | TS=1>`, `E=EL_5(J)`, `Q=1-ST`, `w=x_13(Q)`.
* `L=GL_fin(N x {1..5},F_2)`, the finitary kernel of `E`.
* `iota:E -> Delta` is the composite
  `E ~= St_5(J) -> St_5(R) -> St_20(R)`.  The first map is
  `binary-jacobson-steinberg-cover-is-elementary`.  The second is induced by
  the unital ring map `S->s_0`, `T->t_0`.  The third is rank stabilization.
  Then `iota(w)=x_13(1-s_0t_0)=z`.
* An **MF character** is a pointwise limit of normalized traces of
  operator-norm asymptotic unitary representations.

**Theorem (regular pullback).**

```text
Rad_MF(Delta) != Delta   ==>   delta_e^E is an MF character of E.      (RP1)
```

Equivalently, excluding the single named trace `delta_e^E` from the MF
characters of `EL_5(J)` proves the full MF radical of `Delta`:

```text
delta_e^E not MF   ==>   Rad_MF(Delta) = Delta.                        (RP2)
```

**Corollaries.**
1. **Unconditional dichotomy.**  Either `Rad_MF(Delta)=Delta`, or `EL_5(J)`
   has operator-norm asymptotic representations whose traces tend to
   `delta_e`.  In the second case `EL_5(J)` is MF (the witnesses are
   asymptotically injective) and also hyperlinear, since an MF character is
   Connes-embeddable.
2. **Hyperlinearity lane.**  If `EL_5(J)` is not hyperlinear, then
   `Rad_MF(Delta)=Delta` without property `(T)`.
3. **Sandwich.**  Write (HC) for `property-t-free-jacobson-head-collapse`
   and (H1) for `jacobson-regular-character-not-mf-without-property-t`.
   Then

```text
(HC)  ==>  (H1)  ==>  Rad_MF(Delta)=Delta  and  delta_e^(EL_n(R)) not MF (n>=5).
```

   The first arrow holds because a regular MF character of `E` retains `w`.
   The last conclusion holds because `E` embeds in `EL_n(R)` by
   `binary-jacobson-head-retaining-homomorphisms-are-faithful`, and the
   regular character restricts to the regular character.
   So (H1) is weaker than the old Jacobson hole (HC), and a T-free proof of
   (H1) closes both the Steinberg goal and the `EL_n(R)` regular-character
   hole.

**What a proof of (H1) may now assume.**  It suffices to refute a model
`sigma_k:E->U(d_k)` with `||sigma_k(gh)-sigma_k(g)sigma_k(h)||->0` and
`tr sigma_k(g)->0` for every `g!=1`.

On each finite subgroup `F` of `L`, `sigma_k|_F` is norm-close to a genuine
representation.  Finite groups are uniformly stable (Kazhdan 1982, "On
epsilon-representations"; this is amenability averaging, not property
`(T)`).  That genuine representation's character tends to `delta_e^F`.  So
every finite window of the finitary kernel is represented, in operator
norm, by an asymptotically regular amplification.  A projection-selection
argument therefore never has to handle rectangular or low-multiplicity
isotypic pieces.  For every finite window `F` and irreducible `pi` of `F`, the
multiplicity of `pi` divided by `d_k` tends to `dim(pi)/|F|`.

DERIVATION
leavitt-mf-survivor-yields-jacobson-regular-character-proof
