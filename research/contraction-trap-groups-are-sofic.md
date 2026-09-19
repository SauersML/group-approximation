---
rg: 2
id: contraction-trap-groups-are-sofic
kind: claim
title: Universal contraction-trap groups (an ascending HNN over a free group with a letter centralizing the base) are sofic, so co-Hopfian contraction traps prove non-LEF but can never prove non-sofic or non-hyperlinear; this includes the rank-three trap of EL_3(J)
distinct_from:
  centralizing-hnn-over-conjugate-basis-is-always-sofic: that treats the three-generator family H_J, whose centralized subgroup is spanned by conjugates of one generator, through a right-angled Artin kernel; here the centralizing letter commutes with the whole base of an ascending HNN extension and no second splitting exists, and soficity comes from a locally residually finite kernel over the stable-letter quotient.
  centralizing-hnn-is-residually-finite-iff-edge-is-separable: that is the residual-finiteness criterion for one centralizing HNN extension; this iterates it along the ascending chain phi^j(F), adds a separability-transfer lemma for subgroups of the edge, and concludes soficity of a group that is not residually finite.
  ascending-hnn-base-profinite-closure-telescope: that shows the base of a proper ascending HNN extension is never separable, which is exactly why the trap group is not residually finite; this shows the same group with the centralizing letter is nevertheless sofic.
  free-group-doubles-over-any-subgroup-are-sofic: that is the symmetric double F *_H F; the trap group is a centralizing HNN extension of an ascending HNN extension, which is neither a double nor an amalgam over an amenable group.
  binary-jacobson-el3-is-sofic: that asks for soficity of EL_3(J) itself; this proves soficity only of the universal group of the contraction-trap certificate that maps to EL_3(J), and so kills one class of non-soficity arguments without deciding the question.
artifacts:
  - research/contraction-trap-groups-are-sofic-proof.md
  - experiments/contraction-trap-soficity-2026-09-17/stallings_trap.py
  - experiments/contraction-trap-soficity-2026-09-17/output.txt
---

**ESTABLISHED** (route `contraction-trap-groups-are-sofic-proof`; agent-verified, no referee).

**Definition.** Let `F` be a finitely generated group and `phi : F -> F` an injective endomorphism. The
*contraction-trap group* is

```text
T(F, phi) = < F, g, e | g x g^(-1) = phi(x),  [e, x] = 1   (x in F) >.
```

For `x in F \ phi(F)` put `w_x = [e, g^(-1) x g]`.

**Theorem.** Assume `F` is residually finite and every subgroup `phi^j(F)` (`j >= 1`) is closed in the
profinite topology of `F`. This holds for every injective endomorphism of a finitely generated free group,
by M. Hall's theorem.
1. **(CT1) Soficity.** `T(F, phi)` is sofic, and hence hyperlinear. More precisely, the kernel `K` of
   `T -> Z` (`g -> 1`, `F, e -> 0`) is a directed union of residually finite groups, and `T = K ⋊ <g>`.
2. **(CT2) The trap is exact.** If `phi` is not surjective and `x in F \ phi(F)`, then `w_x != 1` in `T`
   (Britton's lemma). Every homomorphism from `T` to a finite group kills `w_x` (the trap mechanism of
   `jacobson-el3-is-not-lef`, which is on the landing branch). So `T` is sofic but not residually finite,
   and, being finitely presented when `F` is free, it is not LEF.
3. **(CT3) The EL_3(J) instance.** The certificate of `jacobson-el3-is-not-lef` is a homomorphism
   `Gamma_3 -> EL_3(R)` from `Gamma_3 = T(F_6, phi_C)`. Here `F_6 = F(a1, a2, a3, a4, c, d)` and `phi_C` is
   given by (C1)-(C6):
   * `a1 -> a2` and `a3 -> a4`;
   * `a2 -> c U a1 U^(-1)` and `a4 -> U a3 U^(-1) d^(-1)`;
   * `c -> U c U^(-1)` and `d -> U d U^(-1)`;
   * `U = a2 a4^(-1) a2 a1^(-1) a3 a1^(-1)`.

   The Stallings graph of `phi_C(F_6)` has 16 vertices, 21 edges and rank 6. So `phi_C` is injective,
   `a1 notin phi_C(F_6)` and `phi_C(F_6)` has infinite index; this is checked exactly by
   `stallings_trap.py`, which exits 0. By (CT1), `Gamma_3` is sofic. By (CT2), its witness
   `w = [e, g^(-1) a1 g]` is nontrivial in `Gamma_3`. It maps to `x_23(-sq)` in `EL_3(R)`.

**Class kill.**
* **Class.** Arguments that derive "the witness dies (trace `-> 1`, or Hamming distance to the identity
  `-> 0`) in every sofic or hyperlinear approximation of `G`" from a contraction-trap certificate
  `T(F, phi) -> G` alone. This covers any finite list of relations of the forms `g a g^(-1) = phi(a)` and
  `[e, a] = 1` on a free base, with `phi` injective.
* **Members.**
  * the rank-three trap for `EL_3(J)` and `EL_3(R)` whenever `ts = 1 != st`;
  * the `P_(2,2)` Baumslag-Solitar trap of `p22-double-parabolic-is-not-lef`, whose trapped subgroup is
    abelian, a case already covered by amenable HNN permanence;
  * every co-Hopfian-hull argument of the form "`Ad sigma(g)` maps the hull into itself, so onto".
* **Invariant.** The injective endomorphism `Ad sigma(g)` of the hull of `sigma(F)`, where `sigma` is the model.
* **Step where every member dies.** "Injective, hence surjective." This needs the hull to be finite, or
  finite-dimensional algebraic. In a sofic or tracial ultraproduct model the hull is an infinite group, or
  a II_1 von Neumann algebra `N` with a proper trace-preserving copy `g N g^* ⊂ N`. The step fails, and it
  must fail, because by (CT1) the universal group `T(F, phi)` has sofic approximations. In those
  approximations `w_x` has normalized fixed-point mass `-> 0`, since sofic approximations of a group
  separate every nontrivial element.
* **Consequence.** A non-soficity or non-hyperlinearity proof for `EL_3(J)`, or for `St_20(L(1,2))` in the
  bounty hole `agent-leavitt-not-bcs-negative-root-corner`, has to use relations of the target outside every
  contraction-trap certificate. Examples are the relations inside `A` (such as `SL_2(F_2)` torsion and
  finitary root identities) or property (T) of the ambient group. The trap alone certifies non-LEF and
  nothing more.

**What is not claimed.**
* Soficity of `EL_3(J)`.
* Soficity of a trap group whose centralizing letter commutes only with a subgroup `A_0 < F` that
  `phi` does not map into itself. Then the edge groups `phi^j(A_0)` are not nested, and the
  separability transfer of the proof does not apply.
* Soficity of a trap certificate enlarged by relations inside `F` (a non-free base). Here (CT1) still
  applies whenever the base is residually finite with all `phi^j(F)` separable, for example when the base
  is LERF.
