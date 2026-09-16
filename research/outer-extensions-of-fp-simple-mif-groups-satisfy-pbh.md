---
rg: 2
id: outer-extensions-of-fp-simple-mif-groups-satisfy-pbh
kind: claim
title: Outer extensions of finitely presented simple MIF groups by finitely presented groups satisfy permutational Boone--Higman
distinct_from:
  decidable-groups-embed-in-outer-extensions-of-fp-simple-groups: that is the open universality statement asking every decidable input to sit in an outer extension of SOME finitely presented simple group; this is a theorem about the extensions themselves when the kernel is MIF, and it shows that the MIF-kernel form of that statement is equivalent to permutational Boone--Higman group by group.
  relative-automorphism-of-fp-simple-mif-group-has-type-a-action: that is BFFHZ Theorem E, a type (A) action of Aut_S(S * F_n), whose elements fix S pointwise; this enlarges that actor by automorphisms that move S and computes the kernel of the enlarged action, which is where the new lemma on word maps enters.
  fp-simple-highly-transitive-groups-satisfy-pbh: that is BFFHZ Theorem C and puts subgroups of finitely presented simple MIF groups in the permutational class; this puts extensions of such groups by outer automorphism groups in the class, and those are not subgroups of the kernel.
  normalizer-image-of-type-a-actor-is-type-a: that is the general enlargement lemma for a type (A) actor by normalizing permutations Q, conditional on Q/(Q ∩ Γ) being finitely presented; this is one specific enlargement, by Aut(S) acting on Hom_S(S * F_n, S), whose content is the computation of Q ∩ Γ through the MIF word-map lemma.
  normalizer-extension-of-type-a-actor-is-a2-cover: that builds non-faithful type [A_2] covers by free groups and bounds their images from below; this builds a faithful type (A) action and identifies the kernel of the unquotiented action as a copy of S.
  pbh-class-closed-under-relative-holomorphs: that adds the free product M * F_m as a normal subgroup under Aut_M, for M already in the class; this adds automorphisms of the simple group S itself, with finitely presented outer part, and needs S finitely presented, simple and MIF.
  boone-higman-type-a-class-closed-under-finite-extensions: that is closure under finite direct products and finite-index overgroups; this is closure of the kernel under overgroups with possibly infinite finitely presented quotient, for finitely presented simple MIF kernels only.
  outer-extension-word-problem-is-kernel-bounded: that bounds the word problem of an outer extension by that of its kernel; this places MIF-kernel outer extensions in the permutational class, a structural conclusion giving no complexity bound.
  outer-extensions-of-fp-simple-groups-are-isolated: that proves such extensions are isolated groups; this proves that, for MIF kernels, they embed in type (A) actors.
artifacts:
  - research/artifacts/outer-extensions-mif-pbh-2026-09-16.md
---

**ESTABLISHED** through `outer-extensions-of-fp-simple-mif-groups-pbh-proof`. Not
independently reviewed.

## Conventions

- **MIF.** In BFFHZ (arXiv:2503.21882v2, §2), a group `S` is mixed identity free if
  for all `n` and all `1 ≠ w ∈ S * F_n` some `S`-homomorphism `S * F_n → S` sends `w`
  to a nontrivial element.
- **`B_A`.** This is the class of groups embedding in a group with an action of type
  (A), as in `boone-higman-type-a-class-closed-under-finite-extensions`. These are the
  groups satisfying permutational Boone--Higman (PBH).
- **The actor.** For `n ≥ 2` put `A = Aut_S(S * F_n)` and `X = Hom_S(S * F_n, S)`.

## Statement

Let `S` be a finitely presented simple MIF group.

1. **(W) Word maps.** If `u ∈ S * ⟨x⟩` and `t ↦ u(t)` is an endomorphism of `S`,
   then `u = 1` or `u = a x a^-1` with `a ∈ S`. In particular, every automorphism of
   `S` given by a one-variable word map with constants is inner.
2. **(K) The enlarged actor.** Let `Inn(S) ≤ B ≤ Aut(S)` and `n ≥ 2`. Put
   `Γ_B = A ⋊ B`, with `B` acting on `S` and trivially on `F_n`. `Γ_B` acts on `X` by
   `γ · f = γ|_S ∘ f ∘ γ^-1`. The kernel of this action is the group
   `{ w ↦ s w s^-1 : s ∈ S } ≅ S` of inner automorphisms of `S * F_n` by elements of
   `S`, and `B` meets it trivially.
3. **(A) Type (A).** If moreover `B/Inn(S)` is finitely presented, then the quotient
   `Λ_B` of `Γ_B` by that kernel acts on `X` with type (A) and contains `B`. So
   `B ∈ B_A`.
4. **(O) Outer extensions.** Let `1 → S → I → Q → 1` be exact, with `Q` finitely
   presented and the conjugation map `Q → Out(S)` injective. Then `I ∈ B_A`. Hence
   every subgroup of `I` has solvable word problem and embeds in a finitely presented
   simple group.
5. **(S) Subgroups of `Aut(S)`.** If `H ≤ Aut(S)` has image in `Out(S)` contained in a
   finitely presented subgroup, then `H ∈ B_A`. In particular, if `Out(S)` is finitely
   presented, then `Aut(S) ∈ B_A`.
For arbitrary groups:

6. **(E) Per-group equivalence.** A finitely generated group lies in `B_A` if and only
   if, for some finitely presented simple MIF group `S`, it embeds in an extension as
   in (O).
7. **(R) What the open statement can add.** Let `G` be a finitely generated group
   embedding in an outer extension `I` as in
   `decidable-groups-embed-in-outer-extensions-of-fp-simple-groups`, with `G ∉ B_A`.
   Then the kernel is infinite and not MIF. If the kernel already lies in `B_A`, then
   the quotient `Q` is infinite.

## Where MIF enters

MIF is used exactly twice.
- **Faithfulness of `A` on `X`.** This is BFFHZ Lemma 2.2.
- **The outer part of the kernel.** An element of the kernel of `Γ_B` restricts on `S`
  to an automorphism given by a one-variable word map. By (W) it is inner, which pins
  the kernel down to the inner copy of `S`.

Without MIF, everything else in the argument survives. `Λ_B` is then a type (A)
actor containing `B` exactly when the kernel is finitely normally generated. That
holds provided both:
- BFFHZ Question 3.2 has a positive answer for `S`;
- the word automorphisms in `B` are finitely normally generated modulo `Inn(S)`.

This is recorded as Proposition 9 of the artifact, and it is not part of the claim.

## Consequence for the parent

The MIF-kernel case of `decidable-groups-embed-in-outer-extensions-of-fp-simple-groups`
is permutational Boone--Higman. By (E), for every finitely generated `G`,
embeddability in an MIF-kernel outer extension is the same as `G ∈ B_A`. By BFFHZ
Remark 3.5, finitely generated simple groups that are highly transitive are MIF.
Examples are Thompson's `V`, the finitely presented commutator subgroups of
Röver--Nekrashevych groups, twisted Brin--Thompson groups and Burger--Mozes groups.
So outer extensions of these kernels by finitely presented groups of outer
automorphisms add no witnesses beyond PBH. A proof of the parent that does not pass
through PBH must use infinite non-MIF finitely presented simple kernels.
