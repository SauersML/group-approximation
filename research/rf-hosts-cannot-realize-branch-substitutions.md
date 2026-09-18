---
rg: 2
id: rf-hosts-cannot-realize-branch-substitutions
kind: claim
title: If a group contains a weakly branch group G and an element t conjugating G into its first level stabilizer, every finite quotient kills the derived subgroup of the rigid copies of the branching subgroup; so no residually finite host realizes such a substitution
distinct_from:
  rf-hosts-cannot-realize-the-lysenok-substitution: that uses torsion to identify ⟨Γ,t⟩ with Grigorchuk's HNN extension and then cites its failure of residual finiteness; this proves the failure directly, for every weakly branch group and every substitution into the level stabilizer, torsion or not, and for every group containing such a pair, not only the HNN extension.
  basilica-hnn-extension-is-fp-amenable-non-ea: that imports finite presentation and amenability of the Bartholdi–Virág extension; this shows it is not residually finite, so it lies in no self-similar group.
---

**ESTABLISHED** (lane proof below, elementary; no priority claimed. Non-residual finiteness of Grigorchuk's extension
is due to Sapir–Wise, J. Pure Appl. Algebra 166 (2002), and Grigorchuk; the uniform argument here was not found
in the sources read.)

## Statement

Let `G <= Aut(X^*)` be self-similar and transitive on `X`. For `x in X` and `h in Aut(X^*)`, let `ι_x(h)` act as
`h` on the cone `xX^*` and trivially elsewhere. Let `L ◁ G` be non-abelian with `ι_x(L) ⊆ G` for all `x`, i.e.
`G` is weakly branch over `L` at the first level. Let `H` be any group containing `G` and an element `t` with

    t^{-1} G t ⊆ St_G(1).

Then every homomorphism `φ` from `H` to a finite group kills `ι_x([L,L]) ≠ 1` for every `x`. So `H` is not
residually finite, and it embeds in no self-similar group and in no group acting faithfully on a locally finite
rooted tree.

## Instances

- **Grigorchuk.** `Γ` is branch over `K = ⟨⟨(ab)^2⟩⟩`, and the Lysenok substitution maps `Γ` into `St_Γ(1)`. So
  Grigorchuk's finitely presented extension `Γ̃` is not residually finite. This reproves Sapir–Wise, and makes
  `rf-hosts-cannot-realize-the-lysenok-substitution` citation-free.
- **Basilica.** `B` is weakly branch over `B'`, with `B''` nontrivial. The Bartholdi–Virág substitution
  `a ↦ b^2 = (a,a)`, `b ↦ a = (1,b)` maps `B` into `St_B(1)`. So the finitely presented amenable extension `B̃`
  (`basilica-hnn-extension-is-fp-amenable-non-ea`) is not residually finite. No torsion is used, so the torsion
  lemma of the Lysenok node is not needed here.
- More generally, every ascending HNN extension along a "last-section" substitution
  `σ(g) = (ψ_0(g), …, g)` of a weakly branch automaton group is not residually finite. Those are the hosts of
  `bounded-last-section-ascending-hnns-satisfy-boone-higman`, which are Boone–Higman only through `V`-type hosts.

## Proof

Let `Q` be finite, `φ: H -> Q`, and `K = G ∩ ker φ`.
- **`K` is not in the level stabilizer.** `φ(t)^{-1} φ(G) φ(t) = φ(t^{-1}Gt) ⊆ φ(G)`. Conjugation is injective
  and `φ(G)` is finite, so this is an equality, and `G = (t^{-1}Gt) K ⊆ St_G(1) K`. Since `G ≠ St_G(1)`, `K`
  contains some `k` with `k(x) = y ≠ x`.
- **One rigid copy becomes abelian.** For `ℓ in L`, `k ι_x(ℓ) k^{-1} = ι_y(k|_x ℓ k|_x^{-1})`, and `φ(k) = 1`.
  So `φ(ι_x(ℓ)) = φ(ι_y(m))` for an element `ι_y(m)` supported on `yX^*`. That element commutes with
  `ι_x(L)`, so `φ(ι_x(L))` is abelian.
- **All rigid copies.** For `g in G`, `g ι_x(ℓ) g^{-1} = ι_{g(x)}(g|_x ℓ g|_x^{-1})`, and `g|_x in G` normalizes
  `L`. So `g ι_x(L) g^{-1} = ι_{g(x)}(L)`, and transitivity makes every `φ(ι_{x'}(L))` abelian.
- **Conclusion.** `φ(ι_{x'}([L,L])) = 1`. Finally `ι_{x'}` is injective, and `[L,L] ≠ 1`. ∎

## Lesson for general BH

The mechanism that makes branch groups "finitely presented up to an endomorphism" is intrinsically not
residually finite. A conjugator that pushes the group into its level stabilizer forces a level-moving element
into every finite-quotient kernel, and that collapses the rigid stabilizers. So a finitely presented self-similar
(or any residually finite) overgroup of a weakly branch group has to do without any such conjugator. The
L-presentation cannot be "closed up" inside the host. `V`-type hosts are not residually finite, so they escape,
with the prefix shift playing `t`.
