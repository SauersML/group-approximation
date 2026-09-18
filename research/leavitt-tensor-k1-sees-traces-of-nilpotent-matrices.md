---
rg: 2
id: leavitt-tensor-k1-sees-traces-of-nilpotent-matrices
kind: claim
title: K_1 of a Leavitt tensor detects traces of nilpotent coefficient matrices, so K_1(k[G] ⊗ L_k(1,2)) is nonzero when G has p-torsion in characteristic p
distinct_from:
  leavitt-tensor-kills-k1-of-coefficient-matrices: that shows the image of K_1(B) in K_1(B ⊗ L) is zero for every B; this shows the unipotents 1 + x ⊗ e_1 with x nilpotent over B can survive, and gives an explicit homomorphism K_1(B ⊗ L) -> k detecting them. So the swindle does not extend past B ⊗ 1.
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that imports vanishing of all K-groups of B ⊗ L for regular supercoherent B; this shows vanishing of K_1 fails for the non-regular rings k[ε] and k[G] with p-torsion, and gives a necessary condition on arbitrary B.
  regular-coherent-coefficients-kill-leavitt-tensor-k-theory: that is a sufficient condition for vanishing; this is a necessary condition (nilpotent traces lie in [B,B]) with explicit counterexamples.
  leavitt-unit-hosts-need-nilpotents-of-unbounded-index: that constrains ring homomorphisms from Leavitt unit groups into rings with bounded nilpotence index; this constrains K_1 of B ⊗ L through traces of nilpotents of B, with no bound on the index.
---

**ESTABLISHED.** Let `k` be a field, `L = L_k(1,2)` with generators
`e_1, e_2, e_1^*, e_2^*`, `B` a unital `k`-algebra and `R = B ⊗_k L`.

**Theorem.** For every integer `m >= 1` and every `k`-linear `φ : B -> k` with
`φ([B,B]) = 0`, there is a group homomorphism `χ_(φ,m) : K_1(R) -> (k,+)` such
that for every `n` and every nilpotent `x ∈ M_n(B)`,

`χ_(φ,m)[1 + x ⊗ e_1] = (-1)^(m-1) φ(tr x^m)`.

**Corollaries.**
1. **Necessary screen.** If `K_1(B ⊗ L) = 0`, then `tr(x^m) ∈ [B,B]` for every
   nilpotent matrix `x` over `B` and every `m >= 1`.
2. **Torsion units.** If `char k = p > 0`, `K_1(B ⊗ L) = 0` and `u ∈ B^x` has
   `u^(p^j) = 1`, then `(u - 1)^m ∈ [B,B]` for all `m >= 1`. In particular
   `u ≡ 1` modulo `[B,B]`.
3. **Counterexamples.** `K_1(k[ε] ⊗ L) != 0` for `ε^2 = 0`. If `char k = p > 0`
   and `G` has an element of order `p`, then `K_1(k[G] ⊗ L) != 0`.
4. **Screen passes for semisimple Artinian `B`.** Over a division ring every
   nilpotent matrix is conjugate to a strictly upper triangular one, so the
   screen holds for `M_r(D)`.

**Class killed.** Every argument that proves `K_1(B ⊗ L) = 0` from hypotheses
that `k[ε]` satisfies, or `F_2[Z/2] ≅ F_2[ε]` satisfies, dies. This covers
coefficient-free swindles, arguments natural in `B`, and hypotheses such as
commutative, finite-dimensional, local or noetherian.
- *Invariant.* `χ_(φ,1)`, with `φ(a + bε) = b`.
- *Step where it dies.* Passing from matrices over `B ⊗ 1`, where
  `leavitt-tensor-kills-k1-of-coefficient-matrices` works, to the unipotent
  `1 + ε ⊗ e_1`, whose value is `1`.

Regularity-type hypotheses, as in Ara--Cortiñas, are therefore genuinely needed.
The nonvanishing matches the nil-terms that regularity removes in the
Ara--Brustenga--Cortiñas computation. No novelty is claimed for that; the
explicit detector is what is recorded here.

DERIVATION
leavitt-tensor-k1-sees-traces-of-nilpotent-matrices-proof
