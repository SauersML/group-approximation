---
rg: 2
id: u-weyl-pairs-need-out-sigma-to-contain-all-finite-simples
kind: claim
title: "In a Weyl pair with torsion-free Lambda, the outer action on Sigma has abelian kernel on every finite subgroup; so a normalized type F witness for N_U needs a type F group Sigma whose homologically trivial outer automorphisms contain every large alternating group, which kills free, abelian, surface, RAAG and finite-Out Sigma"
distinct_from:
  normalized-benign-witnesses-give-the-semidirect-join: That shows U Weyl (a normalized witness for N_U) suffices for (d) and the root; this proves a necessary condition on the Sigma of any such witness and kills the witness classes whose Out(Sigma) has bounded finite subgroups.
  separable-benign-witness-forces-rf-quotient: That kills witnesses with Sigma profinitely closed, for any benign witness; this kills normalized witnesses through the outer action of the normalizer on Sigma, independently of separability.
  weyl-class-closes-under-free-products-and-liftable-hnn: That is the positive closure theory of the Weyl class; this is the obstruction showing its outer-action condition 4(b) is forced on every finite simple subgroup.
---

**ESTABLISHED (proposed, 2026-09-18; referee welcome).** Let `Σ ≤ Λ` with
`Λ` torsion-free (for instance a Weyl pair of type `F`). Put `M = N_Λ(Σ)`,
`W = M/Σ`, and let `ρ : W -> Out(Σ)` be the conjugation action.

1. **Abelian kernel on finite subgroups.** For every finite `Q ≤ W`,
   `Q ∩ ker ρ` is abelian: it is `D/Z(Σ)` for a torsion-free abelian group
   `D ⊇ Z(Σ)` with finite index. If `Z(Σ) = 1`, then `ρ` is injective on
   every finite subgroup of `W`.
2. **Finite simple subgroups embed in `Out(Σ)`.** Every nonabelian finite
   simple subgroup of `W` embeds in `Out(Σ)` via `ρ`. For every finite
   `Q ≤ W`, some quotient of `Q` by an abelian normal subgroup embeds.
3. **They act trivially on homology.** Let `Σ` be of type `F`. There is an
   `n_0(Σ)` such that for `n ≥ n_0`, every `A_n ≤ W` embeds in the
   homologically trivial subgroup
   `T(Σ) = ker(Out(Σ) -> ∏_k Aut H_k(Σ; Z))`.
4. **The consequence for `U`.** Suppose `N_U` has an `F(B)`-normalized type
   `F` witness, equivalently `U` is type `F` Weyl. Then the `Σ` of that
   witness is a type `F` group whose `T(Σ)` contains `A_n` for every large
   `n`. In particular `Out(Σ)` has finite subgroups of unbounded order.
   - The same holds for any group containing `A_n` for infinitely many `n`,
     such as Thompson's `V`.
5. **Class kill.** No normalized type `F` witness for `N_U` has `Σ` in any
   class where `Out(Σ)` has finite subgroups of bounded order, or where
   `T(Σ)` is torsion-free. This includes:
   - `Σ` free, since `Out(F_r)` is virtually torsion-free;
   - `Σ` free abelian, since the finite subgroups of `GL_r(Z)` are bounded;
   - closed surface groups, since the mapping class group is virtually
     torsion-free;
   - right-angled Artin groups (Charney--Vogtmann: `Out(A_Γ)` is virtually
     torsion-free);
   - any `Σ` with `Out(Σ)` finite, for example closed hyperbolic
     `n`-manifold groups with `n ≥ 3` (Mostow).

**Scope.** Item 1 uses only that `Λ` is torsion-free. So the obstruction
applies to the type `F` root and to its torsion-free `F_m` variants, not to
`F_m`-Weyl pairs whose `Λ` has torsion. It concerns the sufficient Weyl
route to the root, not the root itself: the root's witnesses need not be
normalized.

**Calibration.** The known members of the class agree with it.
- A finite `Q = F/N`, with `Σ = N` free of rank `r = 1 + |Q|(rk F - 1)`,
  embeds in `Out(F_r)`. There `r` grows with `|Q|`, consistent with the
  bound `2^r r!` on finite subgroups of `Out(F_r)`.
- For `Γ/M` with `M ⊴ Γ` of type `F`, every finite simple subgroup embeds
  in `Out(M)`.

**Open question it leaves.** Is there a type `F` group `Σ` whose
homologically trivial outer automorphism group contains `A_n` for infinitely
many `n`? If there is none, then `U` is not type `F` Weyl, and the Weyl route
to (d) is dead in type `F`. If there is one, it is the only possible shape
of `Σ` for a normalized witness of `N_U`.

Proof: route `u-weyl-pairs-need-out-sigma-to-contain-all-finite-simples-proof`.
