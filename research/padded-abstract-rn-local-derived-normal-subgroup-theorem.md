---
rg: 2
id: padded-abstract-rn-local-derived-normal-subgroup-theorem
kind: claim
title: The finite-index derived subgroup of an even padded abstract RN group is relatively simple for its boundary kernel and has a type A2 clopen action
distinct_from:
  cantor-prefix-subgroup-detects-every-normal-kernel: that detects normal subgroups in a faithful boundary group; this treats abstract table groups whose nontrivial formal labels can act trivially and must retain those labels throughout the support calculus.
  padded-abstract-rn-perfect-decidable-nonrecursive-kernel: that is an existential hard witness with undecidability and non-removal properties; this is the uniform structural theorem for arbitrary finite free recursion data satisfying the finite-abelianization padding condition.
  abstract-rover-nekrashevych-groups-are-finitely-presented: that supplies the abstract finite presentation; this concerns the proper normal subgroups and clopen stabilizers of its derived subgroup.
artifacts:
  - research/artifacts/padded-abstract-rn-manuscript-integration-2026-09-20.md
---

## Statement

Let `F` be finite-rank free, let `ψ:F→F^d⋊Sym(d)` be any finite recursion,
and add `k≥1` fixed letters having section `f` on an input `f`. Suppose
`D=d+k≥4` is even and the integer matrix `B=(k−1)I+A` is nonsingular, where
the columns of `A` sum the old sections' exponent vectors. Put
`P=V_D(F,ψ_k)` and `E=P′`. The abstract table group contains its prefix
subgroup `V_D`. Let `K` be the boundary-action kernel and `M=E∩K`.

Then `M` contains every proper normal subgroup of `E`, `E` is perfect, and
the action of `E` on the proper nonempty clopen subsets of the boundary is
of type `[A₂]`. In particular, the kernel is `M`, the quotient `E/M` is
infinite nonabelian simple, and every nonidentity prefix element normally
generates `E`.

This statement does **not** assume that the recursion has a nonrecursive
kernel. Finite index follows separately from the finite abelianization
`P_ab≅ℤ^r/Bℤ^r`; finite presentation follows from the abstract RN
presentation and Reidemeister–Schreier. The new hard-witness synthesis needs
this structural conclusion for its chosen padded recursion.

## Attempts

The user-supplied manuscript proposes the following proof, reconstructed in
Sections 7 and 9 of the linked artifact. It remains a **proof-review
obligation**, with no incoming complete-proof route added in this integration.

1. Define `D(Y)` by tables having identity maps and identity labels off the
   clopen `Y`. Verify that common expansion preserves the required support
   calculus; prove restriction products, disjoint commutation and conjugation
   transport without passing to the faithful boundary quotient.
2. Use cone-count residues modulo `D−1` to move every proper clopen into a
   specified nonempty cone. Split prefix swaps and expand labels to obtain
   arbitrarily small formal supports. Prove
   `P′=⟨D(Y)′ : Y proper clopen⟩`; this is the generation assertion required
   after the double commutator, not a consequence of displacement alone.
3. For `n∈L◁E` moving a cone `O` off itself, balance arbitrary `a,b∈D(B₀)`
   into `a₀=[a,v₁], b₀=[b,v₂]∈E` on three disjoint subcones of `O`. Check
   `[[n,a₀⁻¹],b₀]=[a,b]` in the **abstract** group, then transport local
   derived groups and apply step 2 to conclude `L=E`. Perfectness follows
   because `E/M` contains the nonabelian simple prefix subgroup.
4. Prove `P_U=D(U)×D(Uᶜ)` by formal restriction. Generate each factor by its
   finitely generated forest-prefix group and finitely many localized free
   states. Check finite-index transfer to `E_U` and the Boolean-atom residue
   classification of pair orbits.

The supplied argument gives a concrete route to review these points, but
neither its submission nor the older faithful displacement theorem is an
independent validation of the nonfaithful support statements. This claim
therefore deliberately remains unresolved until a justified proof route is
added. It is a mathematical lemma, not a procedural “review passed” flag.
