---
rg: 2
id: locally-indicable-groups-are-torus-surjunctive-proof
kind: route
title: The constants give an invertible augmentation of the degree matrix, and Strebel's D(Z) property lifts injectivity from the augmentation to the group ring
target: locally-indicable-groups-are-torus-surjunctive
requires:
  - strebel-class-dz-is-locally-indicable
  - torus-automata-over-rf-or-domain-groups-are-surjunctive
  - torus-degree-regular-on-prime-power-residual-support
  - torus-automata-with-regular-degree-are-surjective
artifacts:
  - research/artifacts/torus-degree-locally-indicable-and-fox-witness-2026-09-18.md
---

Artifact Section 2 (Theorem A).

1. **Constants.** The periodic-point lemma of
   `torus-automata-over-rf-or-domain-groups-are-surjunctive`, at `N = G`, holds over every group
   (route step 3 there). It gives `epsilon(D) in GL_d(Z)`. So `r_D (x) Z = r_{epsilon(D)}` is
   injective on `Z[H]^d (x)_{Z[H]} Z = Z^d`, and `epsilon(D)` is the same whether computed in
   `Z[H]` or in `Z[G]`.
2. **Lift.** `r_D: Z[H]^d -> Z[H]^d` is a homomorphism of free left `Z[H]`-modules. By
   `strebel-class-dz-is-locally-indicable` it is injective, since `H` is locally indicable.
   - If `xi in Q[H]^d` and `xi D = 0`, pick `m >= 1` with `m xi in Z[H]^d`.
   - Then `(m xi) D = 0`, so `m xi = 0`, so `xi = 0`.
3. **Support reduction.** Lemma 1 of `torus-degree-regular-on-prime-power-residual-support`
   (route step 2 there) extends injectivity from `Q[H]^d` to `Q[G]^d`.
4. **Onto.** `torus-automata-with-regular-degree-are-surjective` gives that `tau` is onto.
5. **Invertible degree.**
   - `tau` is a continuous equivariant bijection of a compact Hausdorff space, hence a
     homeomorphism.
   - `tau^{-1}` is continuous and equivariant, so it has a degree matrix `D(tau^{-1})`.
   - By functoriality of `H^1`, `D(tau^{-1}) D(tau) = D(tau) D(tau^{-1}) = I`.
   - So `D(tau) in GL_d(Z[G])` whenever `H` is locally indicable. This step needs no further
     hypothesis on `G`.
6. **BS(2,3).** The following are recalled standard facts, used only to name the new host:
   - Torsion-free one-relator groups are locally indicable (Brodskii; Howie).
   - `BS(2,3)` is non-Hopfian, so it is not residually finite (Malcev).

**Independent second route for step 2 (not required).** Item 1(ii) of
`flat-weak-bass-holds-exactly-for-locally-indicable-groups`, which is proposed and pending
referee, gives `rk_U(D) >= rank_Q epsilon(D) = d`. `U(H)` is von Neumann regular and `dim_U` is
faithful on f.g. projectives, so the kernel of `r_D` on `U(H)^d` is zero.

**Check.** Part C of `experiments/torus-fox-witness-2026-09-17/check_fox_witness.py` shows that
the Fox witness of `fox-witness-kills-augmentation-torus-degree-proofs` does not exist on
`BS(2,3)`: its exponent-sum lattice has rank 1 < 2. This is consistent with step 2.
