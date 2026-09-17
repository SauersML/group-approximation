---
rg: 2
id: cyclic-germ-brown-complexes-proof
kind: route
title: Infinite edge stabilizers make cyclic vertex stabilizers commensurable, and the near index turns commensuration of tau into a central shift power
target: cyclic-germ-brown-complexes-force-virtually-cyclic-shell-input
requires:
  - shell-prefix-core-detects-finite-ray-enumerations
  - shell-cantor-embeddings-are-finite-germ-extensions
artifacts:
  - research/artifacts/shell-germ-brown-complexes-2026-09-17.md
---

The full proofs are in the artifact, Sections 0 to 2.

1. **Rigid form near p.** Every element of A_1 acts near p by a rigid cone map
   0^n 1 z -> 0^(pi(n)) 1 z, where pi represents its germ. This holds for the generators (prefix
   maps of Fix_V(p), and hat(g)), and so for their products.
2. **K is not finitely generated.** K = ker d is the increasing union of the groups
   V(C_0 u ... u C_(m-1)). A finitely generated subgroup lies in one stage, which misses V(C_m).
   Finite extensions of K are therefore not finitely generated either.
3. **Coarse orbit condition.**
   - Let F be a finite generating set of A(H). Take O to be the closure of a finite initial set
     under the rigid maps of F.
   - Every word in F is rigid on C_n for n outside O.
   - Nonidentity elements of V(C_n) <= K <= A(H) are not rigid there.
   - So O = N.
4. **Obstruction.**
   - An infinite edge stabilizer has finite index in the virtually cyclic stabilizers of its
     endpoints. By connectivity, all vertex stabilizers are commensurable.
   - Q therefore commensurates a vertex stabilizer Q_(v0) containing tau^m, hence commensurates
     <tau>.
   - q tau^a q^-1 = tau^b with a, b != 0 forces a = b, because the near index is a conjugation
     invariant homomorphism with eta(tau) = 1.
   - Taking the lcm over the finite generating set rho(S) u {tau} makes tau^a central.
   - `shell-prefix-core-detects-finite-ray-enumerations` (clause 2) then forces P to be
     virtually cyclic.
