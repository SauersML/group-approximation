---
rg: 2
id: bounded-multiplicity-kazhdan-sectors-defect-proof
kind: route
title: The block algebra is in the commutant, the kernel closure absorbs the compressor, and realizer sets are invariant under kernel conjugation
target: bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect
requires:
  - kazhdan-kernel-isotypic-sectors-extend-within-kernel-closure
  - kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient
  - hyperbolic-kazhdan-cover-of-leavitt-unit-group
  - binary-leavitt-unit-group-is-simple
  - leavitt-unit-group-finitely-presented
  - realized-relative-twists-embed-in-outer-twist-group
artifacts:
  - research/artifacts/rnorm-kazhdan-projection-sizes-2026-09-12.md
---

Notation as in the target. The full text is Section 2 of the artifact.

0. **Hypotheses.** `R^x` is finitely presented and infinite simple, so it has no
   nontrivial finite quotient. `N` is Kazhdan. By block invariance
   `D^N = D^G`, so `A` commutes with `sigma(G)`. So
   `kazhdan-kernel-isotypic-sectors-extend-within-kernel-closure` applies to the
   Koopman representation of `sigma` on `H`, with this `A`.
1. **Item 1.**
   - Invariance of `H_b` under `sigma(G)` is item 2 of the source claim together
     with `W_rho(G)`-invariance of each `E`.
   - On a finite sub-sum `S`, item 4 of the source claim puts `sigma(g)|_S` in the
     norm closure of `T . sigma(N)|_S`.
   - Indexing a net by pairs (finite sub-sum, `eps`) gives
     `lambda_alpha sigma(n_alpha) -> sigma(g)` strongly on `H_b`. For unitaries this
     is strong* convergence, since
     `||u_alpha^* xi - u^* xi||^2 = 2||xi||^2 - 2 Re <xi, u_alpha u^* xi>`.
2. **Realizer sets are invariant under kernel conjugation.** Let `n in N`,
   `x in R(q)`, `m in M_s` and `c in C_s`.
   - `sigma(n)^-1 x m c sigma(n) = x (x^-1 sigma(n)^-1 x) m sigma(n) c`, because
     `c` commutes with `sigma(Gamma_hat)`, which contains `sigma(N)`.
   - `x` normalizes `M_s`, so `x^-1 sigma(n)^-1 x` lies in `M_s`. So the product
     lies in `R(q)`.
   - `P_b` commutes with `sigma(N)`, since `sigma(n)|_(H_rho) = rho(n) (x) 1`
     preserves `V_rho (x) E`. So `P_b R(q) P_b` is invariant under conjugation by
     `T . sigma(N)|_(H_b)`.
   - Conjugating a fixed bounded operator along a strong* convergent net of
     unitaries converges strongly. So `S_b(q)` is invariant under conjugation by
     the strong closure of that group.
3. **Item 2.** Put `s = sigma(t)`.
   - `R(eps_t(q)) = s^-1 R(q) s` (`conjugation-invariant-sizes-miss-defect-proof`,
     step 1, via items 1 and 2 of `realized-relative-twists-embed-in-outer-twist-group`).
   - `s` commutes with `P_b`, so `P_b R(eps_t q) P_b = s^-1 P_b R(q) P_b s`.
   - By step 1, `s|_(H_b)` is in the strong closure of `T . sigma(N)|_(H_b)`, so
     step 2 gives `S_b(eps_t q) <= S_b(q)`.
   - The same argument with `s^-1`, applied to `R(eps_t q)`, gives the reverse
     inclusion.
4. **Item 3.** `sigma(z) in R([sigma(z)])` commutes with `P_b`, so
   `P_b R([sigma(z)]) P_b = sigma(z) P_b M_s C_s P_b`. By step 1 this lies in the
   strong closure of `T . sigma(N) P_b M_s C_s P_b = T . P_b R(1) P_b`, because
   `sigma(N) = M_s`. The reverse inclusion uses `sigma(z)^-1`.
   - On the cover, `Q = C_(R^x)(EL_alpha(R))`, and it lifts into `G` by
     `relative-defect-iff-surjective-compressor-endomorphisms`.
5. **Item 4.** Every ingredient listed in the target is built from `S_b`, from
   `sigma(G)|_(H_b)` and `sigma(N)|_(H_b)`, or from `A`. By steps 1–4 each ingredient
   is transported identically for `B` and `eps_t(B)`, and for host twists and the
   trivial group.
