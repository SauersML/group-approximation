---
rg: 2
id: torsor-cfi-isomorphism-algebra-is-coset-constraint-algebra-proof
kind: route
title: Read each context block of a colour-preserving magic unitary as one PVM indexed by left shifts
target: torsor-cfi-isomorphism-algebra-is-coset-constraint-algebra
requires: []
artifacts:
  - research/artifacts/ex-kac-quantum-compiler-torsor-cfi-2026-09-13.md
---

The complete proof is §2 of the artifact.  Outline, with every step checkable
from the relations.

1. **Blocks.**  `v_((k,alpha),(l,beta)) = v^2` is killed by the differing
   vertex colours when `k != l`.  So `V` is block diagonal.
2. **Shift dependence.**
   - Put `g = beta alpha^(-1)` and let `alpha'` be any vertex of block `k`.
   - Multiply `u_(alpha,beta)` by row `alpha'`.  Colour agreement allows only
     `beta' = g alpha'`.
   - So `u_(alpha,beta) = 0` unless `g alpha' in R'_k`, and otherwise
     `u_(alpha,beta) <= u_(alpha', g alpha')`.
   - By squareness and symmetry, `g R_k = R'_k` and all `u_(alpha, g alpha)`
     are one projection `p^k_g`.
3. **Relations.**
   - Rows give `sum_(g in T_k) p^k_g = 1`.
   - Across contexts, colour agreement of
     `(alpha_i^(-1) alpha'_i)` with `((g alpha)_i^(-1) (g' alpha')_i)` is
     `g_i = g'_i` on shared variables.
4. **Converse.**  Define `V` from the `p^k_g`.
   - Columns sum to one, because `alpha |-> beta alpha^(-1)` is a bijection
     onto `T_k`.
   - Distinct colours give distinct shifts in one PVM, or disagreeing
     restrictions.
   - The maps are mutually inverse on generators.
5. **Cosets.**  `g R_k = R'_k = h_k R_k` gives `h_k^(-1) g in Stab(R_k)`.
6. **Coproduct.**  In `Delta(v_(xz)) = sum_y v_(xy) (x) v_(yz)` with
   `x = (k,alpha_0)`, `z = (k, g alpha_0)` and `y = (k, h alpha_0)`, the two
   factors are `p^k_h` and `p^k_(g h^(-1))`.
7. **Not a group dual.**
   - The span of `{p^k_g}` is a commutative finite-dimensional Hopf
     *-subalgebra, with antipode `p^k_g |-> p^k_(g^(-1))`.  So it is `C(Λ)`.
   - Its characters are the evaluations at `g in L_k`, and convolution gives
     `ev_g * ev_(g') = ev_(g' g)`.  So `Λ ≅ L_k^op`.
   - A nonabelian `L_k` makes this Hopf subalgebra non-cocommutative.
   - Hopf subalgebras of a group algebra are cocommutative.

**Credit.**  Roberson--Schmidt, arXiv:2111.12362v1, read at source:
- Definition 3.2 gives the `F_2` graphs;
- Lemma 3.6 is step 2 over `F_2`;
- Theorems 3.8 and 6.7 are the `F_2` case of the theorem.
