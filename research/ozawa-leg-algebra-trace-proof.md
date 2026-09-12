---
rg: 2
id: ozawa-leg-algebra-trace-proof
kind: route
title: Fixed points of non-scalar matrices on the projective plane kill the block characters
target: ozawa-leg-algebra-carries-non-amenable-trace
requires: []
---

1. **Fixed points.** A non-scalar `x ∈ GL_3(F_p)` fixes only the points of
   `P²(F_p)` lying on its eigenlines. Its eigenspaces for distinct eigenvalues are
   independent and each has dimension at most 2. So there are at most `p + 2`
   fixed points: one projective line plus one point, or three points.
2. **Non-scalar mod p.** Let `g ≠ 1` in `SL(3,Z)`, and suppose `g ≡ λ_p I (mod p)`
   for infinitely many `p`.
   - The off-diagonal entries are divisible by infinitely many primes, so they
     are 0.
   - The diagonal entries are pairwise congruent modulo infinitely many primes,
     so they are equal.
   - So `g = aI` with `a³ = 1`, i.e. `g = 1`.
   Hence `g` is non-scalar mod `p` for all large `p`.
3. **Block characters.** `ℓ²(P²(F_p))` is the permutation representation, whose
   character is the number of fixed points. Removing the constants subtracts 1,
   and the dimension is `p² + p`. So the normalized character is
   `tr_k(π_k(g)) = (fix_{p_k}(g) − 1)/(p_k² + p_k)`. By 1 and 2 this tends to 0
   for `g ≠ 1`.
4. **The limit trace.** `x ↦ tr_k(x_k)` is a tracial state on `D`. A weak\* cluster
   point `τ` is a tracial state with `τ(π(g)) = δ_{g,1}`.
5. **Non-injectivity.** `M = π_τ(D)''` is a finite von Neumann algebra with faithful
   normal trace `τ`. The unitaries `π_τ(π(g))` have trace `δ_{g,1}`, so they
   generate a von Neumann subalgebra isomorphic to `L(G)`, and there is a
   trace-preserving conditional expectation `M → L(G)`.
   - If `D` were nuclear, `M` would be injective (Choi--Effros, Connes), and so
     would `L(G)`.
   - Then `G` would be amenable, but `SL(3,Z)` is not.
   So `D` is not nuclear.
6. **Exactness.** Subalgebras of nuclear algebras are exact. So `D ⊂ C` with `C`
   nuclear forces `D` to be exact.
