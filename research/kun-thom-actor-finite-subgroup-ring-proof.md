---
rg: 2
id: kun-thom-actor-finite-subgroup-ring-proof
kind: route
title: Bound prime element orders by Minkowski in SL_d(Z) and by eigenvalue degrees over a regular function field
target: kun-thom-actor-finite-subgroup-ring-has-finitely-many-primes
requires: []
---

Notation: `E = EL_r(R)`, `pi : G -> SL_d(Z)` the quotient with kernel `E`, and
`K = F_q(x_1, ..., x_d)`, the fraction field of `R`.

1. **Reduction to prime-order elements.** By Cauchy's theorem, a prime `l`
   divides `|H|` for a finite `H <= G` iff `H` contains an element of order
   `l`. So it suffices to show that every element of prime order `l` in `G`
   has `l` in `P(q,r,d)`.

2. **The case `pi(g) != 1`.** Then `pi(g)` has order `l` in `SL_d(Z)`. Its
   minimal polynomial over `Q` divides `t^l - 1` and is not `t - 1`, so it is
   divisible by the `l`-th cyclotomic polynomial, which has degree `l - 1`.
   That polynomial divides the characteristic polynomial, of degree `d`, so
   `l - 1 <= d` and `l <= d + 1`.

3. **The case `pi(g) = 1`, so `g` lies in `E`, inside `GL_r(K)`.**
   - If `l = p`, then `l` lies in `P`.
   - Otherwise `l` is prime to the characteristic, so `g` is diagonalizable
     over an algebraic closure of `K`, and it has a primitive `l`-th root of
     unity `zeta` as an eigenvalue.
   - `zeta` is algebraic over `F_q`. `K` is purely transcendental over `F_q`,
     hence regular, hence linearly disjoint over `F_q` from `F_q(zeta)`. So
     `[K(zeta) : K] = [F_q(zeta) : F_q]`.
   - `zeta` is a root of the characteristic polynomial of `g`, which lies in
     `K[t]` and has degree `r`. So `[K(zeta) : K] <= r`.
   - Therefore `zeta` lies in `F_(q^k)` for some `k <= r`, and `l` divides
     `q^k - 1`.

4. **Conclusion.** Every prime dividing the order of a finite subgroup lies in
   `P(q,r,d)`, so `Lambda^G` is contained in `Z[1/l : l in P(q,r,d)]`. That set
   is finite, so the ring is a proper subring of `Q`. QED
