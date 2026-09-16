---
rg: 2
id: stw63-distinct-z-cu-maps-need-perforation-witness
kind: claim
title: Unit-fixing Cu maps out of Cu(Z) can differ only through a rational unit-interval perforation witness
distinct_from:
  stw63-strict-comparison-sr1-uniqueness: that claim uses normalized 2-quasitraces and strict comparison in a stable-rank-one target to return approximate unitary equivalence; this claim is order-theoretic in an arbitrary Cu-semigroup, uses no quasitraces, stable rank or simplicity, and characterizes exactly when the two Cu maps differ.
  stw64-z-maps-avoid-supersoft-classes: that claim compares one Jiang--Su map with the canonical supersoft family in a simple positive-radius target; this claim compares two genuine maps with each other in any Cu-semigroup.
---

Write the Jiang--Su Cuntz semigroup as `Cu(Z) = N disjointUnion (0,infinity]`,
with compact classes `e_n = n[1_Z]` and soft classes `sigma_t`. A generalized
Cu-morphism is an additive, order-preserving map that sends `0` to `0` and
preserves suprema of increasing sequences.

Let `S` be a Cu-semigroup, and let `f,f':Cu(Z)->S` be generalized
Cu-morphisms with `f(e_1)=f'(e_1)`. Then:

1. **Eventual domination.** For real numbers `0<t<s<infinity` and every
   integer `m>=(1+t)/(s-t)`,

   ```text
   (m+1) f(sigma_t) <= m f'(sigma_s)   and   (m+1) f'(sigma_t) <= m f(sigma_s).
   ```

2. **Localization.** `f != f'` if and only if there are rational numbers
   `0<t<s<=1` with `f(sigma_t)` not below `f'(sigma_s)`, or with
   `f'(sigma_t)` not below `f(sigma_s)`.

3. **Perforation obstruction.** Suppose `S` has the following property.
   Whenever `x,y` in `S` satisfy `(m+1)x<=my` for all sufficiently large
   integers `m`, then `x<=y`. Then `f=f'`. In particular this holds when `S`
   is almost unperforated, meaning that `(k+1)x<=ky` for one `k` implies
   `x<=y`. That special case is already Antoine--Perera--Thiel,
   arXiv:1410.0483v3, Proposition 7.3.10 (uniqueness of a generalized
   Cu-morphism `Cu(Z)->S` with prescribed image of `1`, for almost
   unperforated `S`).

For a unital C-star algebra `B` and unital *-homomorphisms `phi,psi:Z->B`,
both `Cu(phi)` and `Cu(psi)` send `e_1` to `[1_B]`. Hence any witness for
`stw63-distinct-cu-maps-counterexample` has a Cuntz semigroup that is not
almost unperforated. The perforation is witnessed by a pair of the specific
form `x=Cu(phi)(sigma_t)`, `y=Cu(psi)(sigma_s)`, or the same pair with `phi`
and `psi` interchanged. Here `t<s` are rationals in `(0,1]`, `x` is not
below `y`, and `(m+1)x<=my` for every `m>=(1+t)/(s-t)`.

The non-almost-unperforated conclusion itself already follows from APT
Proposition 7.3.10. The additions here are parts 1 and 2 in an arbitrary
Cu-semigroup, the weaker hypothesis in part 3, and the rational unit-interval
form of the witness.

This claim does not assert that such a pair exists in any algebra. It also
asserts nothing about existence of Cu-morphisms out of `Cu(Z)`.
