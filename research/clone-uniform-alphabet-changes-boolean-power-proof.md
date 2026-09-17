---
rg: 2
id: clone-uniform-alphabet-changes-boolean-power-proof
kind: route
title: Read an element through its characteristic Boolean coordinates and rebuild it by nested if-then-else
target: clone-uniform-alphabet-changes-reach-only-boolean-powers
requires: []
---

This is a complete direct proof. Fix distinct `0, 1` in `A` and list `A = {a_1, ..., a_k}`.

**Operations on `A`.**
- `c_a(x) = a` (unary constant).
- `s(x) = 0` if `x = 0`, and `1` otherwise.
- `and(u, v) = 1` if `u != 0` and `v != 0`, and `0` otherwise.
- `not(u) = 1` if `u = 0`, and `0` otherwise.
- `chi_a(x) = 1` if `x = a`, and `0` otherwise.
- `t(u, x, y) = x` if `u != 0`, and `y` if `u = 0`.

Write `or(u, v) := not(and(not u, not v))`, and
`R(u_1, ..., u_{k-1}) := t(u_1, c_{a_1}(u_1), t(u_2, c_{a_2}(u_1), ..., t(u_{k-1}, c_{a_{k-1}}(u_1), c_{a_k}(u_1))...))`.

**Identities, each checked in `A` by cases.**
- **(E1)** `c_a(x) = c_a(y)` for every `a`.
- **(E2)** `s(s(u)) = s(u)`, `s(and(u, v)) = and(u, v)`, `s(not u) = not u`, `s(chi_a(x)) = chi_a(x)`,
  `s(c_0(u)) = c_0(u)`, `s(c_1(u)) = c_1(u)`. In addition, every axiom of a finite equational axiomatization of
  Boolean algebras in `and`, `not` (with `0 := c_0`, `1 := c_1`) holds with its variables replaced by `s(u)`,
  `s(v)`, `s(w)`. This is true in `A` because `s` takes values in `{0, 1}`, where `and` and `not` are the
  Boolean operations and `c_0`, `c_1` are the bottom and top.
- **(E3)** `and(chi_a(x), chi_b(x)) = c_0(x)` for `a != b`, and `or(chi_{a_1}(x), or(..., chi_{a_k}(x))) = c_1(x)`.
- **(E4)** `R(chi_{a_1}(x), ..., chi_{a_{k-1}}(x)) = x`. If `x = a_j` with `j < k`, the first nonzero argument is
  the `j`-th, so `R` returns `a_j`. If `x = a_k`, all arguments are `0` and `R` returns `a_k`.
- **(E5)** For `j < k`,
  `chi_{a_j}(R(s u_1, ..., s u_{k-1})) = and(not u_1, ..., not u_{j-1}, s u_j)`, and
  `chi_{a_k}(R(s u_1, ..., s u_{k-1})) = and(not u_1, ..., not u_{k-1})`.
  Here `R(s u)` returns `a_j` for the least `j` with `u_j != 0`, and `a_k` if there is none. The right-hand
  sides are the indicators of exactly these events.

**Proof in `M`.** Assume (E1)–(E5) hold in `M`.

1. **The Boolean part.** By (E1), `c_a^M` is a constant. Call its value `a_M`. Put `B = {m in M : s(m) = m}`.
   - By (E2), `s` maps `M` into `B`, and `and`, `not` map `B` into `B`.
   - The Boolean axioms instantiated at `s(u), s(v), s(w)` hold, and every element of `B` has the form `s(u)`.
     So `(B; and, not, 0_M, 1_M)` is a Boolean algebra.
   - `B` is finite, so it is the power set of its `r >= 0` atoms (`r = 0` is the one-element algebra).
2. **Partitions of unity.** Let `P` be the set of tuples `(e_a)_{a in A}` in `B^A` with `and(e_a, e_b) = 0_M` for
   `a != b` and `or_a e_a = 1_M`. In the power set of the atoms, such a tuple assigns each atom to exactly one
   label `a`, so `|P| = k^r`.
3. **The map.** Define `X: M -> B^A` by `X(m) = (chi_a(m))_a`.
   - By (E2) and (E3), `X` takes values in `P`.
   - By (E4), `m = R(chi_{a_1}(m), ..., chi_{a_{k-1}}(m))`, so `X` is injective.
4. **Surjectivity.** Given `e` in `P`, put `m = R(e_{a_1}, ..., e_{a_{k-1}})`. Every `e_a` satisfies
   `s(e_a) = e_a`, so (E5) with `u_i = e_{a_i}` gives two cases.
   - For `j < k`: `chi_{a_j}(m) = and(not e_{a_1}, ..., not e_{a_{j-1}}, e_{a_j}) = e_{a_j}`, since `e_{a_j}` is
     disjoint from each earlier `e_{a_i}`.
   - For `j = k`: `chi_{a_k}(m) = not(or_{i<k} e_{a_i}) = e_{a_k}`, the unique complement.

   So `X(m) = e`.
5. **Conclusion.** `|M| = |P| = k^r`.

**Corollary.** A clone homomorphism `Clo(A) -> Clo(M)` preserves projections and substitution. Every identity
(E1)–(E5) is an equality of two terms of the clone, and so it is preserved. So `|M| = k^r`. For `r >= 1`,
`k^r` has the same set of prime divisors as `k`, and it is a power of two iff `k` is. For `r = 0`, `|M| = 1`
and no automaton on `M^G` is strict.

No property of any group is used. Only the finitely many operations listed are transported.
