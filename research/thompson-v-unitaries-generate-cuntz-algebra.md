---
rg: 2
id: thompson-v-unitaries-generate-cuntz-algebra
kind: claim
title: The prefix-replacement unitaries of Thompson's V generate the whole Cuntz algebra O_2, and they do so in every representation of O_2
distinct_from:
  cuntz-groupoid-admits-no-folner-sequence: that is a groupoid Folner statement and gives only the absence of an invariant mean on orbits; this is the exact equality C*(V) = O_2 inside O_2, so the C*-algebra of every O_2-factoring representation of V is properly infinite.
  properly-infinite-cstar-quotient-is-compatible-with-fp-mf-group: that shows an MF free group can have O_2 as a C*-quotient, so a properly infinite quotient alone never refutes MF; this computes the C*-algebra of V's own prefix-replacement unitaries, and is used only against models that factor through it.
---

**ESTABLISHED (written proof; not Lean-verified).**

Let `s_0, s_1` be the Cuntz generators of `O_2`, with `s_i^* s_j = delta_ij` and
`s_0 s_0^* + s_1 s_1^* = 1`. For a word `w = w_1...w_k` put `s_w = s_{w_1}...s_{w_k}`
(`s_empty = 1`). An element `g` of Thompson's group `V` is given by two complete
prefix codes `(p_1,...,p_n)` and `(q_1,...,q_n)` with `g(p_i x) = q_i x`. Put

```text
u_g = sum_i s_{q_i} s_{p_i}^*  in U(O_2).
```

Let `B = C*(u_g : g in V)`, the C*-subalgebra of `O_2` these unitaries generate.

**Claim.** `B = O_2`.

**Consequences, all immediate.**

- For every unital *-homomorphism `theta : O_2 -> C` into any unital C*-algebra, the
  unitaries `theta(u_g)` generate `theta(O_2)`. When `C != 0` this algebra contains
  the isometry `theta(s_0)`, whose range projection is `1 - theta(s_1)theta(s_1)^*`,
  and that is not `1`. So `C*(theta(u_V))` is infinite. It is not stably finite,
  not MF and not quasidiagonal.
- The following representations of `V` all have this form, so each of them
  generates a copy of an infinite quotient of `O_2`:
  - the permutation representation of `V` on `l^2` of any orbit of the Cantor set, which is
    the quasi-regular representation `lambda_{V/V_xi}`;
  - the Radon--Nikodym-twisted Koopman representation on `L^2` of the uniform Bernoulli
    measure;
  - the Fock, or tree, near-permutation representation modulo compacts. It is described in
    `cuntz-calkin-lifts-of-thompson-v-have-no-compression`.
- The proof uses only transpositions of two cones and the prefix-replacement maps.
  It is written for `d = 2`, and the same computation is expected to give
  `C*(V_{d,1}) = O_d` for the Higman--Thompson groups. That extension is not
  claimed here.

Proof: `thompson-v-unitaries-generate-cuntz-algebra-proof`.
