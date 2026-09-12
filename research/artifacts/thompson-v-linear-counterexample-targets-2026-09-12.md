# Linear counterexample targets over Thompson's V

Lane `gk-n-thompson-v`, 2026-09-12. Supports the claims `thompson-v-nonsurjunctive`,
`thompson-v-modular-group-algebra-not-directly-finite` and
`thompson-v-ternary-swap-idempotent-is-full`, and the routes between them.

## 0. Summary

- `V` is the bottom of the tower `V <= R^x <= A^x` (`leavitt-surjunctivity-tower`). So a
  nonsurjunctive `V` is the strongest counterexample available in this graph. It refutes
  Gottschalk's conjecture over every group of the tower and makes `V` nonsofic. The graph
  had the positive root `thompson-v-surjunctive` and no negative one; it is now
  `thompson-v-nonsurjunctive`.
- The linear half: for some prime `p`, `F_p[V]` is not directly finite. Then
  `stable-finiteness-failure-refutes-surjunctivity` gives a strict linear automaton over `V`.
- A concrete target over `F_3`. `V` contains the first-letter swap `w`, and `e = 2(1+w)` is an
  idempotent of `F_3[V]`. If `c e b = 1` for some `b, c` in `F_3[V]`, then `F_3[V]` is not
  directly finite. Equivalently, some one-sided unit `a` of `F_3[V]` satisfies `w a = a`.
- Where witnesses and obstructions stand:
  - the Leavitt witnesses `b = s0+s1`, `c = 2(t0+t1)` of the ternary Leavitt targets are not
    in the image of `F_3[V]` (Section 3);
  - every finite-dimensional representation of `V` over any field is trivial, so
    representation ranks see only the augmentation, which is consistent (Section 4.1);
  - the identity-coefficient trace is consistent (Section 4.2);
  - the Cantor orbits carry no Følner sets, so no invariant density obstructs (Section 4.3);
  - soficity or `F_3`-linear soficity of `V` would make `F_3[V]` stably finite and kill the
    target (Section 5).

## 1. Conventions

`Omega = {0,1}^N`. An element of `V` is a pair of complete prefix codes `(a_1..a_k)`,
`(b_1..b_k)` acting by `a_i eta -> b_i eta`. For every field `k`, the map
`g -> sum_i S[b_i]T[a_i]` embeds `V` in `L_k(1,2)^x` (`leavitt-cylinder-swaps-generate-thompson-in-el`).

- The swap `w` has codes `(0, 1) -> (1, 0)`. In `L_k(1,2)` it is `s0 t1 + s1 t0`, and `w^2 = 1`.
- The element `h` with codes `(00, 01, 1) -> (01, 1, 00)` has order 3.

## 2. Idempotents and the fullness step

**Proposition 2.1.**
- In `F_3[V]`, `e = 2(1+w)` is an idempotent different from `0` and `1`.
- In `F_2[V]`, `e_h = 1 + h + h^2` is an idempotent different from `0` and `1`.

*Proof.*
- `w^2 = 1` gives `e^2 = 4(1 + 2w + w^2) = 4(2 + 2w) = 8(1+w) = 2(1+w) = e` mod 3.
- `h^3 = 1` gives `e_h^2 = 1 + h^2 + h^4 + 2(h + h^2 + h^3) = 1 + h + h^2` mod 2.
- `1, w` (and `1, h, h^2`) are distinct basis vectors of the group algebra, so neither
  idempotent is `0` or `1`. QED

**Proposition 2.2.** Let `S` be a unital ring, `e != 1` an idempotent, and `b, c` in `S` with
`c e b = 1`. Put `a = e b` and `d = c e`. Then `d a = 1` and `a d != 1`. So `S` is not
directly finite.

*Proof.*
- `d a = c e e b = c e b = 1`.
- `(1-e) a = (1-e) e b = 0`. If `a d = 1`, then `1 - e = (1-e) a d = 0`, a contradiction. QED

**Proposition 2.3.** For `e = 2(1+w)` in `S = F_3[V]`, the following are equivalent:
1. `c e b = 1` for some `b, c` in `S`;
2. some `a` in `S` has a left inverse and satisfies `w a = a`.

Every such `a` is a one-sided unit that is not a unit.

*Proof.*
- (1) => (2): take `a = e b` with left inverse `d = c e`. Since `w e = 2(w + w^2) = e`,
  `w a = a`.
- (2) => (1): if `d a = 1` and `w a = a`, then `e a = 2(1+w) a = 4a = a`, so `d e a = 1`.
- If `a` were a unit, `w a = a` would force `w = 1`. QED

The `F_2` analogue: `c e_h b = 1` in `F_2[V]` holds exactly when some left-invertible `a`
satisfies `h a = a`.

**Single permutation terms do not work.** `a = (1+w) g` with `g` in `V` has no left inverse.
If `d (1+w) g = 1`, then `d(1+w) = g^-1`. Multiplying by `1 - w` gives
`g^-1 (1-w) = d (1+w)(1-w) = 0`, so `w = 1`. A witness must be a genuine linear combination.

## 3. The Leavitt witnesses are not in `F_3[V]`

Let `M` be the `F_3`-vector space with basis `delta_x`, `x` in `Omega`, with

```text
s_i delta_x = delta_(ix),        t_i delta_(jx) = delta_(ij) delta_x.
```

- These operators satisfy `t_i s_j = delta_(ij)` and `s0 t0 + s1 t1 = 1`, so `M` is a left
  `L_(F_3)(1,2)`-module.
- An element of `V` permutes the basis vectors.

**Lemma 3.1.** Let `X = sum_g lambda_g g` in `F_3[V]` act on `M`. Then every column sum
`sum_y X_(y,x)` and every row sum `sum_x X_(y,x)` equals `sum_g lambda_g`.

*Proof.* A permutation matrix has exactly one entry `1` in each row and in each column, and
the sums are finite. QED

**Corollary 3.2.** Neither `s0 + s1` nor `2(t0 + t1)` lies in the image of `F_3[V]` in
`L_(F_3)(1,2)`.

*Proof.*
- `s0 + s1` sends `delta_x` to `delta_(0x) + delta_(1x)`: column sums `2`, row sums `1`.
- `2(t0 + t1)` sends `delta_(jx)` to `2 delta_x`: column sums `2`, row sums `4 = 1`.
- By Lemma 3.1 an element of the image has equal row and column sums. QED

So the solution of `c e b = 1` that `ternary-anti-invariant-swap-corner-is-full` starts from
does not restrict to `V`. The Leavitt witness doubles mass (`x -> 0x + 1x`). A V-internal
witness must be built from combinations of prefix permutations, whose row and column sums
balance.

## 4. Obstructions that say nothing

**4.1 Finite-dimensional representations.**
- `V` is finitely generated, infinite and simple (`thompson-v-finitely-presented-infinite-simple`),
  and not residually finite (`thompson-v-not-lef`).
- A representation `V -> GL_n(k)` has a finitely generated linear image, which is residually
  finite by Mal'cev.
- By simplicity the representation is faithful or trivial, and a faithful one would make `V`
  residually finite. So it is trivial.

Every finite-dimensional representation of `F_3[V]` therefore factors through the
augmentation `epsilon`. There `epsilon(e) = 2(1+1) = 1`, and `c e b = 1` is consistent.

**4.2 The trace.**
- The identity coefficient `tau` is a trace on `F_3[V]`.
- With `a = eb` and `d = ce`: `ad` is an idempotent below `e`, `tau(ad) = tau(da) = 1` and
  `tau(e) = 2`.
- So the idempotent `e - ad` has `tau(e - ad) = 1`. This is consistent, and Zalesskii's theorem
  (traces of idempotents lie in the prime field) adds nothing.

**4.3 Densities.** A counting obstruction would need an invariant density on the permutation
modules of the Cantor action. `thompson-v-cantor-orbits-have-no-folner-sets` rules those out.

## 5. The gate

- If `V` is sofic, `F_3[V]` is stably finite (Elek–Szabó), and the claims of this artifact are
  false. The same holds if `V` is `F_3`-linear sofic. Both are open.
- So the target sits exactly where `V` is not linear sofic over `F_3`.
- A proof would give the first non-linear-sofic group. It would also give a nonsofic group with
  the Haagerup property (`thompson-v-has-haagerup-property`), which no (T)-based mechanism can
  produce (`thompson-v-has-no-rigid-compression-defect`).

## 6. Relation to the other ternary targets

- `V <= G_3 = L_(F_3)(1,2)^x`, and the image meets the scalars only in `1`: a permutation of
  the basis of `M` is never `-1`. So `V <= PG`.
- A solution in `F_3[V]` solves `c e b = 1` in `F_3[G_3]` with the same `e`, and gives the
  larger-host claims. The converse fails a priori.
- The larger-host forms: `ternary-leavitt-swap-idempotent-is-full`,
  `ternary-anti-invariant-swap-corner-is-full`, `projective-ternary-klein-idempotent-is-full`.

## 7. Self-similar rewrites change nothing

**Proposition 7.1.** Let `(tau, sigma)` be a left-inverse rule pair over `V`, with encoder
memory `M`, decoder memory `S` and rules `mu`, `nu`.
1. Let `U` be a nonempty clopen and `phi : V -> V_U` an isomorphism. The rewritten pair, with
   memories `phi(M)`, `phi(S)` and the same rules, has the same forward and reverse tables, and
   it is strict exactly when `(tau, sigma)` is.
2. For pairs with memories inside `V_(U_1)`, `V_(U_2)` on disjoint clopens, the product pair
   over `A_1 x A_2` is strict exactly when a factor is.

*Proof.*
1. `phi` is injective, so `phi(s)phi(m) = phi(s')phi(m')` iff `sm = s'm'`, and likewise for
   `ms`. By `strict-automata-live-on-canonical-table-groups` the design and its tables decide
   strictness. Directly: the rewritten automaton is `tau` transported along `phi` to
   `V_U ~= V` and extended along the cosets of `V_U`, and that preserves injectivity and
   surjectivity in both directions.
2. The product map is `tau_1 x tau_2` on `A_1^V x A_2^V`, with left inverse
   `sigma_1 x sigma_2`. It is onto iff both factors are. QED

**Scope.** This excludes inductions whose steps are these rewrites: conjugating the memory into
a cylinder copy of `V`, and taking products over disjoint clopens. The rewrites keep the rules
and the tables, and the tables with the rules decide strictness. A descent proof of
`thompson-v-surjunctive` would need an operation that changes the rules or the tables.

## 8. How the two sides of the V question are wired

- `thompson-v-is-sofic` (open) feeds `thompson-v-surjunctive` through Gromov--Weiss. Through
  linear soficity it also feeds `thompson-v-modular-group-algebras-are-stably-finite`, which
  refutes the linear targets of Sections 2 and 3.
- `thompson-v-nonsurjunctive` (open) feeds `thompson-v-not-sofic` and, by ascent,
  `leavitt-unit-group-nonsurjunctive`.
- Every positive argument recorded for `V` goes through soficity. Every negative one proves `V`
  nonsofic. A decision of `thompson-v-surjunctive` that avoids soficity would need a mechanism
  that none of the landed tools provide: not permanence, coset peeling, Cantor encodings,
  self-similar rewrites, or (T)-compression.
