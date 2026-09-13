---
rg: 2
id: simple-group-classical-width-finite-field-linear-soficity
kind: claim
title: A finitely presented simple group not linear sofic over finite fields has bounded relator width over all symplectic, unitary and orthogonal groups
distinct_from:
  simple-group-psl-width-is-finite-field-linear-soficity: that proves the special linear family and the converse; this is the symplectic, unitary and orthogonal families, which need class-size bounds from the fixed space and a commutator choice inside the isometry group.
  non-linear-sofic-simple-groups-bounded-width-in-classical-groups: that is the fixed-field statement for all four families with a field-dependent constant; this proves the three isometry families with a constant uniform in the rank and in the field.
  simple-group-relator-width-in-finite-simple-targets: that covers bounded rank, sporadic, symmetric and alternating targets; this covers unbounded rank isometry groups.
---

**ESTABLISHED (reviewed: PASS in `research/artifacts/ex-review-backlog-2026-09-13-part7.md` §27.1 and `research/artifacts/ex-review2-groups-2026-09-13-part2.md` §§1--5).** Let `G = <X | R>` be an infinite finitely presented simple group that is
not linear sofic over finite fields (definition on `simple-group-psl-width-is-finite-field-linear-soficity`).
Then there is `K = K(G)` with `w_Q(a) <= K` for every `a in Q^X` and every `Q = Q_0/Z_0`, where:
- `Q_0` is `Sp_n(q)`, `SU_n(q)` or `Omega^+-_n(q)` (for odd `n` the single type `Omega_n(q)`, `q` odd; case (O) of part 1 covers both parities), for any `n` and `q` such that `Q_0/Z(Q_0)` is a
  nonabelian simple group;
- `Z_0` is central.

With "not `F_p`-linear sofic" in place of the hypothesis, the same holds uniformly over all `q = p^e`.
No soficity hypothesis beyond this is used.

**Converse: not proved here.** Whether linear soficity over finite fields forces unbounded width over
each isometry family separately is not written. The equivalence over all finite simple groups does not
need it, because the special linear converse already gives unbounded width over `PSL_n(q)`.

**Payoff.** With `simple-group-psl-width-is-finite-field-linear-soficity` and
`simple-group-relator-width-in-finite-simple-targets`, the relator width of a finitely presented simple
group is bounded over all finite simple groups iff the group is not linear sofic over finite fields
(`simple-group-width-over-all-finite-simple-groups`).

**Mechanism.**
- **Double commutator template.** `G = G''`, so it suffices to cover commutators of elements of
  `I(W)'`. Scalars cancel, and no determinant or spinor-norm corrections arise.
- **Class sizes.** An isometry `k` with `s = rk(k - 1) <= n/4` has `|k^(Q_0)| >= q^(sn/2 - 3n - 4)/4`.
  The proof counts stabilizers of the fixed space against a big-cell lower bound for `|Q_0|`
  (part 1, elementary).
- **Seeds.**
  - *Proportional case.* For a relator `h` with `rho(h) >= eta n`, a greedy hyperbolic subspace `Y` with
    `dim(Y + hY) >= (3/2) dim Y` and a Levi companion matrix `y` give `[h, y]` of support between
    `r'` and `4r'`.
  - *Near-central case.* The tuple is localized in `I(W) x 1`. The displacement is the product of two
    conjugate swap involutions, so it lies in `I(V)'`, and it makes `[r(a), y]` of rank `2t` inside
    `I(W''')`.
- **Covering.** Liebeck--Shalev covers in boundedly many steps. Bounded local dimension is handled by
  minimal degrees.

Derivation: `simple-group-classical-width-finite-field-linear-soficity-proof`.
