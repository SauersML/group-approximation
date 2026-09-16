# Binary three-address strict automata are linear

Lane `swarm-every-group-is-binary-surjunct`, 2026-09-16.

**Target.** `every-group-is-binary-surjunctive`, restricted to automata whose memory has at most three
elements.

**Result (Theorem 6.1).** Let `G` be any group and `tau : {0,1}^G -> {0,1}^G` an injective,
non-surjective cellular automaton whose memory has at most three elements. Then its minimal memory
`M = {m_0, m_1, m_2}` has exactly three elements, its rule is `x_0 + x_1 + x_2 + epsilon`, and
`<M m_0^-1>` is not sofic. Equivalently, `tau = L + epsilon` with
`L(x)(h) = x(h m_0) + x(h m_1) + x(h m_2)` an injective, non-surjective linear automaton over `F_2`.
So the three-address binary case of Gottschalk's conjecture is exactly the question of linear strict
automata over `F_2` with a memory of three elements. The converse direction is trivial, since such an
`L` is itself a binary automaton with three memory elements.

**Uses.** `three-address-binary-injective-rules-are-balanced` (balance, Section 2) and
`sofic-groups-are-surjunctive` (Gromov-Weiss, Fact 1.3). Nothing else from the graph.

## 0. Conventions

- `A = {0,1} = F_2`. For a finite `M = (m_0, ..., m_{k-1})` of distinct elements of `G` and a rule
  `mu : A^k -> A`, the automaton is `tau(x)(h) = mu(x(h m_0), ..., x(h m_{k-1}))`. It commutes with
  the left shifts `(g.x)(h) = x(g^-1 h)`.
- For three addresses, a pattern is written `(t_0, t_1, t_2)` and indexed `4 t_0 + 2 t_1 + t_2` in the
  scripts. `e_i` is the pattern with a single `1` at address `i`, and `0 = 000`, `1 = 111`.
- `delta_k` is the configuration equal to `1` exactly at `k in G`, and `1_S` is the indicator of
  `S ⊆ G`. Constant configurations are written `0` and `1`.
- A *strict* automaton is injective and not surjective.

## 1. Standard facts

**Fact 1.1 (right translation).** For `g in G` put `R_g(x)(h) = x(hg)`. `R_g` is a bijective
automaton with inverse `R_{g^-1}`. If `tau` has memory `M` and rule `mu`, then `tau = tau' o R_g`,
where `tau'` has memory `M g^-1` and the same rule, `tau'(y)(h) = mu(y(h m_0 g^-1), ...)`. Indeed
`tau'(R_g x)(h) = mu(x(h m_0 g^-1 g), ...) = tau(x)(h)`. So `tau` is injective, respectively
surjective, iff `tau'` is.

**Fact 1.2 (localization).** Suppose `M ⊆ H` for a subgroup `H`, and let `tau_H` be the automaton
over `H` with the same memory and rule.
- For `h` in a left coset `gH`, every `h m` lies in `gH`. So `tau(x)` restricted to `gH` depends only
  on `x` restricted to `gH`.
- Identify `A^{gH}` with `A^H` through `x_g(k) = x(gk)`. Then `tau(x)(gk) = tau_H(x_g)(k)`.
- So `A^G` is the product of the `A^{gH}` over the left cosets, and `tau` acts on it as the product
  of copies of `tau_H`. A product of copies of one map is injective, respectively surjective, iff
  that map is.

**Fact 1.3 (soficity).** Put `H_M = <M m^-1>` for any `m in M`. This subgroup does not depend on `m`,
since `M m'^-1 = (M m^-1)(m' m^-1)^-1` lies in `<M m^-1>`, and symmetrically.
- If `H_M` is sofic, then every injective `tau` with memory `M` is surjective.
- Proof. By Fact 1.1 with `g = m`, `tau = tau' o R_m` and `tau'` has memory `M m^-1 ⊆ H_M`. By
  Fact 1.2 `tau'` is injective iff `tau'_{H_M}` is, and surjective iff it is. Sofic groups are
  surjunctive (`sofic-groups-are-surjunctive`).
- In particular this applies when `H_M` is finite or cyclic, since those are amenable.

**Fact 1.4 (symmetries).** Let `c(x) = 1 - x`. Then `c o tau` has rule `1 - mu` and memory `M`. It
is injective, respectively surjective, iff `tau` is. Permuting the addresses of `M` does not change
the automaton. Removing an address on which `mu` does not depend does not change it either.

## 2. Reduction to seventeen rules

Let `tau` be strict with a memory of at most three elements. By Fact 1.4 we may pass to the minimal
memory, so `mu` depends on every address of `M` and `|M| <= 3`.

- **Balance.** By `three-address-binary-injective-rules-are-balanced`, `mu` is balanced:
  `|mu^-1(0)| = |mu^-1(1)|`.
- **Constant test.** `mu(0) != mu(1)`. Otherwise `tau(0) = tau(1)` with `0 != 1`.
- **`|M| = 0`.** `tau` is constant, hence not injective.
- **`|M| = 1`.** `mu(t) = t` or `1 - t`, so `tau = R_m` or `c o R_m`, which is bijective.
- **`|M| = 2`.** The six balanced functions of two bits are `x_0`, `x_1`, `x_0 + x_1` and their
  complements. Those depending on both bits are `x_0 + x_1 + epsilon`. They take equal values on
  `00` and `11`, so the constant test fails.
- **`|M| = 3`.** By Fact 1.4 (output complement), normalize to `mu(000) = 0` and `mu(111) = 1`. Then
  `mu` takes value `1` on exactly three of the six middle patterns.

**Hand classification.** Put `S_1 = {i : mu(e_i) = 1}` and `S_2 = {j : mu(1 - e_j) = 1}`, where
`1 - e_j` is the weight-two pattern missing address `j`. Then `|S_1| + |S_2| = 3`, which gives
`C(6,3) = 20` normalized balanced rules.

| `(#S_1, #S_2)` | rules | name | depends on all? | test |
|---|---|---|---|---|
| `(0, 3)` | 1 | majority | yes | Lemma T |
| `(3, 0)` | 1 | parity `x_0 + x_1 + x_2` | yes | survives |
| `(1, 2)`, `S_2 ∌ i` where `S_1 = {i}` | 3 | `x_i` | no | excluded |
| `(1, 2)`, `S_2 ∋ i` | 6 | multiplexer `x_b ? x_c : x_a` | yes | Lemma C |
| `(2, 1)`, `S_2 = {k}` where `S_1 = {0,1,2} - {k}` | 3 | selector `x_k ? AND : OR` | yes | Lemma F |
| `(2, 1)`, other `S_2` | 6 | `x_a + x_b (1 + x_c)` | yes | Lemma C |

So there are `20 - 3 = 17` normalized rules depending on all addresses.

**Checks of the table.**
- **`(1,2)` with `S_1 = {i}` and `S_2 = {j,k}`, `i` not in `S_2`.** Then `S_2 = {0,1,2} - {i}` and
  `mu = 1` on `e_i`, on `e_i + e_j`, on `e_i + e_k` and on `111`. That is `mu = x_i`.
- **`(2,1)` with `S_1 = {i,i'}` and `S_2 = {k}`, `k` the index not in `S_1`.**
  - `mu = 1` on `e_i`, `e_{i'}`, `e_i + e_{i'}` and `111`.
  - `mu = 0` on `000`, `e_k`, `e_k + e_i` and `e_k + e_{i'}`.
  - So `mu = x_i OR x_{i'}` when `x_k = 0`, and `mu = x_i AND x_{i'}` when `x_k = 1`.
- **Worked example.** `S_1 = {2}`, `S_2 = {1,2}` gives `mu = x_1 ? x_0 : x_2`, with ANF
  `x_2 + x_1 x_2 + x_0 x_1`.
- **Second worked example.** `S_1 = {1,2}`, `S_2 = {1}` gives `mu = x_2 + x_1 (1 + x_0)`.
- The script `three_address_classify.py` reproduces the counts `T1: 1, C: 12, A: 3, AFF: 1`.

**When Lemma C applies.** Lemma C needs an index `r` with `mu(e_r) = mu(1 - e_r)`.
- **Row `(1,2)` with `S_2 ∋ i`.** Take `r = i`. Then `i` lies in `S_1` and in `S_2`, so both values
  are `1`.
- **Row `(2,1)` with `S_2 = {j}` and `j != k`.** Take `r = j`. Then `j` lies in `S_1` and in `S_2`,
  so both values are `1`. Also `r = k` works, since `k` lies in neither set and both values are `0`.
- **Majority, parity and selector rules.** `mu(e_r) != mu(1 - e_r)` for every `r`.

## 3. Lemma T: majority

**Lemma 3.1.** Let `|M| = 3` and `mu(e_i) = mu(0)` for `i = 0, 1, 2`. Then `tau(delta_k) = tau(0)`
for every `k in G`, so `tau` is not injective.

*Proof.* Fix `h`. If `h m_i = k = h m_j` then `m_i = m_j`. So the pattern of `delta_k` at `h` has at
most one `1`, and `tau(delta_k)(h)` is `mu(0)` or some `mu(e_i)`, which equals `mu(0) = tau(0)(h)`.
QED.

Majority has `mu(e_i) = 0 = mu(0)`, so it is never injective.

## 4. Lemma C: coset backgrounds

**Lemma 4.1.** Let `|M| = 3` with `mu(000) = 0` and `mu(111) = 1`. Suppose `(p, q, r)` is an ordering
of `{0, 1, 2}` with `mu(e_r) = mu(e_p + e_q)`. Put `u = m_q m_p^-1`, `v = m_r m_p^-1` and `U = <u>`.
- If `v in U`, then `H_M = U` is cyclic, so an injective `tau` is surjective (Fact 1.3).
- If `v not in U`, then `tau` is not injective.

*Proof.*
- **Case `v in U`.** `M m_p^-1 = {1, u, v} ⊆ U`, and it contains `u`, so `H_M = U`.
- **Case `v not in U`.** Put `x = 1_{U m_p}`, so `x(g) = 1` iff `g m_p^-1 in U`. For `h in G`:
  - `x(h m_p) = 1` iff `h in U`;
  - `x(h m_q) = 1` iff `h u in U` iff `h in U`;
  - `x(h m_r) = 1` iff `h v in U`.
- **Patterns of `x`.**
  - If `h in U`, then `hv in U` would give `v in U`. So the pattern at `h` is `e_p + e_q`.
  - If `h not in U`, the pattern is `000` or `e_r`.
- **Value `0`.** If `mu(e_r) = mu(e_p + e_q) = 0`, every value is `0`. So `tau(x) = 0 = tau(0)`,
  while `x(m_p) = 1`.
- **Value `1`.** If `mu(e_r) = mu(e_p + e_q) = 1`, use `x' = 1 - x`. Its patterns are the complements:
  `e_r` on `U`, and `111` or `e_p + e_q` off `U`. So `tau(x') = 1 = tau(1)`, while `x'(m_p) = 0`.
QED.

**Corollary 4.2.** Each of the twelve multiplexer and `x_a + x_b (1 + x_c)` rules of Section 2 has an
index `r` with `mu(e_r) = mu(1 - e_r)`. With `{p, q}` the other two indices, `1 - e_r = e_p + e_q`,
so Lemma 4.1 applies. Hence no such `tau` is strict: either it is not injective, or `H_M` is cyclic.

## 5. Lemma F: selector flips

Let `mu = x_s ? (x_t AND x_u) : (x_t OR x_u)` with `{s, t, u} = {0, 1, 2}`. By Fact 1.1 with
`g = m_s`, `tau = tau' o R_{m_s}`, where `tau'` has memory `{1, a, b}` with `a = m_t m_s^-1` and
`b = m_u m_s^-1`. Here `1, a, b` are distinct and

```text
tau'(y)(h) = y(h) ? (y(ha) AND y(hb)) : (y(ha) OR y(hb)).
```

**Lemma 5.1.** If `{1, a, b}` is not a subgroup of order three, then there is `y` with
`tau'(y) = tau'(y + delta_1)`. So `tau'` and `tau` are not injective. If `{1, a, b}` is a subgroup of
order three, then `H_M` is finite and an injective `tau` is surjective (Fact 1.3).

*Proof.* Let `y' = y + delta_1`. `tau'(y)(h)` reads `y` at `h`, `ha` and `hb`, so it can differ from
`tau'(y')(h)` only when `1 in {h, ha, hb}`, that is, for the three distinct readers
`h in {1, a^-1, b^-1}`. With `sigma` the selector bit, the local map is `s OR t` if `sigma = 0` and
`s AND t` if `sigma = 1`.
- **Reader `h = 1`.** The flip changes the selector. `s OR t = s AND t` iff `s = t`. So the reader is
  blind iff `y(a) = y(b)`.
- **Reader `h = a^-1`.** The pattern is `(y(a^-1), y(1), y(a^-1 b))`, and the flip changes the first
  data bit. `OR` ignores it iff the other data bit is `1`, and `AND` ignores it iff that bit is `0`.
  So the reader is blind iff `y(a^-1 b) != y(a^-1)`.
- **Reader `h = b^-1`.** Symmetrically, the reader is blind iff `y(b^-1 a) != y(b^-1)`.

None of the six sites `a, b, a^-1, a^-1 b, b^-1, b^-1 a` equals `1`, because `a != 1`, `b != 1` and
`a != b`. So we need `y` on `G - {1}` solving three linear equations over `F_2`, each on a pair of
distinct sites:

```text
(E1) y(a) + y(b) = 0          on P_1 = {a, b}
(E2) y(a^-1) + y(a^-1 b) = 1  on P_2 = {a^-1, a^-1 b}
(E3) y(b^-1) + y(b^-1 a) = 1  on P_3 = {b^-1, b^-1 a}
```

- **Solvability.** A system `y(p) + y(p') = c_e` on the edges of a multigraph is solvable iff the
  constants sum to `0` around every cycle. Three edges without loops form a cycle only as a doubled
  edge or as a triangle.
- **Triangle and `P_2 = P_3`.** A triangle sums to `0 + 1 + 1 = 0`. A doubled edge `P_2 = P_3` sums to
  `1 + 1 = 0`. Neither obstructs.
- **So the system fails only if `P_1 = P_2` or `P_1 = P_3`.**
  - `P_1 = P_2`: either `a = a^-1` and `b = a^-1 b`, forcing `a = 1`, impossible; or `a = a^-1 b` and
    `b = a^-1`, forcing `b = a^2 = a^-1`, so `a^3 = 1`.
  - `P_1 = P_3`: either `a = b^-1 a`, forcing `b = 1`, impossible; or `a = b^-1` and `b = b^-1 a`,
    forcing `a = b^2 = b^-1`, so `b^3 = 1`.
  - Both cases give `{1, a, b} = {1, a, a^2}`, a subgroup of order three.
- **Collision.** Otherwise pick a solution on the six sites, extend it arbitrarily to `G - {1}`, and
  set `y(1) = 0`. Then `tau'(y) = tau'(y')` with `y != y'`.
- **Subgroup case.** `M m_s^-1 = {1, a, a^2}`, so `H_M` has order three.
QED.

**Remark 5.2.** In the subgroup case the automaton does not reduce to the linear lane, but it cannot
be strict, because finite groups are surjunctive.

## 6. Conclusion

**Theorem 6.1.** Let `G` be a group and `tau` a strict automaton on `{0,1}^G` whose memory has at most
three elements. Then:
- the minimal memory `M = {m_0, m_1, m_2}` has three elements;
- the rule is `x_0 + x_1 + x_2 + epsilon` for some `epsilon in F_2`;
- `H_M = <M m_0^-1>` is not sofic.

Equivalently, `L = tau + epsilon`, `L(x)(h) = x(h m_0) + x(h m_1) + x(h m_2)`, is a strict linear
automaton over `F_2`, and `H_M` is not sofic.

*Proof.*
- **Seventeen rules.** By Section 2, `|M| = 3` and, after output complement, `mu` is one of the
  seventeen rules.
- **Majority.** Lemma 3.1 excludes it.
- **Twelve Lemma C rules.** Corollary 4.2 excludes them.
- **Three selector rules.** Lemma 5.1 excludes them.
- **Parity.** The only rule left is `x_0 + x_1 + x_2`, so before normalization
  `mu = x_0 + x_1 + x_2 + epsilon`.
- **Linear part.** `x -> x + epsilon` is a bijection of `A^G`, so `tau` is strict iff `L` is.
- **Non-soficity.** `H_M` is not sofic, by Fact 1.3.
QED.

**Converse.** If `L` above is strict, it is a strict binary automaton with three memory elements.

**Proposition 6.2 (group-ring form).** Put `gamma = m_0 + m_1 + m_2 in F_2[G]`. Then `L` is strict iff
`gamma` has a left inverse in `F_2[G]` but is not a unit. Equivalently `1 + a + b`, with
`a = m_1 m_0^-1` and `b = m_2 m_0^-1`, has a left inverse but is not a unit.

*Proof.* Let `F_2[G]` be the finitely supported functions. Pair `<x, beta> = sum_g x(g) beta(g)` for
`x in F_2^G`; this identifies `F_2^G` with the algebraic dual of `F_2[G]`.
- **Transpose.** `<L(x), beta> = sum_h sum_i x(h m_i) beta(h) = sum_g x(g) sum_i beta(g m_i^-1)`.
  So `L` is the dual map of `T(beta) = beta gamma`, right multiplication by `gamma`.
- **Duality.** For a linear map of vector spaces, the dual map is injective iff the map is
  surjective, and surjective iff the map is injective.
- **Injective `L`.** `L` is injective iff `T` is onto, which holds iff `1 in F_2[G] gamma`, i.e.
  `gamma` has a left inverse.
- **Surjective `L`.** `L` is surjective iff `T` is injective.
- **Unit case.** If `beta gamma = 1 = gamma beta`, then `T` is bijective.
- **Non-unit case.** If `beta gamma = 1 != gamma beta`, then `(1 - gamma beta) gamma = 0` with
  `1 - gamma beta != 0`, so `T` is not injective.
- **Translation.** `gamma = (1 + a + b) m_0` and `m_0` is a unit.
QED.

**Remark 6.3.** This is `linear-strict-pairs-are-transposes-of-post-surjective-automata` at memory
size three, specialized to `F_2`. It needs nothing beyond linear algebra.

**Corollary 6.4 (with the imported `dykema-heister-juschenko-bounded-rank-direct-finiteness`).**
- Kaplansky's direct finiteness holds over `F_2` for rank pairs `(3, n)` with `n <= 11`, symmetric
  in the two supports.
- So in any strict `tau` as in Theorem 6.1, every left inverse `beta` of `gamma` has
  `|supp beta| >= 12`.
- Dualizing `beta gamma = 1` gives `T_gamma T_beta = id` and hence `L_beta o L = id`. So `L` has a
  linear left inverse automaton with memory `supp beta`, and any such memory has at least twelve
  elements.
- This corollary is not part of the claim, and it rests on DHJ's computer enumeration.

**Consequence for the target.** A counterexample to `every-group-is-binary-surjunctive` with at most
three memory elements exists iff some group `G` and distinct `1, a, b in G` make `1 + a + b` have a
left inverse in `F_2[G]` without being a unit.
- The anti-involution `g -> g^-1` turns right inverses into left inverses. So this is the same as a
  support-three one-sided unit of `F_2[G]` that is not a unit.
- That is the support-three case of Kaplansky's direct finiteness over `F_2`, which is open in
  general.

## 7. Computational cross-checks

These are evidence only. Finite groups are surjunctive, so they cannot exhibit strictness, but they do
test the combinatorics of Sections 2 to 5. Scripts are in
`experiments/every-group-is-binary-surjunctive-2026-09-16/`. They are python3, single-threaded, and
each run is capped with `timeout 600`.

- **`three_address_classify.py` (group-free).** It enumerates normalized balanced rules depending on
  all three addresses. Output: `total 17 {'T1': 1, 'C': 12, 'A': 3, 'AFF': 1}`. The three `A` rules
  are the selector rules `00101011` (selector 2), `01001101` (selector 1) and `01110001` (selector 0).
- **`finite_group_checks.py GROUP ...`.** For every ordered triple of distinct elements and each of the
  seventeen rules, it checks three things.
  - *Lemma C directly.* For every applicable `(p, q, r)` with `v not in U`, `tau(1_{U m_p}) = tau(0)`,
    or `tau(1 - 1_{U m_p}) = tau(1)`, according to the value condition.
  - *Lemma F criterion.* For the selector rules, a blind flip at the identity exists iff `M` is not a
    right coset of an order-three subgroup. This is brute force over the sites `e M^-1 M`.
  - *Full injectivity (small groups only).* Over all `2^|G|` configurations: injective majority never
    occurs; an injective selector rule has `M` a right coset of order three; an injective Lemma C rule
    has `v in U` for every applicable triple.
- **Results** (runs of 2026-09-16). No failure line was printed for any group that ran to completion.
  In each row, `inj` counts the pairs (ordered triple, rule) whose automaton is injective, and
  `triples` counts the ordered triples of distinct elements.
  - *Full check, 0 failures.* `Z2` (no triples); `Z3` (inj 90, triples 6); `Z4` (24, 24); `Z5`
    (300, 60); `Z6` (252, 120); `Z2xZ2` (24, 24); `D3` (180, 120); `Z7` (630, 210); `Z8`, `D4`,
    `Z2xZ4`, `Z2^3` and `Q8` (336, 336 each); `Z9` (1242, 504); `Z3xZ3` (1080, 504); `Z10` and `D5`
    (1200, 720 each); `Z11` (2310, 990); `Z12` (1296, 1320); `D6` (720, 1320); `A4` (2376, 1320);
    `Dic3` (720, 1320); `Z2xZ6` (1296, 1320).
  - *Lemma C and flip checks only, 0 failures.* `S4` (12144 triples), `D8` (3360) and `Z3 x S3`
    (4896).
  - *Not completed.* The `A5` run was stopped at the 600 s cap.
  - *Batching.* `Z12`, `D6` and `A4` ran in one batch whose next member hit the cap before the final
    total was printed. Output is flushed at each group's statistics line, and any failure line for a
    group is printed before that line. None appeared. `Dic3` and `Z2xZ6` were rerun alone.
  - *Sanity reading.* On `Z3` each triple is all of `G`, and fifteen of the seventeen rules are
    injective. Majority (Lemma 3.1) and parity, whose output is constant in `h` there, are the two
    exceptions. This matches Corollary 4.2 (with `U = G`) and Lemma 5.1 (with `M` a subgroup of
    order three).

## 8. Boundary

- **Not closed: the linear remainder.** Theorem 6.1 does not decide support-three direct finiteness
  over `F_2`. Constant and coset backgrounds do not detect parity rules.
  - For `L'(y)(h) = y(h) + y(ha) + y(hb)`, one has `L'(1_H) = 1_H` for every subgroup `H` containing
    `a` and `b`.
  - `L'(delta_k)` has weight three.
- **Not closed: four or more addresses.** The tests used here rely on `|M| = 3`.
  - The single-flip Lemma 3.1 uses only distinctness of the addresses. So it extends verbatim to any
    rule that is blind to single flips on a constant background.
  - The coset background of Lemma 4.1 works because, once `v not in U`, the pattern is determined by
    membership `h in U`. With four addresses there are two outside addresses. Their joint coset
    membership varies with `h`, and failure of the test no longer makes `H_M` cyclic.
  - The flip system of Lemma 5.1 becomes a larger system over `F_2`, possibly with non-linear
    blindness conditions. It was not analyzed here, and nothing shown here confines its obstructions
    to finite `H_M`.
- **Balance import.** The reduction to seventeen rules uses
  `three-address-binary-injective-rules-are-balanced`, which is established in the graph by two
  independent routes. Without it, one would also have to exclude unbalanced three-address rules, and
  that is exactly what that claim does.
