---
rg: 2
id: gap-tables-first-appear-at-three-by-six-and-four-by-five-proof
kind: route
title: Free products of cyclic groups on two-row tables, a census at three by five, explicit Baumslag-Solitar tables at three by six and four by five, and padding
target: gap-tables-first-appear-at-three-by-six-and-four-by-five
requires:
  - strict-pairs-need-a-memory-with-five-elements
  - baumslag-solitar-gap-table-at-five-by-five
artifacts:
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/RESULTS.md
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/enumtables6.c
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/census_3x5.jsonl.gz
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/census_5x3.jsonl.gz
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/verify_gap36.g
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/gap_tables_3x6.jsonl
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/gap_tables_4x5.jsonl
---

Notation and definitions are those of `strict-pairs-need-a-memory-with-five-elements`:

- A forward table `T` of shape `|S| x |M|` is a rook-independent partition of `S x M`, with `1` in both memories.
- `P(T) = <x_a (a != 1) | x_s x_m = x_s' x_m' along the blocks of T>`, with `x_1 = 1`.
- `T` is *realizable* when some group `K` and distinct labels `S, M` in `K` give `T_f(K) = T` exactly.
- `T` is *resolved* when finite quotients of `P(T)` separate every pair of reverse cells `x_m x_s` that is distinct
  in `P(T)`, and a *gap table* when it is realizable but not resolved.

Throughout, `G = BS(2,3) = <a, t | t a^2 t^-1 = a^3>`, `u = t^-1 a t`, and `H = Z[1/6] x| Z` with `t` acting by
`3/2`. The map `rho: G -> H`, `a -> (1,0)`, `t -> (0,1)`, sends a word to `(x, i)`, where `i` is the `t`-exponent
sum and `x` is the sum of `+-(3/2)^j` over the `a`-letters, `j` the `t`-exponent sum of the prefix before the letter.

## 0. Two facts about BS(2,3)

These are Sections 1 and 4 of `baumslag-solitar-gap-table-at-five-by-five-proof`.

- **(F1)** `a u != u a` in `G`, by Britton's lemma: the commutator `a t^-1 a t a^-1 t^-1 a^-1 t` has no pinch.
- **(F2)** In every finite quotient of `G`, the images of `a` and `u` commute. Indeed `ord(alpha)` is coprime to `6`
  for `alpha` the image of `a`, so `tau <alpha> tau^-1 = <alpha^3> = <alpha>` and `tau^-1 alpha tau` lies in
  `<alpha>`.

## 1. Tables with a side of size at most two are resolved

By inversion (`g -> g^-1` sends a table of shape `p x q` to one of shape `q x p` with an isomorphic table group,
matching reverse cells), it is enough to treat `|S| <= 2`. If `|S| = 1` there are no relators and `P(T)` is free.

Let `S = {1, s}`. A block of `T` has at most one cell per row, so each nontrivial block is `{(1, m'), (s, m)}` with
`m != m'` and gives the relator `y_m' = x_s y_m`, where `y_c = x_c` for `c` in `M` and `y_1 = 1`. Each `m` lies in at
most one block through row `s` and at most one through row `1`. So `f(m) = m'` is a partial injection of `M`, and its
graph is a disjoint union of paths and cycles.

- Along a path `m_0 -> m_1 -> ... -> m_k`, the relators say `y_(m_i) = x_s^i y_(m_0)`. Eliminating `y_(m_1), ...,
  y_(m_k)` leaves no relator. If `1` lies on the path, the letter `y_(m_0)` is eliminated too, through `y_1 = 1`.
- Along a cycle of length `k`, elimination leaves one letter `y_(m_0)` and the relator `y_(m_0) = x_s^k y_(m_0)`,
  that is `x_s^k = 1`. If `1` lies on the cycle, take `m_0 = 1`: no letter remains, and the relator `x_s^k = 1`
  still does.

So `P(T) = <x_s | x_s^g> * F_r`, where `g` is the gcd of the cycle lengths (`g = 0` when there is no cycle, which
gives `Z`) and `r` counts the components that avoid `1`. A free product of residually finite groups is residually
finite. For finitely many distinct pairs, the intersection of the separating kernels has finite index, so one finite
quotient separates them all. So `T` is resolved, and it is not a gap table.

## 2. No gap table at shape 3x5 or 5x3

`enumtables6.c` generalizes the orderly enumerator of the `4x4` census to six labels per side. The difference
closure is the same, and it is also run on partial tables after each completed row. That pruning is sound: the
relations of a partial table are among those of every completion, and the blocks of cells already assigned never
change. In `full` mode (closure only at the leaves) and in `prune` mode, it reproduces the survivor lists at `3x3`,
`3x4` and `4x3`, and byte for byte the published `reps_4x4.txt` (21,252 survivors).

The survivors at `3x5` and `5x3` then go through the unchanged pipeline of the `4x4` census (`gapcensus.py`, `pass2.py`,
`pass3.py`). Every table ends as RESOLVED or NOTCLOSED, and `verify.py` replays every separation witness. The counts
are in `RESULTS.md`. The trust boundary is that of the `4x4` census:

- rejections rest on the difference closure, which holds in every group;
- NOTCLOSED verdicts and the reverse classes rest on sound Knuth-Bendix rewriting;
- separations are checked by the independent checker.

A NOTCLOSED table is not realizable, so it is not a gap table. A RESOLVED table is not a gap table by definition.
Rejected tables are NOTCLOSED or have a label collision, so they are not realizable. The enumeration covers every
table up to relabeling of `S minus 1` and `M minus 1`, and both notions are invariant under relabeling.

## 3. A gap table at 3x6

Take `S = {1, t, ta}` and `M = {1, a, a^-1, a^-2, a^-1 t^-1 a, a^-2 t^-1 a}`.

**Products.**

| `s \ m` | `1` | `a` | `a^-1` | `a^-2` | `a^-1 t^-1 a` | `a^-2 t^-1 a` |
|---|---|---|---|---|---|---|
| `1` | `1` | `a` | `a^-1` | `a^-2` | `a^-1 t^-1 a` | `a^-2 t^-1 a` |
| `t` | `t` | `ta` | `ta^-1` | `ta^-2` | `t a^-1 t^-1 a` | `t a^-2 t^-1 a = a^-2` |
| `ta` | `ta` | `ta^2` | `t` | `ta^-1` | `a` | `t a^-1 t^-1 a` |

The equality `t a^-2 t^-1 = a^-3` is the relator. So six coincidences hold:

```text
(1, a) = (ta, a^-1 t^-1 a),   (1, a^-2) = (t, a^-2 t^-1 a),   (t, 1) = (ta, a^-1),
(t, a) = (ta, 1),             (t, a^-1) = (ta, a^-2),         (t, a^-1 t^-1 a) = (ta, a^-2 t^-1 a).
```

**There are no others.** The images under `rho`:

- *`t`-exponent 0:* `1, a, a^-1, a^-2, a^-1 t^-1 a, a^-2 t^-1 a, t a^-1 t^-1 a` give `x = 0, 1, -1, -2, -1/3, -4/3,
  -1/2`.
- *`t`-exponent 1:* `t, ta, ta^-1, ta^-2, ta^2` give `x = 0, 3/2, -3/2, -3, 3`.

These twelve images are distinct, so the table has exactly `18 - 6 = 12` classes. The labels in `S` (column `1`) and
in `M` (row `1`) are distinct. So `T` is realized in `G`.

**P(T) is BS(2,3).** Write `X = x_t`, `Z = x_ta`, `Y = y_a`, and `y_2, ..., y_5` for the letters of `a^-1, a^-2,
a^-1 t^-1 a, a^-2 t^-1 a`. The relators are `Y = Z y_4`, `y_3 = X y_5`, `X = Z y_2`, `X Y = Z`, `X y_2 = Z y_3` and
`X y_4 = Z y_5`. Eliminate, in turn:

- `Z = X Y`, then `y_2 = Z^-1 X = Y^-1`;
- `y_3 = Z^-1 X y_2 = Y^-2`;
- `y_4 = Z^-1 Y = Y^-1 X^-1 Y`;
- `y_5 = Z^-1 X y_4 = Y^-2 X^-1 Y`.

The remaining relator `y_3 = X y_5` becomes `Y^-2 = X Y^-2 X^-1 Y`, that is `X Y^2 X^-1 = Y^3`. So
`P(T) = <X, Y | X Y^2 X^-1 = Y^3>`, and `x_c -> c` sends `X -> t` and `Y -> a`. It is the identity of `BS(2,3)` on
generators, so it is an isomorphism `phi: P(T) -> G`.

**The gap pair.** Take the reverse cells `(a^-1 t^-1 a, t)` and `(a^-2 t^-1 a, ta)`. Through `phi` their products are
`a^-1 u` and `a^-2 u a`. These are equal if and only if `a u = u a`. They are distinct by (F1) and merged in every
finite quotient by (F2). So `T` is a gap table of shape `3x6`.

## 4. A gap table at 4x5

Take `S = {1, a, t, u}` and `M = {1, a, t, u, u^2}`.

**Products.** Here `t u = a t`, `t u^2 = a^2 t` and `u^3 = t^-1 a^3 t = t^-1 (t a^2 t^-1) t = a^2`.

| `s \ m` | `1` | `a` | `t` | `u` | `u^2` |
|---|---|---|---|---|---|
| `1` | `1` | `a` | `t` | `u` | `u^2` |
| `a` | `a` | `a^2` | `at` | `au` | `au^2` |
| `t` | `t` | `ta` | `t^2` | `at` | `a^2 t` |
| `u` | `u` | `ua` | `ut` | `u^2` | `a^2` |

There are six coincidences: `(a,1) = (1,a)`, `(t,1) = (1,t)`, `(u,1) = (1,u)`, `(u,u) = (1,u^2)`, `(a,a) = (u,u^2)`,
`(a,t) = (t,u)`.

**There are no others.** The fourteen distinct entries are `1, a, t, u, u^2, a^2, at, au, au^2, ta, t^2, a^2 t, ua, ut`.
Their images under `rho`:

- *`t`-exponent 0:* `1, a, u, u^2, a^2, au, au^2, ua` give `x = 0, 1, 2/3, 4/3, 2, 5/3, 7/3, 5/3`.
- *`t`-exponent 1:* `t, at, ta, a^2 t, ut` give `x = 0, 1, 3/2, 2, 2/3`.
- *`t`-exponent 2:* `t^2`.

The only collision is `au` versus `ua`, which differ by (F1). So there are `20 - 6 = 14` classes. The labels are
distinct, and `T` is realized in `G`.

**P(T) is BS(2,3).** The relators are `x_a = y_a`, `x_t = y_t`, `x_u = y_u`, `x_u y_u = y_(u^2)`,
`x_a y_a = x_u y_(u^2)` and `x_a y_t = x_t y_u`. Eliminate:

- the four `y` letters, which gives `y_(u^2) = x_u^2`;
- `x_a = x_t x_u x_t^-1`, from the sixth relator.

The fifth relator becomes `x_t x_u^2 x_t^-1 = x_u^3`. So `P(T) = <x_t, x_u | x_t x_u^2 x_t^-1 = x_u^3>`. The map
`x_c -> c` sends `x_t -> t` and `x_u -> u = t^-1 a t`. Composing with the identification `a' = x_u`, `t' = x_t` of
this presentation with `BS(2,3)`, it is `a -> t^-1 a t`, `t -> t = t^-1 t t`. That is the inner automorphism by `t`.
So `phi: P(T) -> G` is an isomorphism.

**The gap pair.** Take the reverse cells `(a, u)` and `(u, a)`, with products `au` and `ua`. They are distinct by (F1)
and merged in every finite quotient by (F2). So `T` is a gap table of shape `4x5`.

`verify_gap36.g` checks both presentations with GAP's `SimplifiedFpGroup` and checks that the label maps are
homomorphisms. It also checks that none of the 10 transitive representations of `G` of degree at most 8 separates
either pair. `gaptable.certify2` recertifies both tables with the normal form of `bsgroup.py`: `gap_tables_3x6.jsonl`
and `gap_tables_4x5.jsonl`, first records.

## 5. Padding and transposes

**Padding.** Let `T` be a gap table of shape `p x q`, realized by labels `S, M` in a group `K`. Put
`K' = K * <z>` with `z` of infinite order, `S' = S u {z}`, and let `T'` be the forward table of `(S', M)` in `K'`.

- *The table is exact.* In the free product, `z m = z m'` forces `m = m'`, and `z m = s m'` with `s` in `K` would put
  `z` in `K`. So `T'` is `T` together with `q` singleton cells.
- *The labels are distinct*, so `T'` is realized.
- *The table group.* `P(T') = P(T) * <x_z>`.
- *The gap pair persists.* It is still distinct, since `P(T)` embeds in the free product. A finite quotient of
  `P(T')` restricts to a finite quotient of `P(T)`, which merges the pair.

So `T'` is a gap table of shape `(p+1) x q`, and in the same way of shape `p x (q+1)`. Gap shapes are upward closed.

**Transposes.** Since `s m = s' m'` iff `m^-1 s^-1 = m'^-1 s'^-1`, the forward table of `(M^-1, S^-1)` in `K` is
the transpose `T^t` of `T`, realized with distinct labels containing `1`. The map `x_c -> (x'_(c^-1))^-1` sends each
relator `x_s x_m = x_s' x_m'` of `P(T)` to the inverse of the relator `x'_(m^-1) x'_(s^-1) = x'_(m'^-1) x'_(s'^-1)`
of `P(T^t)`, and it has the inverse map of the same form. So it is an isomorphism. It sends the reverse cell
`x_m x_s` to the inverse of the reverse cell `x'_(s^-1) x'_(m^-1)` of `T^t`. So distinct pairs, and pairs merged by
every finite quotient, correspond. A shape is a gap shape iff its transpose is.

## 6. Conclusion

By Section 1, no shape with a side of size at most two is a gap shape. By
`strict-pairs-need-a-memory-with-five-elements`, no shape of size at most `4x4` is one, and by Section 2 neither
`3x5` nor `5x3` is. Sections 3 to 5 give gap tables at `3x6`, `6x3`, `4x5` and `5x4`, and at every larger shape.

The minimal elements of the up-set of gap shapes are therefore exactly `3x6`, `4x5`, `5x4` and `6x3`. The shapes that
are not gap shapes are exactly those with a side of size at most two, together with the four shapes `3x3`, `3x4`,
`3x5` and `4x4` and their transposes. QED.

**Strict pairs.** By the resolution lemma of `strict-pairs-need-a-memory-with-five-elements`, a strict pair with
memories of sizes `3` and `5` would have a forward table of shape `3x5` (after normalizing `1` into both memories and
padding), which is resolved. So none exists.
