---
rg: 2
id: baumslag-solitar-gap-table-at-five-by-five-proof
kind: route
title: Compute the forward table in BS(2,3), eliminate letters down to the Baumslag-Solitar relator, and separate by Britton but not by finite quotients
target: baumslag-solitar-gap-table-at-five-by-five
requires:
  - strict-pairs-need-a-memory-with-five-elements
  - strict-automata-live-on-canonical-table-groups
  - elek-szabo-sofic-permanence
  - sofic-groups-are-surjunctive
artifacts:
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/RESULTS.md
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/bsgroup.py
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/gaptable.py
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/verify_gap55.g
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/gap_tables_5x5.jsonl
---

Let `G = BS(2,3) = <a, t | t a^2 t^-1 = a^3>`, and write `u = t^-1 a t`.

- The memories are `S = {1, a, t, a^3, u a^-1}` and `M = {1, a, a^2, t, u}`.
- Letters of `P(T)`: `x_a, x_t, x_3, x_4` for the non-identity elements of `S`, in that order, and
  `y_1, y_2, y_3, y_4` for `a, a^2, t, u` in `M`.

## 1. Britton's lemma and the map to H

We use two standard facts.

**Britton's lemma.** A word in `a, t` with at least one `t^{+-1}` and no pinch is nontrivial in `G`. A pinch is a
subword `t a^k t^-1` with `2 | k`, or `t^-1 a^k t` with `3 | k`. In particular, `a` and `u` do not commute. The
commutator `a t^-1 a t a^-1 t^-1 a^-1 t` has the subwords `t^-1 a t` and `t^-1 a^-1 t`, with exponents `+-1` not
divisible by `3`, and `t a^-1 t^-1`, with exponent `-1` not divisible by `2`. So it has no pinch and is
nontrivial.

**The map to H.** Let `H = Z[1/6] x| Z`, where the generator of `Z` acts by multiplication by `3/2`. Then
`a -> (1, 0)` and `t -> (0, 1)` define a homomorphism `rho: G -> H`, because `t a^2 t^-1 -> 2 * 3/2 = 3`. A word
maps to `(x, i)`, where `i` is its `t`-exponent sum and `x` is the sum of `+-(3/2)^j` over its `a`-letters,
with `j` the `t`-exponent sum of the prefix before that letter.

## 2. The forward table

The products `sm` are the following.

| `s \ m` | `1` | `a` | `a^2` | `t` | `u` |
|---|---|---|---|---|---|
| `1` | `1` | `a` | `a^2` | `t` | `u` |
| `a` | `a` | `a^2` | `a^3` | `at` | `au` |
| `t` | `t` | `ta` | `ta^2 = a^3 t` | `t^2` | `tu = at` |
| `a^3` | `a^3` | `a^4` | `a^5` | `a^3 t` | `a^3 u` |
| `u a^-1` | `u a^-1` | `u` | `u a` | `u a^-1 t` | `u a^-1 u` |

**The seven coincidences hold.** Six are immediate. The seventh is `t a^2 = a^3 t`, which is the relator.

**There are no other coincidences.** Images under `rho`, sorted by `t`-exponent:

- *Exponent 0.*
  - `1, a, a^2, a^3, a^4, a^5` map to `0, 1, 2, 3, 4, 5`.
  - `u, au, a^3 u` map to `2/3, 5/3, 11/3`.
  - `u a^-1, u a, u a^-1 u` map to `-1/3, 5/3, 1/3`.
- *Exponent 1.* `t, at, ta, a^3 t, u a^-1 t` map to `0, 1, 3/2, 3, -1/3`.
- *Exponent 2.* `t^2` alone.

Different images mean different elements. The only collision among distinct entries of the table is `au` versus
`ua`, both with image `(5/3, 0)`. These are different elements, because `a` and `u` do not commute (Section 1).
So the table has 18 classes on 25 cells, which is exactly the seven coincidences. The labels in `S` are distinct
(column `m = 1`), and so are the labels in `M` (row `s = 1`). So `T = T_f(G)` is realized with distinct
labels. `gaptable.py` recomputes this with the normal form of `bsgroup.py`.

## 3. The table group is BS(2,3)

The relators of `P(T)`, in the order of the theorem, are:

```text
x_a = y_1,   x_a y_1 = y_2,   x_t = y_3,   x_4 y_1 = y_4,   x_a y_2 = x_3,   x_a y_3 = x_t y_4,   x_t y_2 = x_3 y_3.
```

Eliminate the letters in turn:

- `y_1 = x_a`, then `y_2 = x_a^2`, `y_3 = x_t`, `y_4 = x_4 x_a` and `x_3 = x_a^3`.
- The sixth relator becomes `x_a x_t = x_t x_4 x_a`, so `x_4 = x_t^-1 x_a x_t x_a^-1`.
- The last relator becomes `x_t x_a^2 = x_a^3 x_t`.

So `P(T) = <x_a, x_t | x_t x_a^2 x_t^-1 = x_a^3>`. Under this identification `x_c -> c` is the identity of
`BS(2,3)` on generators, so it is an isomorphism `phi: P(T) -> G`. GAP's `SimplifiedFpGroup` gives the same
presentation, and `verify_gap55.g` checks that the label map is a homomorphism.

## 4. The reverse pair is a gap

The reverse cells are `(m, s) = (a, u a^-1)` and `(u, 1)`. In `P(T)`, through `phi`, their products are
`a u a^-1` and `u`.

**Distinct in P(T).** They are equal iff `a u = u a`, which is false by Section 1.

**Equal in every finite quotient.** Let `pi: P(T) -> F` be a homomorphism to a finite group. Write `alpha = pi(x_a)`,
`tau = pi(x_t)` and `n = ord(alpha)`.

- `alpha^2` and `alpha^3` are conjugate, so `n / gcd(n, 2) = n / gcd(n, 3)`. This forces `gcd(n, 2) = gcd(n, 3)`,
  and since the first lies in `{1, 2}` and the second in `{1, 3}`, both are `1`.
- So `alpha^2` generates `<alpha>`. Hence `tau <alpha> tau^-1 = <tau alpha^2 tau^-1> = <alpha^3> = <alpha>`.
- So `tau^-1 alpha tau` lies in `<alpha>` and commutes with `alpha`. Therefore
  `pi(x_a x_u x_a^-1) = pi(x_u)`, where `x_u = x_t^-1 x_a x_t`.

**T is a gap table.** Section 2 shows that `T` is realizable. The pair above is distinct in `P(T)` and merged by
every finite quotient. So `T` is not resolved, and it is a gap table.

`verify_gap55.g` confirms that none of the 10 transitive permutation representations of `P(T)` of degree at most 8
separates the pair. The census pipeline of `strict-pairs-need-a-memory-with-five-elements` (`gapcensus.py reps 5 5`,
then `pass3.py`) reports this table as `CANDIDATE`, with exactly this unseparated pair.

## 5. Soficity kills the table anyway

**P(T) is sofic.** Let `N` be the kernel of `G -> Z`, where `t -> 1` and `a -> 0`.

1. *The kernel as an amalgam.* By Bass-Serre theory `N` is the fundamental group of a bi-infinite line of groups.
   The vertex groups are `<a_i> = Z`, with `a_i = t^i a t^-i`, and the edges are `a_i^3 = a_(i+1)^2`.
2. *Finite pieces.* The finite segments `N_k = <a_-k, ..., a_k | a_i^3 = a_(i+1)^2>` are subgroups, and `N` is
   their directed union.
3. *A central element.* `z = a_-k^(3^(2k)) = a_k^(2^(2k))` lies in every vertex group of `N_k`, so it is central.
4. *Each piece is residually finite.* `N_k / <z>` is a finite tree of finite cyclic groups, so it is virtually
   free. Over a free subgroup of finite index, the central extension by `<z> = Z` splits, because `H^2` of a free
   group vanishes. So `N_k` is virtually `F x Z`. That group is residually finite, hence sofic.
5. *Conclusion.* `N` is a directed union of sofic groups, and `G / N = Z` is amenable. By `elek-szabo-sofic-permanence`
   (direct limits, subgroups, and extensions by amenable quotients), `G` is sofic. This also follows from the
   permanence of soficity under HNN extensions over amenable subgroups, quoted in
   `berlai-residue-class-kernel-decomposition`.

**No strict pair has forward table T.** Suppose a group `K`, a finite alphabet and rules give a strict pair with
labels `S, M` in `K` and `T_f(K) = T`.

- The relators of `P(T)` hold in `K`, so `x_c -> c` is a homomorphism `P(T) -> K`.
- Hence `T_r(P(T))` refines `T_r(K)`, and `T_f(P(T))` is coarser than or equal to `T`.
- By the monotonicity in Section 1.3 of `strict-pairs-need-a-memory-with-five-elements-proof`, the same rules
  over `P(T)` satisfy `Dec` and fail `Enc`. So they give an injective automaton on `A^(P(T))` that is not
  surjective.
- This is the pullback of `strict-automata-live-on-canonical-table-groups`. It contradicts
  `sofic-groups-are-surjunctive`, since `P(T) = G` is sofic.

QED.

## 6. How the table was found

`bsgapsearch.py` and `extend.py` search memory pairs inside `BS(2,3)`. They keep a pair when two reverse products
have the same image in `H` but different normal forms, and when Tietze elimination of its forward relators leaves
two letters with the Baumslag-Solitar relator. That certificate is exactly Sections 2 to 4.

The counts are in `RESULTS.md`:

- No certified table at `4x4`, `4x5` or `5x4` over the radius-2 ball, nor at `4x5` or `5x4` over extensions from the
  radius-4 ball.
- One certified table at `5x5`, from extensions over the radius-4 ball.
- Two certified tables at `5x6`.

The certificate is sufficient, not necessary. So the zero counts do not decide whether a gap table of shape `4x5`
exists.
