# Rigid two-patch ternary seed: two-site moves, the relation `(a^-1 b)^2 = 1`, and a free-memory census

Lane w7-two-patch-rigid, 2026-09-12. These are candidate proofs on paper. They await independent re-derivation
by w3-vf-nonlinear.

- **Sections 1–4.** Claim `rigid-two-patch-seed-rule-is-never-injective`.
- **Sections 5–6.** Claim `unit-case-pair-distinct-two-patch-rules-are-not-injective`.
- **Parent.** `two-patch-ternary-rules-reduce-to-linear-strictness`.

## 0. Setting

- **Automaton.** `G` is a group with `1, a, b` distinct, and `H = <a, b>`. The window at `g` is
  `W_g = (g, ga, gb)`, and `tau(x)(g) = mu(x(g), x(ga), x(gb))`.
- **Seed.** `mu_3(y_1, y_a, y_b) = y_1 + y_a - y_b + [y = p] + [y = q]` over `F_3`, with `p = (0,0,2)` and
  `q = (1,2,0)`.
  - **Counts.** Outputs `0, 1, 2` occur `8, 9, 10` times.
  - **Diagonal.** `mu_3(v, v, v) = v`.
  - **Blind pairs.** A pair is blind at a coordinate when changing that coordinate within the pair keeps
    the output, for the context shown:

    | coordinate | pair at context | pair at context |
    |---|---|---|
    | `1` | `{0,1}` at `(y_a, y_b) = (0,2)` | `{1,2}` at `(2,0)` |
    | `a` | `{0,1}` at `(y_1, y_b) = (0,2)` | `{0,2}` at `(1,0)` |
    | `b` | `{1,2}` at `(y_1, y_a) = (0,0)` | `{0,2}` at `(1,2)` |

  - **Rigid.** Every pair is blind at exactly two coordinates: `{0,1}` at `1, a`, `{1,2}` at `1, b`, and
    `{0,2}` at `a, b`. No pair is blind at all three.
- **Collisions.** Let `x, x'` agree off a finite set `S` and differ at each site of `S`. Then
  `tau x = tau x'` if and only if the outputs agree at every touched window, that is, at every `g` in
  `S M^-1` with `M = {1, a, b}`.
- **Moves.** A move is a list of words with values. It realizes in `G` if the assignment is well defined
  there: words that coincide in `G` carry equal values in both `x` and `x'`.
  - **Conflicts.** A changed word that coincides with an unchanged one is a conflict, and so are unchanged
    words with different values that coincide.
  - **Relators.** A coincidence `u = w` means `u^-1 w = 1` in `H`. We call `u^-1 w` its relator.
  - Touched windows that coincide are one window, so conflicts are the only obstruction.
  - A site marked `*` may take any value, and every completion is a collision.
- **Quotient rule.** If a relator `r` holds in `H`, then `H` is a quotient of `<a, b | r>`. So a relator
  that makes that group cyclic, `Z^2`, or the Klein bottle group `<s, t | s t s^-1 = t^-1>` makes `H`
  amenable.

## 1. Three two-site moves over free memory

Words are reduced in `F(a, b)`, and the eleven words of each move are distinct there.

**Move `T_ab`.** Change `a: 1 -> 2` and `b: 0 -> 1`. Context: `1 = *`, `a^2 = 2`, `ab = 0`, `ab^-1 = 0`,
`ab^-1 a = 0`, `ba = 0`, `b^2 = 2`, `ba^-1 = 0`, `ba^-1 b = 2`.

| window | before | after | outputs |
|---|---|---|---|
| `1` | `(*, 1, 0)` | `(*, 2, 1)` | `* + 1` both, no patch |
| `a` | `(1, 2, 0)` | `(2, 2, 0)` | `1` (patch `q`), `1` |
| `ab^-1` | `(0, 0, 1)` | `(0, 0, 2)` | `2`, `2` (patch `p`) |
| `b` | `(0, 0, 2)` | `(1, 0, 2)` | `2` (patch `p`), `2` |
| `ba^-1` | `(0, 0, 2)` | `(0, 1, 2)` | `2` (patch `p`), `2` |

**Move `T_1a`.** Change `1: 0 -> 2` and `a: 1 -> 2`. Context: `b = *`, `a^-1 = 1`, `a^-1 b = 0`,
`b^-1 = 1`, `b^-1 a = 2`, `a^2 = 2`, `ab = 0`, `ab^-1 = 0`, `ab^-1 a = 0`.

| window | before | after | outputs |
|---|---|---|---|
| `1` | `(0, 1, *)` | `(2, 2, *)` | `1 - *` both, no patch |
| `a^-1` | `(1, 0, 0)` | `(1, 2, 0)` | `1`, `1` (patch `q`) |
| `b^-1` | `(1, 2, 0)` | `(1, 2, 2)` | `1` (patch `q`), `1` |
| `a` | `(1, 2, 0)` | `(2, 2, 0)` | `1` (patch `q`), `1` |
| `ab^-1` | `(0, 0, 1)` | `(0, 0, 2)` | `2`, `2` (patch `p`) |

**Move `T_1b`.** Change `1: 0 -> 2` and `b: 1 -> 0`. Context: `a = *`, `a^-1 = 1`, `a^-1 b = 0`,
`b^-1 = 1`, `b^-1 a = 2`, `ba = 0`, `b^2 = 2`, `ba^-1 = 0`, `ba^-1 b = 2`.

| window | before | after | outputs |
|---|---|---|---|
| `1` | `(0, *, 1)` | `(2, *, 0)` | `* - 1` both, no patch |
| `a^-1` | `(1, 0, 0)` | `(1, 2, 0)` | `1`, `1` (patch `q`) |
| `b^-1` | `(1, 2, 0)` | `(1, 2, 2)` | `1` (patch `q`), `1` |
| `b` | `(1, 0, 2)` | `(0, 0, 2)` | `2`, `2` (patch `p`) |
| `ba^-1` | `(0, 1, 2)` | `(0, 0, 2)` | `2`, `2` (patch `p`) |

**Why two sites.** Each changed site has two private windows, at the addresses other than its address in the
shared window. So its pair must be blind at those two coordinates.
- `T_ab` uses `{1,2}` at `1, b` for `a`, and `{0,1}` at `1, a` for `b`.
- `T_1a` uses `{0,2}` at `a, b` for `1`, and `{1,2}` at `1, b` for `a`.
- `T_1b` uses `{0,2}` at `a, b` for `1`, and `{0,1}` at `1, a` for `b`.

## 2. Coincidence tables

For each move, compare all 55 pairs of its eleven words. The conflicting coincidences give the relators below,
up to rotation and inversion. Write `c = a^-1 b`. A relator `a`, `b` or `a^-1 b` breaks distinctness. The
others listed as cyclic express one generator as a power of the other, or both as powers of one word.

**`T_ab`.**
- **Cyclic.** `a`, `b`, `a^-1 b`, `ab`, `a^-2 b`, `b^-2 a`, `a^-3 b` and `b^-3 a`, together with:
  - `a b^-2 a b^-1`, where `x = ab^-1` gives `b = x^2` and `a = x^3`;
  - `b a^-1 b a^-1 b`, where `x = ba^-1` gives `b = x^-2` and `a = x^-3`.
- **Nonamenable.**
  - `c^2`, from `a = ba^-1 b` and from `b = ab^-1 a`.
  - `c^3`, from `ab^-1 a = ba^-1 b`.

**`T_1a`.**
- **Cyclic.** `a`, `b`, `a^-1 b`, `ab`, `a^-2 b`, `a^2 b`, `b^-2 a`, `b^2 a`, `a^-3 b`.
- **`Z^2`.** `[a, b]`.
- **Klein bottle.** `b a b^-1 a` and `a^-1 b a b`.
- **Nonamenable.**
  - `a^2`, from `1 = a^2` and from `a^-1 = a`.
  - `a^3`, from `a^-1 = a^2`.
  - `c^2`, from `b^-1 a = a^-1 b`.

**`T_1b`.**
- **Cyclic.** `a`, `b`, `a^-1 b`, `ab`, `a^-2 b`, `a^2 b`, `b^-2 a`, `b^2 a`, `b^-3 a`.
- **Klein bottle.** `a b a^-1 b` and `a^2 b^-2`.
- **Nonamenable.**
  - `b^2`, from `1 = b^2`, from `b^-1 = b` and from `b^-1 a = ba`.
  - `b^3`, from `b^-1 = b^2`.
  - `c^2`, from `b^-1 a = a^-1 b`.

## 3. The relation `c^2 = 1`

Suppose `c = a^-1 b` satisfies `c^2 = 1`. Then `H` is a quotient of `Z * Z/2 = <a> * <c>`, and:
- `b = ac` and `b^-1 = ca^-1`;
- `ab^-1 = ba^-1 = aca^-1`;
- `ab^-1 a = b` and `ba^-1 b = a`.

So the windows `ab^-1` and `ba^-1` of `T_ab` coincide, and that window reads both changed sites.

**Move `C`.** Change `a: 0 -> 1` and `b: 1 -> 2`. Context: `1 = *`, `w = ab^-1 = *`, `a^2 = 0`, `ab = 2`,
`ba = 2`, `b^2 = 0`.

| window | sites | before | after | outputs |
|---|---|---|---|---|
| `a` | `(a, a^2, ab)` | `(0, 0, 2)` | `(1, 0, 2)` | `2` (patch `p`), `2` |
| `b` | `(b, ba, b^2)` | `(1, 2, 0)` | `(2, 2, 0)` | `1` (patch `q`), `1` |
| `1` | `(1, a, b)` | `(*, 0, 1)` | `(*, 1, 2)` | `* - 1` both, no patch |
| `w` | `(w, b, a)` | `(*, 1, 0)` | `(*, 2, 1)` | `* + 1` both, no patch |

These are all the touched windows: `a` is read by the windows `a`, `1` and `w`, and `b` by `b`, `w` and `1`.

**Coincidences.** In `Z * Z/2` the eight words have distinct normal forms `1, a, ac, a^2, a^2 c, aca, acac, aca^-1`.
Their conflicting coincidences force `a = 1`, `c = 1` or `a = c`.
- `a = 1` and `c = 1` break distinctness.
- `a = c` gives `b = a^2 = c^2 = 1`.

So Move `C` realizes in every group where `c^2 = 1` and `1, a, b` are distinct.

## 4. Theorem

**Theorem 4.1.** `tau` for `mu_3` is not injective over any group `G` in which `1, a, b` are distinct. If
`<a, b>` is nonamenable, two configurations that differ at two sites have the same image.

*Proof.* A collision over `H` extends to `G` coset by coset, and an injective automaton over `G` is injective over
`H`. So work over `H`.
- **Amenable `H`.** An injective `tau` is pre-injective, so it is surjective by the Garden of Eden theorem, and
  then bijective. By `bijective-ca-preserve-uniform-bernoulli-measure` it preserves the uniform Bernoulli
  measure. So `mu_3` of a uniform triple is uniform, but the counts are `8, 9, 10`.
- **Nonamenable `H`.** If some move realizes, we are done. Otherwise each of `T_ab`, `T_1a` and `T_1b` has a
  conflict whose relator holds in `H`. By the quotient rule, only the relators listed as nonamenable in Section 2
  are possible.
  - **`c^2 = 1`.** Move `C` realizes, by Section 3.
  - **Otherwise.** `c^3 = 1`, `a^k = 1` and `b^m = 1` for some `k, m` in `{2, 3}`. So `H` is a quotient of the
    von Dyck group `<x, y | x^k, y^m, (xy)^3>` with `x = a^-1` and `y = b`. That group has order 6 for
    `(k, m) = (2, 2)` and order 12 for `(2, 3)` and `(3, 2)`. For `(3, 3)` it is the Euclidean triangle group,
    which is virtually `Z^2`. All are amenable, a contradiction. ∎

## 5. Uniform filters

**Lemma 5.1 (injectivity descends to marked quotients).** Let `pi: H -> Q` be a surjective homomorphism.
- **Automaton on `Q`.** `tau_Q(x)(u) = mu(x(u), x(u pi(a)), x(u pi(b)))` on `F_3^Q`.
- **Intertwining.** `tau_H(x ∘ pi) = tau_Q(x) ∘ pi`, since `pi(ha) = pi(h) pi(a)`.
- **Conclusion.** `x -> x ∘ pi` is injective. So if `tau_H` is injective, so is `tau_Q`.

**Corollary 5.2 (constants).** Take `Q = 1`. If `v -> mu(v, v, v)` is not injective, then `tau` is not injective over
any group.

**Corollary 5.3 (host filter).** Let `mu` be unbalanced and `tau_H` injective. Then for every amenable quotient `Q`
of `H`, the restriction of `mu` to the coincidence pattern of `1, pi(a), pi(b)` is balanced.
- **Proof.** Apply Lemma 5.1, then the amenable case of Theorem 4.1 to `tau_Q`, whose memory set is the image
  of `{1, a, b}`.
- **For `mu_3`.** `mu_3(y, y, z) = 2y - z + [(y, z) = (0, 2)]` is unbalanced. The other restrictions are
  balanced: `mu_3(y, z, y) = z`, `mu_3(y, z, z) = y` and `mu_3(v, v, v) = v`. So a host would need `b = 1` or
  `a = b` in every amenable quotient. Theorem 4.1 makes this moot for `mu_3`.
- **For `mu' = x_1 + x_a - x_b + [(0,1,0)] - [(1,2,2)]`.**
  - **Balanced.** `mu'(y, y, z) = 2y - z` and `mu'(v, v, v) = v`.
  - **Unbalanced.** `mu'(y, z, y) = z + [(y, z) = (0, 1)]` and `mu'(y, z, z) = y - [(y, z) = (1, 2)]`.
  - **So** in every amenable quotient of a counterexample host, `a` maps to `1`.
  - **With the unit hypothesis.** The abelianization `Q` of `<a, b>` is cyclic of odd order, generated by the
    image of `b`.
    - A unit of `F_3[G]` lying in `F_3[H]` is a unit of `F_3[H]`: take the `H`-component of its inverse.
    - `a` dies in `Q`, so `1 + a - b` maps to `2 - b`.
    - `2 - b` is not a unit in `F_3[Z]`. In `F_3[Z/n] = F_3[t]/(t^n - 1)` it is a unit exactly when
      `1 + t` does not divide `t^n - 1`, that is, when `n` is odd.

## 6. Free-memory census and the smallest open case

**Enumeration.** The census lists rules up to three symmetries:
- **Output shift.** Take `c_0 = 0`, since a shift of the output changes nothing.
- **Coordinate permutations.** They come from changing the generating pair. For example, `W_(h a^-1)` reads
  `(h a^-1, h, h a^-1 b)`.
- **Global negation.** `mu -> -mu(-y)` is a bijection.

The coefficient classes that can be units are then `(1, 1, -1)` and `(1, 1, 0)`. Augmentation `0` is never a unit,
and a rule with one nonzero coefficient is never rigid.
- **Patches.** Unordered pairs `p != q` sharing a symbol, with weights in `{1, 2}^2`.
- **Blind pairs.** Found by trying all nine contexts. This does not use Proposition 4 of
  `two-patch-seed-relation-moves-2026-09-12.md`, which needs patches at distance two or more.
- **Counts.** Raw, so symmetric duplicates are counted separately.

**Leaf principle over free memory.** Over `F(a, b)` the site–window incidence graph of a finite collision is a
forest; the proof is the argument of `pair-distinct-ternary-rules-pre-injective-on-free-memory`.
- **Leaves.** A leaf site has at least two private windows, so its pair is blind at two coordinates.
- **Two-site collisions.** A shared window reads `s` at address `m` and `t` at address `m' != m`. So `s` needs a
  pair blind at the two addresses other than `m`, and `t` a pair blind at the two other than `m'`. The shared
  window must also absorb both changes for some value at its third address.

| class | description | `(1,1,-1)` | `(1,1,0)` |
|---|---|---|---|
| diagonal collapses | settled by Corollary 5.2 | 114 | 12 |
| `I_3` | all three two-site shapes exist, as for `mu_3` | 42 | 0 |
| `I_1` | exactly one two-site shape exists | 186 | 276 |
| `I_0` | one doubly blind coordinate pair, so no two-site collision | 195 | 0 |
| `II` | three distinct blind pairs, none blind twice | 30 | 0 |

There are 855 rigid unbalanced rules, and 126 of them have a collapsing diagonal. The rows after the first count
only rules with an injective diagonal.

- **`I_3` and `I_1`.** Two-site moves exist over free memory. Relation tables have been done only for `mu_3`.
- **`I_0`.** Every leaf of a collision must read its shared window at the same address. Longer supports, such as
  three sites along two windows, are not excluded. They were not searched.
- **`II`.**
  - **No finite collision over free memory.** In all 42 raw rules of this class, each coordinate has exactly one
    blind pair, and the three pairs are distinct. So these are exactly the rules of
    `pair-distinct-ternary-rules-pre-injective-on-free-memory`.
  - **Lifting.** Suppose the ball of radius `R` of `F(a, b)` maps injectively into `H`. Take a collision whose
    changed sites lie within `R - 2` of one of them, and lift it. The result is a finite collision over free
    memory, which cannot exist.
  - **Known cases.** Over amenable and sofic `H`, balance rules these rules out. In the non-unit case,
    injectivity gives the parent claim's conclusion. So the open case is a nonsofic `H` in which the linear
    part is a unit.
- **Scale of the unit.** Suppose `1 + a - b` has an inverse `K` supported on words of length at most `r`. Then
  `H` has a relation of length at most `2r + 2`. Otherwise `(1 + a - b)K = 1` would lift to `F_3[F(a, b)]`,
  where `1 + a - b` has no one-sided inverse. So moves at the scale of the inverse are not excluded.

**Smallest open case.** This is class `II`, with 30 raw rules. The seed is
`mu' = x_1 + x_a - x_b + [(0,1,0)] - [(1,2,2)]`:
- counts `10, 7, 10`;
- blind pairs `{0,1}`, `{1,2}` and `{0,2}` at `1, a, b`;
- identity diagonal, and shared symbol `1`.

The open case is `mu'` over a nonsofic `H` in which `1 + a - b` is a unit and `a` maps to `1` in every amenable
quotient. No collision is known there, and no obstruction either.

## 7. Where it stops, and checks

- **Awaiting re-derivation by w3-vf-nonlinear.** Theorem 4.1, Lemma 5.1 with its corollaries, and the class `II`
  lifting bound.
- **Not attempted.**
  - relation tables for the other `I_3` rules and for the `I_1` rules;
  - three-site supports for `I_0`;
  - Proposition 5 residues and delta-preimage moves for `mu'`.
- **Checks.** The window tables of Sections 1 and 3, the coincidence lists and the census were replayed with tiny
  `F_3` scripts in the lane scratch. They ran for a few seconds, and nothing was landed from them. Every entry the
  proofs use is listed above for re-derivation by hand. The relator classification in Section 2 is by hand.
