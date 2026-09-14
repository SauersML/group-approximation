# Three-factor audit, and surjunctivity of controlled self-linear feedback

Lane `gk-three-factor`, 2026-09-12. Supports
`controlled-self-linear-feedback-ca-are-surjunctive`,
`gottschalk-specializes-to-three-factor-class` and
`three-factor-class-specializes-to-recipient-affine`. Mathematics on paper; no
computation was used.

## 1. Audit of the stable three-factor reduction

Every step of `gottschalk-stable-three-factor-reduction-2026-09-08.md` was
re-derived independently.

1. **Setting.** `G` is any group and `A` a finite alphabet with `q >= 2`
   symbols, identified with `R = Z/qZ`. Only the additive group of `R` and
   its commutative multiplication at one output site are used.
2. **The cancellation.** Take a term `cAB` of length `d >= 4` in output
   coordinate `i`, with factor lengths `a, b >= 2`. Put
   `S(x,u,v) = (x, u + A(x), v + B(x))` and `T(y,r,s) = (y - c r s e_i, r, s)`.
   `T` reads only `r` and `s`, which it passes through unchanged, so adding
   `c r s e_i` inverts it. The composite `T o (F x id) o S` sends `(x,u,v)` to
   `(F(x) - c(u + A(x))(v + B(x)) e_i, u + A(x), v + B(x))`. Expanding at the
   output site gives `F_i - cAB - cuv - cuB - cvA`, as the artifact states.
3. **Lengths.** The seven new occurrences have lengths `2, b+1, a+1` in
   coordinate `i` and `1, a, 1, b` in the new coordinates. Since `a, b >= 2`
   and `a + b = d`, each is at most `d - 1`. So `Phi` drops by at least
   `8^d - 7 * 8^(d-1) = 8^(d-1) > 0`. A split with both parts of length at
   least two exists exactly when `d >= 4`, so the procedure stops with every
   length at most three.
4. **Setting preserved.** Domain and codomain stay full shifts over the same
   group, with alphabet `R^(N+2)`. Adding identity tracks and composing with
   bijective automata preserves injectivity and surjectivity in both
   directions. The intermediate map's memory stays inside the original `M`.
5. **Quantifiers.** The equivalence holds group by group. For fixed `G`,
   Gottschalk's assertion for all finite alphabets holds if and only if the
   three-factor assertion holds for all `q >= 2` and all `N`. The converse
   direction is a specialization, since a three-factor automaton is an automaton.

**Verdict.** The reduction is correct, and it is an equivalence.
`three-factor-finite-alphabet-ca-are-surjunctive` restates the conjecture in
normal form, the way 3-SAT restates SAT; it is not a smaller problem.
`recipient-affine-three-factor-ca-are-surjunctive` restates it again: its
hypotheses define a subclass of the three-factor class, and
`affine-normal-form-reduces-three-factor-surjunctivity` shows that subclass is
already universal. The two specialization routes landed with this artifact
make both cycles visible in the graph. The 09-08 positive theorems (bipartite
operand graphs, target-multiplicative systems, cyclic nearest-two feedback,
the common-factor and central `C_3` families) exclude subclasses inside the
conjecture. They are not steps toward a smaller target.

**Scoped remark on the bound three.** The shear trick itself cannot lower the
bound to two. Splitting a length-three term as `1 + 2` creates the term `uB`
of length three again, and `Phi` rises: `8^3 = 512` is removed and
`8^2 + 8^3 + 8^2 + 8 + 8 + 8 + 8^2 = 728` is added. This concerns this
particular move only; no invariant forbidding a quadratic normal form is
claimed.

## 2. Controlled self-linear feedback

### Statement

Let `G` be a group and `R` a finite ring. Partition the tracks into blocks
`X_1, ..., X_r`, where block `a` has alphabet `R^(d_a)`. Let `F` be a cellular
automaton on the product full shift whose rows have the form

```text
F_a(x)(g) = X_a(g) + sum_(s in S) C_(a,s)(x)(g) . X_a(g s),      a = 1, ..., r,     (2.1)
```

where `S` is a finite subset of `G` and each **controller** `C_(a,s)` is a
local `M_(d_a)(R)`-valued function (finite memory, equivariant) that reads no
coordinate of block `a`. It may read every other block at any addresses, with
any nonlinearity. Write

```text
L0_a X_a(g) = X_a(g) + sum_s C_(a,s)(0)(g) . X_a(g s)
```

for the constant linear automaton obtained by setting every other block to
zero.

**Theorem 2.1.** If every `L0_a` is bijective and `F` is injective, then `F`
is surjective. In particular this holds when every controller vanishes
whenever all other blocks vanish, since then `L0_a = id`.

### Two-block lemma

**Lemma 2.2.** Let `F(X,Y) = (L_Y X, V(X,Y))` be a cellular automaton on a
product full shift, where `X` has alphabet `R^d` and
`L_Y X(g) = sum_s C_s(Y)(g) . X(g s)` with local controllers `C_s`. Assume:

1. `v_0 : Y -> V(0,Y)` is surjective;
2. `L_(Y_0)` is bijective for one configuration `Y_0`.

If `F` is injective, then `F` is surjective.

*Proof.*
- **Every `L_Y` is injective.** Suppose `L_Y X = 0`. By (1) choose `Y'` with
  `V(0,Y') = V(X,Y)`. Then `F(X,Y) = (0, V(X,Y)) = (L_(Y') 0, V(0,Y')) = F(0,Y')`,
  so `X = 0` by injectivity. `L_Y` is additive, so it is injective.
- **Straightening the first block.** `E(X,Y) = (L_Y X, Y)` is an injective
  automaton that leaves the certificate `Y` unchanged, and its fiber at `Y_0`
  is bijective. By `nonlinear-certificate-fibers-are-all-surjective-or-all-strict`,
  `E` is surjective, hence bijective. By Curtis–Hedlund–Lyndon its inverse
  `(Z,Y) -> (L_Y^(-1) Z, Y)` is a cellular automaton.
- **The zero fiber.** `D = F o E^(-1)` sends `(Z,Y)` to `(Z, V(L_Y^(-1) Z, Y))`.
  It is an injective automaton that leaves the certificate `Z` unchanged. Its
  fiber at `Z = 0` is `Y -> V(0,Y) = v_0`, which is surjective by (1). The
  same theorem makes `D` surjective, so `F = D o E` is surjective. QED

### Proof of Theorem 2.1

Induction on the number `r` of blocks.

- **`r = 1`.** The controllers read nothing, so they are constants equal to
  `C_(1,s)(0)`, and `F = L0_1` is bijective by hypothesis.
- **`r >= 2`.** Put `X = X_1` and `Y = (X_2, ..., X_r)`.
  - Row 1 is `L_Y X` with `L_Y X(g) = X(g) + sum_s C_(1,s)(Y)(g) . X(g s)`,
    because `C_(1,s)` reads only `Y`. Here `L_0 = L0_1` is bijective, which is
    condition (2) with `Y_0 = 0`.
  - The rows `a >= 2` at `X = 0` define `v_0`. This is a system of the form
    (2.1) on `r - 1` blocks, with controllers `C_(a,s)(0, .)`. They still read
    no coordinate of their own block, and they give the same constant
    operators `L0_a`.
  - `F(0,Y) = (0, v_0(Y))`, so `v_0` is injective. By induction `v_0` is
    bijective, which is condition (1).
  - Lemma 2.2 finishes the step. QED

### The peeling criterion

The same induction tolerates offsets and own-block nonlinearity once they
vanish with the earlier blocks.

**Theorem 2.3.** Let `F` be a cellular automaton on a product full shift with
block rows `F_1, ..., F_r`, block `a` with alphabet `R^(d_a)`. Suppose the
blocks can be ordered so that, for every `a`, setting
`X_1 = ... = X_(a-1) = 0` turns row `a` into

```text
X_a(g) + sum_(s in S) C_(a,s)(X_(a+1), ..., X_r)(g) . X_a(g s),                  (2.2)
```

with local controllers reading only later blocks, and with bijective constant
part `L0_a` (all later blocks zero). If `F` is injective, then `F` is
surjective.

Before the earlier blocks are set to zero, row `a` is unrestricted. It may
carry pure-others offsets and nonlinearity in its own block, provided these
vanish whenever `X_1, ..., X_(a-1)` vanish. Theorem 2.1 is the special case
with no such terms; its hypotheses hold in every ordering, because a controller
reading any other block reads only later blocks once the earlier ones are zero.

*Proof.* For `a = 1, ..., r` let `S_a` be the automaton on blocks
`a, ..., r` sending `(X_a, ..., X_r)` to rows `a, ..., r` of
`F(0, ..., 0, X_a, ..., X_r)`.

- **`S_a` is injective.** For `b < a`, row `b` of
  `F(0, ..., 0, X_a, ..., X_r)` is (2.2) for `b` evaluated at `X_b = 0`, which
  is zero. So `F(0, X_(>=a)) = (0, S_a(X_(>=a)))`, and injectivity of `F`
  passes to `S_a`.
- **Downward induction.** `S_r = L0_r` is bijective. For `a < r`, row `a` of
  `S_a` is `L_Y X_a` with `Y = (X_(a+1), ..., X_r)`, and `L_0 = L0_a` is
  bijective. Also `S_a(0, Y) = (0, S_(a+1)(Y))`, so `v_0 = S_(a+1)`, which is
  bijective by induction. Lemma 2.2 makes `S_a` surjective, hence bijective.
- **Conclusion.** `S_1 = F`. QED

**No ordering peels the universal normal form.** In
`H(x,u) = (x + u, F(x) - x - u)`:
- with `x` first, its row `x + u` has the offset `u`;
- with `u` first, its row `-u + (F(x) - x)` has the offset `F(x) - x`, which
  vanishes identically only when `F = id`.

This agrees with universality: the peeling criterion cannot apply to every
automaton unless the conjecture holds.

### Corollaries

- **Bipartite quadratic operand graphs** (09-08 block-elimination artifact).
  Take two blocks. Each row is linear in its own block, with controllers
  linear in the other block that vanish at zero.
- **Target-multiplicative systems** `F_i = x_i + sum_(j != i) B_(ij)(x_i, x_j)`.
  Take single-track blocks; the controllers are linear in `x_j`.
- **New scope.** Controllers of any degree and memory, reading any number of
  other blocks. For Boolean polynomial automata the criterion reads: for some
  partition of the tracks, every monomial of a row in block `a`, other than
  the identity monomial `X_a(g)`, has exactly one factor from block `a`, and
  the monomials with no other factor give a bijective linear automaton. For
  instance, over `F_2` with three tracks,

  ```text
  F_1(x)(g) = x_1(g) + x_2(gs) x_3(gt) x_1(gp) + x_2(gu) x_1(gp'),
  F_2(x)(g) = x_2(g) + x_1(gv) x_3(gw) x_2(gq),
  F_3(x)(g) = x_3(g) + x_1(gm) x_2(gn) x_3(gq'),
  ```

  is surjective whenever it is injective, over every group and for all
  addresses. It is cubic and has no bipartite operand graph (each row reads all
  three tracks), so neither 09-08 criterion covers it.

## 3. Where the theorem stops, sharply

Each hypothesis of Theorem 2.1 marks a boundary of the conjecture. Under
Theorem 2.3 the boundaries (B2) and (B3) are crossed only by offsets or
own-block nonlinearity that survive with the earlier blocks set to zero, in
every ordering of the blocks.

- **(B1) The constant own part must be invertible.** Without that hypothesis,
  a single block with constant controllers gives `F = I + A`, an arbitrary
  linear automaton on `(R^d)^G`. The extension then contains the stable
  finiteness question for `R[G]`, which is open in general.
- **(B2) No pure-others offsets.** Allow each row an additive term
  `beta_a(others)`, even a linear one, while keeping constant own coefficients
  `+1` and `-1`. The recipient-affine normal form
  `H(x,u) = (x + u, F(x) - x - u)` lies in this extension:
  - the `x` row has own coefficient `1` and offset `u`;
  - the `u` row has own coefficient `-1` and offset `F(x) - x`;
  - `H` is stably equivalent to an arbitrary `F`.

  So the extension is universal, and the offsets carry the entire conjecture.
  Removing an offset by the shear `(X,Y) -> (X + beta(Y), Y)` only moves it
  into the other block's zero fiber. In `H` that fiber is `u -> F(-u)`, a copy
  of the unknown map (recipient-affine artifact, section 3).
- **(B3) No own-block nonlinearity.** Allow terms with two factors from the
  row's own block. The same-track control
  `x(g) + x(g)x(gt) + x(gt)x(gt^2)`, with `t` of order three, is bijective and
  nonlinear. On `Gamma x C_3`, surjunctivity of `x + A Q_t(x)` is equivalent to
  direct finiteness of `F_2[Gamma]`
  (`central-c3-quadratic-surjunctivity-iff-direct-finiteness`). So own-block
  nonlinearity already contains the characteristic-two direct finiteness
  question.

## 4. Consequence for counterexample design

A strict injective automaton admits no stable reversible equivalence, no
block partition and no ordering satisfying Theorem 2.3. In every ordered
presentation of a counterexample, some row keeps, after the earlier blocks are
set to zero, a pure-others offset, an own-block nonlinearity, or a
non-invertible constant own part. The universal recipient-affine normal form
has an offset in its first row under both orderings, which is consistent with
its universality.

## 5. What this does not settle

The three-factor claim, the recipient-affine claim and Gottschalk's conjecture
remain open. Group by group, they are equivalent to one another.
