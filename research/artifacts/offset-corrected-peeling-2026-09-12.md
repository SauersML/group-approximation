# Offset-corrected peeling: where surviving offsets go

Date: 2026-09-12. Lane `gk-logic`, which absorbs the program of `gk-three-factor`.
Handwritten proofs; no computation.

`controlled-self-linear-feedback-ca-are-surjunctive` peels an injective automaton
block by block. It tolerates an offset in a row only when the offset vanishes
with the earlier blocks. This note shows where a surviving offset goes.

- If a row is linear in its own block with an invertible linear part for every
  value of the later blocks, solve the row for zero. That gives a local
  correction `X*(Y)`.
- The automaton is surjective exactly when its *corrected tail*, the later rows
  evaluated at `X*`, is surjective.
- Such steps mix with the steps of the peeling criterion. A mixed chain ending in
  a surjective tail proves surjectivity.

The universal recipient-affine normal form peels in one step of this kind, and its
corrected tail is a copy of the original automaton. So these steps are exact
reductions, never class theorems by themselves. Surjunctivity lives entirely in
the corrected tails.

## 1. Setting

- `G` is a group and `R` a finite ring.
- The tracks are grouped into blocks `X_1, ..., X_r`; block `a` has alphabet
  `R^(d_a)`. All maps are cellular automata on product full shifts.
- A *local function of `Y`* reads finitely many addresses of the blocks in `Y`,
  uniformly in position.

**Own-linear rows.** A row in block `X` with others `Y` is *own-linear* if

    row(X, Y)(g) = sum_(s in S) C_s(Y)(g) . X(g s) + beta(Y)(g),

with `S` finite, local `M_d(R)`-valued controllers `C_s`, and a local
`R^d`-valued offset `beta`. Write `L_Y X = sum_s C_s(Y) . X(. s)`.

**Step types.**
- **(O)** `E(X, Y) = (L_Y X + beta(Y), Y)` is bijective, which says every `L_Y`
  is bijective. By `nonlinear-certificate-fibers-are-all-surjective-or-all-strict`
  it suffices that `E` is injective and one `L_Y` is surjective. A concrete
  sufficient form: the controller at `s = 1` is `I + N_1(Y)`, the other
  controllers are `N_s(Y)`, and every `N_s(Y)(g)` is strictly upper triangular in
  one fixed flag. Then `N_Y = L_Y - I` satisfies `N_Y^d = 0`. The entries of
  `N_Y^k` are products of `k` strictly upper triangular matrices, which vanish for
  `k >= d`. So `L_Y^(-1) = sum_(k<d) (-N_Y)^k` is local, uniformly in `Y`. For a
  single track (`d = 1`) this is a pure shear row `X + beta(Y)`.
- **(Z)** `beta = 0` identically, and `L_0` is bijective.

The *correction* is `X*(Y)`, the first component of `E^(-1)(0, Y)`, in case (O),
and `X* = 0` in case (Z). It is local in both cases, by Curtis--Hedlund--Lyndon
in case (O).

The *corrected tail* of an automaton `F` on blocks `X, Y`, peeled at `X`, is the
automaton on `Y` given by the rows of the blocks in `Y`, evaluated at
`(X*(Y), Y)`.

## 2. The theorem

**Lemma 2.1 (two-block lemma, zero offset).** Let `F(X, Y) = (L_Y X, V(X, Y))` be
injective, with `v_0 = V(0, .)` surjective and `L_0` bijective. Then `F` is
surjective.

*Proof.* This is Lemma 2.2 of `three-factor-audit-and-controlled-feedback-2026-09-12.md`,
restated so this note is self-contained.
- If `L_Y X = 0`, choose `Y'` with `V(0, Y') = V(X, Y)`. Then `F(X, Y) = F(0, Y')`,
  so `X = 0`. Hence every `L_Y` is injective.
- `E(X, Y) = (L_Y X, Y)` is injective and has the bijective fiber `L_0`, so it is
  bijective by the certificate-fiber theorem.
- `F o E^(-1)` preserves its first coordinate, and its zero fiber is `v_0`, which is
  surjective. By the same theorem `F o E^(-1)` is surjective, hence so is `F`. QED

**Theorem 2.2 (offset-corrected peeling).** Let `F` be an injective automaton on
blocks `X_1, ..., X_r`, and put `F^(1) = F`. Suppose that for `a = 1, ..., r-1`,
row `a` of `F^(a)` is own-linear in `X_a`, with controllers and offset reading
only `X_(a+1), ..., X_r`, and of type (O) or (Z). Let `F^(a+1)` be the corrected
tail of `F^(a)` peeled at `X_a`. Then:
- every `F^(a)` is injective;
- if `F^(r)` is surjective, then `F` is surjective;
- if every step is of type (O), then `F` is surjective iff `F^(r)` is surjective.

*Proof.* Write `Y = (X_(a+1), ..., X_r)` and `E_a(X_a, Y) = (row_a(X_a, Y), Y)`.

- **Injectivity, type (O).** `E_a^(-1)(Z, Y) = (L_Y^(-1)(Z - beta(Y)), Y)`, so

      D_a = F^(a) o E_a^(-1) : (Z, Y) -> (Z, T_Z(Y)),

  where `T_Z(Y)` is the other rows of `F^(a)` evaluated at
  `(L_Y^(-1)(Z - beta(Y)), Y)`. `D_a` is an injective automaton that leaves `Z`
  unchanged, and its fiber `T_0` is `F^(a+1)`. So `F^(a+1)` is injective.
- **Injectivity, type (Z).** Row `a` vanishes at `X_a = 0`, so
  `F^(a)(0, Y) = (0, F^(a+1)(Y))` and `F^(a+1)` is injective.
- **Surjectivity passes up.** Assume `F^(a+1)` is surjective.
  - Type (O): `D_a` has the surjective fiber `T_0`, so it is surjective by the
    certificate-fiber theorem, and `F^(a) = D_a o E_a` is surjective.
  - Type (Z): Lemma 2.1 with `V(0, .) = F^(a+1)` makes `F^(a)` surjective.

  Downward induction from `F^(r)` gives surjectivity of `F = F^(1)`.
- **Surjectivity passes down at type (O).** If `F^(a)` is surjective, so is `D_a`.
  By the dichotomy every fiber of `D_a` is bijective, in particular
  `T_0 = F^(a+1)`. QED

**Recovered cases.**
- All steps of type (Z) with `F^(r) = L0_r` bijective: this is Theorem 2.3 of the
  audit artifact (`controlled-self-linear-feedback-ca-are-surjunctive`).
- All steps of type (O): an exact reduction of surjectivity to the last corrected
  tail.

## 3. The universal normal form peels to itself

Let `F` be any injective automaton and
`H(x, u) = (x + u, F(x) - x - u)` its recipient-affine normal form
(`affine-normal-form-reduces-three-factor-surjunctivity`).
- Peel at `x`. The row `x + u` is a pure shear row, type (O), with `beta(u) = u`,
  so `x* = -u`.
- The corrected tail is `u -> F(-u) - (-u) - u = F(-u)`.

So `H` is surjective iff `F` is. This turns the zero-fiber obstruction of the
recipient-affine artifact into an exact equivalence. Every automaton has a
presentation that peels completely in type-(O) steps. What the theorem cannot
supply is knowledge of the corrected tail, and that is where surjunctivity lives.

## 4. Consequences for the three-factor region

- **Offsets are not an obstruction by themselves.** A surviving offset in a row
  whose own-linear part is uniformly invertible can always be peeled. The
  remaining question is always the corrected tail, an automaton over the same
  group with fewer blocks.
- **Counterexample design.** In any presentation of a strict automaton that peels
  through steps (O) and (Z), the last corrected tail is strict too. By the
  certificate-fiber dichotomy, strictness also occurs at every constant value of
  every peeled certificate.
- **Where the peeling criterion stops.** Boundary (B2) of the audit artifact
  concerns offsets under type-(Z) steps. Under type (O) the offsets move into
  the tail. Boundary (B3), own-block nonlinearity, is untouched: an own-block
  quadratic row is not own-linear, and the central three-cycle family keeps its
  equivalence with direct finiteness.
- **Scope.** No new group is proved surjunctive. The three-factor claim, the
  recipient-affine claim and Gottschalk's conjecture remain open.
