---
rg: 2
id: thompson-f-b1-ramsey-witnesses-at-most-one-third-proof
kind: route
title: Reduce Moore's Ramsey condition for the unit ball to balancedness of realized picture collections, then settle radii 3 to 11 of F by DRAT-checked SAT for the upper bounds and explicit sets with exact rational duals for the lower bounds
target: thompson-f-b1-ramsey-witnesses-are-at-most-one-third
requires: []
artifacts:
  - experiments/ramsey-picture-sat-2026-09-17/groups.py
  - experiments/ramsey-picture-sat-2026-09-17/ramsey_sat.py
  - experiments/ramsey-picture-sat-2026-09-17/cegar.py
  - experiments/ramsey-picture-sat-2026-09-17/witness_dual.py
  - experiments/ramsey-picture-sat-2026-09-17/certify_upper.py
  - experiments/ramsey-picture-sat-2026-09-17/lower_bound.py
  - experiments/ramsey-picture-sat-2026-09-17/third_barrier.py
  - experiments/ramsey-picture-sat-2026-09-17/certify_barrier.py
  - experiments/ramsey-picture-sat-2026-09-17/barrier_core.py
  - experiments/ramsey-picture-sat-2026-09-17/certify_core.py
  - experiments/ramsey-picture-sat-2026-09-17/summarize.py
  - experiments/ramsey-picture-sat-2026-09-17/barrier_lp.py
  - experiments/ramsey-picture-sat-2026-09-17/barrier_lp_third_F_n7-11.json
  - experiments/ramsey-picture-sat-2026-09-17/barrier_lp_third_F2_n2-10.json
  - experiments/ramsey-picture-sat-2026-09-17/families_closed_k5.json
  - experiments/ramsey-picture-sat-2026-09-17/cegar_F_n3.json
  - experiments/ramsey-picture-sat-2026-09-17/cegar_F_n7.json
  - experiments/ramsey-picture-sat-2026-09-17/cegar_F_n10.json
  - experiments/ramsey-picture-sat-2026-09-17/cegar_F2_n3.json
  - experiments/ramsey-picture-sat-2026-09-17/certify_F_n3.json
  - experiments/ramsey-picture-sat-2026-09-17/certify_F_n7.json
  - experiments/ramsey-picture-sat-2026-09-17/lower_bound_F_n6_fam88.json
  - experiments/ramsey-picture-sat-2026-09-17/lower_bound_F_n2_fam2.json
  - experiments/ramsey-picture-sat-2026-09-17/families_k5.json
  - experiments/ramsey-picture-sat-2026-09-17/third_barrier_F_n6-11.json
  - experiments/ramsey-picture-sat-2026-09-17/certify_barrier_F_n11.json
  - experiments/ramsey-picture-sat-2026-09-17/barrier_core_F_n11.json
  - experiments/ramsey-picture-sat-2026-09-17/certify_core_F_n11.json
---

Notation as in `thompson-f-b1-ramsey-witnesses-are-at-most-one-third`. `A = B_1` is listed in the fixed
order `(e, x_0, x_0^{-1}, x_1, x_1^{-1})`, and a picture `P ⊆ A` is stored as a 5-bit mask.
For `E ⊆ B_n`, `Y_E = {X_E(g) : g ∈ I_n}` is the realized collection. For a collection `Y`,
`bal(Y) = min{max_a v_a − min_a v_a : v = Σ_{P ∈ Y} λ_P 1_P, λ ∈ P(Y)}`.

## Step 1. The Ramsey condition is balancedness of realized pictures

Moore's definition is quoted verbatim in `moore-ramsey-criterion-for-amenability`. It asks, for each
`E ⊆ B`, for some `ν ∈ P(B)` with the following two properties:
- `P(A)ν ⊆ P(B)`. Taking `μ = δ_a` for each `a`, this says exactly `supp ν ⊆ I = {g : Ag ⊆ B}`.
- `|μν(E) − μ′ν(E)| ≤ ε` for all `μ, μ′ ∈ P(A)`.

Write `v_a = δ_a ν(E) = Σ_g ν(g) [ag ∈ E] = Σ_g ν(g) 1_{X_E(g)}(a)`. Then `μν(E) = Σ_a μ_a v_a`, so the second
condition is `max_a v_a − min_a v_a ≤ ε`.
- The push-forward `λ` of `ν` under `g ↦ X_E(g)` is a probability vector on `Y_E` with `v = Σ λ_P 1_P`.
- Conversely, given `λ ∈ P(Y_E)`, pick for each `P` one `g_P ∈ I` with `X_E(g_P) = P`. Then
  `ν = Σ λ_P δ_{g_P}` is supported on `I` and has the same `v`.

Hence `B_n` is ε-Ramsey w.r.t. `B_1` iff `bal(Y_E) ≤ ε` for every `E ⊆ B_n`. So
`ρ_G(n) = max_{E ⊆ B_n} bal(Y_E)`, a maximum over finitely many LPs, attained.

**Duality (used for lower bounds only in the easy direction).** For probability vectors `α, β` on `A` and
any `ν` as above,

`max_a v_a − min_a v_a ≥ Σ_a (α − β)_a v_a = Σ_g ν(g) (α − β)(X_E(g)) ≥ min_{P ∈ Y_E} (α − β)(P).`

So one `E` and one pair `(α, β)` with `min_{P ∈ Y_E} (α−β)(P) ≥ t` prove `ρ_G(n) ≥ t`.

**Monotonicity.** `ρ_G(n+1) ≤ ρ_G(n)` (monotonicity in `B`, recorded in the criterion node). The reason is
concrete here. For `g ∈ I_n ⊆ I_{n+1}` and `E ⊆ B_{n+1}`, the picture of `E ∩ B_n` at `g` equals that of `E`.

## Step 2. Exact group arithmetic and the balls

`groups.py` represents an element of `F` as its piecewise-linear homeomorphism of `[0,1]`, stored as the
tuple of breakpoints with `Fraction` coordinates. `_norm` deletes every point at which the slope does not
change, so the representation is the unique minimal breakpoint list, and equality of tuples is equality in `F`.
- The generators are `x_0` (breakpoints `(1/2,1/4), (3/4,1/2)`) and `x_1` (breakpoints `(1/2,1/2), (3/4,5/8), (7/8,3/4)`).
- The product is composition, `a·g = a ∘ g`. The opposite convention is the same group up to the inversion
  isomorphism `F → F^op`. Every `B_n` is inversion-closed, so `ρ_F` does not depend on the convention.
- `F_2` is reduced words with free reduction, and `Z^2` is the amenable control.

`ball` is breadth-first search. Its layers are the spheres, and `setup` lists `I_n` together with the index
row `(ag)_{a ∈ A}` of each `g ∈ I_n`.

**Sanity checks.**
- The sphere sizes of `F` for radii 0 to 11 are `1, 4, 12, 36, 108, 314, 906, 2576, 7280, 20352, 56664, 156570`.
- Through radius 4 they equal the free values `4·3^{r−1}`. Any relator has exponent sum zero in each generator,
  so it has even length. A nontrivial relator of length `2k ≤ 8` would identify two reduced words of length
  `k ≤ 4`, so `F` has no relator shorter than 10. The relator `[x_0 x_1^{-1}, x_0^{-1} x_1 x_0]` has length 10.
- It follows that the labelled Cayley balls of radius 4 of `F` and `F_2` are isomorphic: a non-tree edge would
  close a cycle of length at most 9. The picture instance at `n = 3` uses only `B_3` and the edges inside it,
  so the `n = 3` instances of `F` and `F_2` are identical up to renaming.
- `I_11` has 88257 elements, which is 4 more than `|B_10| = 88253`.

## Step 3. Upper bounds: the CEGAR list and its DRAT-checked final CNF

`cegar.py F n` builds a list `L` of picture collections `C`. The loop is only a search, and nothing it computes
in floating point is trusted. The certificate is the final list, which `certify_upper.py F n b` re-checks from
scratch as follows.

1. **Exact balance of each `C ∈ L`.** An LP optimum `λ` on `C` is rationalised and renormalised in `Fraction`.
   The script then checks exactly that `λ ≥ 0`, that `Σ λ = 1`, and that the coverage `v_a = Σ_{P ∋ a} λ_P` has
   `max v − min v ≤ b`. So `bal(C) ≤ b`. The exact `λ`'s are stored in `certify_F_n{n}.json` under `lambda_exact`.
2. **Covering CNF.** There is one variable `x_h` for each `h ∈ B_n` (meaning `h ∈ E`) and one variable `r_P` for
   each of the 32 masks.
   - *Base clauses.* For every `g ∈ I_n` and every `P`, the clause says "if the pattern of `(x_{ag})_a` is `P`,
     then `r_P`".
   - *Blocking clauses.* For every `C ∈ L`, the clause `∨_{P ∈ C} ¬r_P`.
3. **Soundness.** Suppose the CNF is UNSAT, and let `E ⊆ B_n`. Set `x = 1_E` and `r_P = [P ∈ Y_E]`. The base
   clauses hold, so some blocking clause fails, that is `C ⊆ Y_E` for some `C ∈ L`. A convex combination on `C` is
   one on `Y_E`, so `bal(Y_E) ≤ bal(C) ≤ b`. By Step 1, `ρ_F(n) ≤ b`.
4. **Checking UNSAT.** Glucose 4 (python-sat) solves the CNF once with proof logging. The empty clause `0` is
   appended to the trace, and `drat-trim`, built from source (github `marijnheule/drat-trim`, master), checks
   the DIMACS file against the trace. CaDiCaL's trace through python-sat omitted the final conflict and was
   rejected by `drat-trim`, so Glucose is used.

| run | `|B_n|` | `|I_n|` | `|L|` | bound `b` | clauses | `drat-trim` |
|---|---|---|---|---|---|---|
| `F`, `n = 3` | 53 | 17 | 930 | 1/2 | 1474 | VERIFIED |
| `F`, `n = 7` | 3957 | 1381 | 775 | 1/3 | 44967 | VERIFIED |
| `F`, `n = 8` | 11237 | 3957 | 684 | 1/3 | 127308 | VERIFIED |
| `F`, `n = 9` | 31589 | 11237 | 595 | 1/3 | 360179 | VERIFIED |

Only the `n = 3` and `n = 7` rows are needed. The other two are consistency checks.

## Step 4. Lower bounds: explicit sets with rational duals

`lower_bound.py` and `third_barrier.py` first ask the SAT solver for `E ⊆ B_n` whose pictures all lie in a
prescribed non-balanced family. They then **recompute `Y_E` from the model** by evaluating every row, and check
`min_{P ∈ Y_E} (α − β)(P) ≥ t` in `Fraction` arithmetic. The solver's answer is therefore only a proposal: the
certificate is the set `E` together with the exact check, and Step 1 (duality) turns it into `ρ ≥ t`.

- **`ρ_F(6) ≥ 1/2`** (`lower_bound_F_n6_fam88.json`). Here `α = (δ_{x_0^{-1}} + δ_{x_1})/2`,
  `β = (δ_{x_0} + δ_{x_1^{-1}})/2`, and `|E| = 823`. The realized masks are `{4, 5, 8, 9, 12, 13, 14, 15, 28, 29}`,
  and the exact minimum is `1/2`. The family is entry 88 of `families_closed_k5.json`.
- **`ρ_F(2) ≥ 2/3`** (`lower_bound_F_n2_fam2.json`; `lower_bound.py F 2 families_k5.json 2 501/1000`).
  Here `α = (δ_e + δ_{x_0} + δ_{x_0^{-1}})/3` and `β = δ_{x_1^{-1}}`, and `|E| = 9`. The realized masks are
  `{3, 6, 13}`, and the exact minimum is `2/3`. Since the radius-2 balls of `F` and `F_2` coincide (Step 2),
  the same holds in `F_2`.
- **`ρ_F(10) ≥ 1/3`** (`third_barrier_F_n6-11.json`, row `n = 10`). Here `w = α − β` with
  `α = (1/3)δ_{x_0^{-1}} + (2/3)δ_{x_1}` and `β = (1/3)δ_{x_0} + (2/3)δ_{x_1^{-1}}`. The family is
  `Y_w = {P : w(P) ≥ 1/3} = {4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 28, 29}`. `certify_core.py` asserts that this
  list is exactly the masks with `w(P) ≥ 1/3`, by checking all 32 cases. The run gives `|E| = 30736` and an exact
  minimum `w(P) = 1/3` over `Y_E`. The runs `n = 6, …, 9` are also SAT with exact minimum `1/3`.

## Step 5. The table for `F`

- `3 ≤ n ≤ 6`: `ρ_F(n) ≤ ρ_F(3) ≤ 1/2` by Step 3 and monotonicity, and `ρ_F(n) ≥ ρ_F(6) ≥ 1/2` by Step 4.
- `7 ≤ n ≤ 10`: `ρ_F(n) ≤ ρ_F(7) ≤ 1/3`, and `ρ_F(n) ≥ ρ_F(10) ≥ 1/3`.
- **Cross-checks, not used.** `cegar_F_n{3,5,6,7,8,9,10}.json` give exact upper bounds `1/2, 1/2, 1/2, 1/3, 1/3,
  1/3, 1/3` and floating lower bounds equal to them. The `n = 10` run took 577 iterations and 1049 s. On the
  control group `Z^2`, CEGAR gives `ρ ≤ 10^{-6}` at every radius `3 ≤ n ≤ 12`, as amenability predicts.

This proves item 1 of the claim.

## Step 6. `F_2`

- **Lower bound, by hand, at every radius.** Let `E` be the set of reduced words whose first letter is `b^{±1}`,
  `α` uniform on `{b, b^{-1}}`, and `β` uniform on `{a, a^{-1}}`. Let `g` be any element.
  - `g = e`: then `X = {b, b^{-1}}` and `(α−β)(X) = 1`.
  - `g = a^{η}u` (reduced, `η = ±1`): both `b^{±1}g` lie in `E`, `a^{η}g` does not, and `a^{-η}g = u` may.
    So `(α−β)(X) ≥ 1 − 1/2`.
  - `g = b^{η}u`: neither `a^{±1}g` lies in `E`, `b^{η}g` does, and `b^{-η}g = u` may. So `(α−β)(X) ≥ 1/2`.

  Hence `(α−β)(X_E(g)) ≥ 1/2` for all `g ∈ F_2`. Restricting `E` to `B_n` gives `ρ_{F_2}(n) ≥ 1/2` for all `n ≥ 1`
  by Step 1.
- **Upper bound.** For `n ≥ 3`, `ρ_{F_2}(n) ≤ ρ_{F_2}(3) = ρ_F(3) ≤ 1/2`. The middle equality holds because the
  `n = 3` instances coincide (Step 2). `cegar_F2_n3.json` is an independent run on the free-group
  instance, and its final list is identical to that of `cegar_F_n3.json`: 930 collections.

This proves item 2.

## Step 7. The consequence for global witnesses of `F`

Let `E ⊆ F` and `α, β ∈ P(B_1)`, and suppose `(α−β)(X_E(g)) ≥ c` for every `g ∈ F`. For `g ∈ I_7` the picture of
`E ∩ B_7` at `g` is `X_E(g)`. So by Step 1, every admissible `ν` for `E ∩ B_7` has spread at least `c`, and
`c ≤ ρ_F(7) ≤ 1/3`. Taking `c` to be the infimum proves item 3. The `F_2` example is Step 6.

## Step 8. The direction `w` dies at radius 11

- **`n ≤ 10`.** The `n = 10` model of Step 4, restricted to `B_n`, works for every `n ≤ 10` (Step 1, monotonicity).
- **`n = 11`, full instance** (`certify_barrier.py`, `certify_barrier_F_n11.json`). The CNF "`X_E(g) ∈ Y_w` for
  all `g ∈ I_11`" has one variable per element of `B_11` (244823) and `88257 × 20 = 1765140` clauses, one for
  each row and each of the 20 masks outside `Y_w`. It is UNSAT, and `drat-trim` reports VERIFIED on the
  Glucose trace.
- **Irreducible core** (`barrier_core.py`, then `certify_core.py`; `certify_core_F_n11.json`). A deletion-based
  shrinking gives 18 rows. Their `g` have lengths `4, 6×5, 8×8, 10×4`, and they touch 71 elements of lengths 3 to 11.
  - The 360 clauses of these 18 rows alone are UNSAT, which is DRAT-verified independently of the full instance.
  - Dropping any single row gives a SAT instance, and each such model is re-checked directly.

  So this finite configuration of 71 elements of `F` already forbids `w` at strength `1/3`.

This proves item 4. It excludes only this one `(α, β)`. Other directions at radius 11 are not examined, and
`ρ_F(11)` is not determined by this route.

## Step 9. The function version at radius 11

`barrier_lp.py F 7 11 third` sets `(Tf)(g) = 3 Σ_a w_a f(ag) = f(x_0^{-1}g) − f(x_0 g) + 2f(x_1 g) − 2f(x_1^{-1}g)`.
It then solves, in floating point, `min max f` subject to `f ≥ 0` on `B_n` and `Tf ≥ 1` on `I_n`.

The optimum is rationalised. The script checks `Tf ≥ 1` on every row of `I_11` in `Fraction` arithmetic, and the
rationalised `f` is nonnegative by construction. The record `barrier_lp_third_F_n7-11.json` gives
`max f = M = 3708337/3787234 < 1` at `n = 11`, while the LP optimum in floating point is `0.97917 ≈ 47/48`.

Put `f′ = f/M : B_11 → [0,1]`. Then `Σ_a w_a f′(ag) ≥ 1/(3M) = c_11` on `I_11`. Consider any `ν` with
`supp ν ⊆ I_11`, and write `aν(f′) = Σ_g ν(g) f′(ag)`. Then

`max_a aν(f′) − min_a aν(f′) ≥ Σ_a w_a aν(f′) ≥ c_11 > 1/3`.

This is the same duality as in Step 1, with `w = α − β`. So `B_11` fails Towsner's condition for `m = 1`,
`l = 1` and every `ε ≤ c_11`, and `R̃_{F,S}(1, ε) ≥ 12`. This proves item 5.

**Not used.** The same script on `F_2` gives exact optima `1/2, 2/3, 3/4, 5/6, 7/8, 11/12, 15/16, 23/24, 31/32`
for `n = 2..10`. The floating optima of `F` agree with these through `n = 10`.

## Step 10. Trust boundary and reproduction

**What must be trusted.**
- The group arithmetic in `groups.py` (`Fraction` breakpoints), BFS, and the row construction in `ramsey_sat.setup`.
- The CNF generators, which are a few lines each in `certify_upper.py`, `certify_barrier.py` and `certify_core.py`.
- The exact checks in `certify_upper.exact_check`, `lower_bound.main`, `third_barrier.py` and `barrier_lp.lp`.
- `drat-trim`.

**What need not be trusted.** Floating-point LPs (scipy/HiGHS) and the SAT solvers' SAT answers only propose
certificates, and each proposal is re-verified exactly. The large `.cnf` and `.drat` files are deleted after
checking; the commands below regenerate them.

```text
cd experiments/ramsey-picture-sat-2026-09-17
python3 cegar.py F 3; python3 cegar.py F 7; python3 cegar.py F2 3      # write cegar_*.json
python3 certify_upper.py F 3 1/2 DRAT_TRIM; python3 certify_upper.py F 7 1/3 DRAT_TRIM
python3 lower_bound.py F 6 families_closed_k5.json 88 1/2
python3 third_barrier.py F 6 11
python3 certify_barrier.py F 11 DRAT_TRIM
python3 barrier_core.py F 11; python3 certify_core.py F 11 DRAT_TRIM
python3 barrier_lp.py F 7 11 third
python3 lower_bound.py F 2 families_k5.json 2 501/1000
python3 summarize.py
```

Setting `RAMSEY_CACHE` to a scratch directory caches the balls. The balls of radius 10 and 11 take several
minutes each to build.
