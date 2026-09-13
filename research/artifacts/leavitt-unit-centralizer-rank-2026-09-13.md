# Centralizer rank of binary Leavitt units: a second obstruction to Heisenberg and Baumslag--Solitar subgroups

Lane `ex-q34-unit-depth`, 2026-09-13. Companion to
`research/artifacts/leavitt-unit-depth-growth-lemmas-2026-09-13.md`.

Notation. `R = L_(F_2)(1,2)`, `Q = R^x`. For `u in Q` of infinite order, `F_2[u]` is a polynomial ring, since
`p(u) = 0` would make `F_2[u^(+-1)]` finite-dimensional and `u` of finite order. Put `C_u = C_R(u)`, the
centralizer algebra, and `S_u = F_2[u] - {0}`, a multiplicative set central in `C_u`. Define the
**centralizer rank**

```text
rho(u) = dim_(F_2(u)) S_u^(-1) C_u   in  {1, 2, ..., ∞}.
```

It is at least `1`, because `1` is not `S_u`-torsion (`p(u) != 0` in `R`). Elements killed by some `p(u)`,
for instance the parts of `R` on which `u` has finite order, do not count.

## 1. Heisenberg centers have infinite centralizer rank

**Proposition 5.** Let `a, b in Q` be such that `c = aba^(-1)b^(-1)` commutes with `a` and `b` and has infinite
order. Then:
- (i) `rho(c) = ∞`;
- (ii) the group algebra `F_2[H_3(Z)]` embeds in `R`.

Conversely, a unital embedding of `F_2[H_3(Z)]` sends group elements to units and so gives `H_3(Z) <= Q`. So `Q`
contains `H_3(Z)` iff `F_2[H_3(Z)]` embeds in `R`.

*Proof of (i).*
- `a`, `b` and their inverses lie in `C_c`, and `c` is central in `C_c`. So `A = S_c^(-1) C_c` is a nonzero
  `F_2(c)`-algebra, and `a, b` are units of `A` with `ab = c ba`.
- Suppose `n = dim_(F_2(c)) A` is finite. The left multiplications `L_a, L_b` are invertible
  `F_2(c)`-linear maps of `A` with `L_a L_b = c L_b L_a`.
- Taking determinants gives `det L_a det L_b = c^n det L_b det L_a`, so `c^n = 1` in the field `F_2(c)`.
- This contradicts `n >= 1`, since `c` is transcendental. ∎

*Proof of (ii).*
- `H = H_3(Z) = <x, y | [x,y] central>`, with center `<z>`, `z = [x,y]`. The algebra `F_2[H]` is free over
  `F_2[z^(+-1)]` on the monomials `x^i y^j`.
- Its localization `T = F_2(z) ⊗ F_2[H]` is the quantum torus `F_2(z)< x^(+-1), y^(+-1) | xy = z yx >`.
- **`T` is simple.** Let `I != 0` be an ideal and `f in I` nonzero with the fewest monomials.
  - `x y^j x^(-1) = z^j y^j`. So if `f` has monomials `x^i y^j` with two different `j`, then
    `x f x^(-1) - z^(j_0) f` is nonzero, lies in `I`, and has fewer monomials.
  - So all monomials of `f` share one `j`, and symmetrically (`y x y^(-1) = z^(-1) x`) one `i`.
  - Then `f` is a monomial, hence a unit, and `I = T`.
- Map `F_2[H] -> R` by `x -> a`, `y -> b`. It lands in `C_c` and sends `z` to `c`.
- Localize at `F_2[z] - {0}`. This gives a unital map `T -> S_c^(-1) C_c`, which is injective because `T` is
  simple and the target is nonzero.
- `F_2[H] -> T` is injective, since `F_2[H]` is free over `F_2[z^(+-1)]`. So `F_2[H] -> C_c -> S_c^(-1) C_c` is
  injective, and so is `F_2[H] -> R`. ∎

## 2. Baumslag--Solitar bases have infinite centralizer rank

**Proposition 6.** If `t x t^(-1) = x^k` in `Q` with `|k| >= 2` and `x` of infinite order, then `rho(x) = ∞`.

*Proof.*
- Put `K = F_2(x^k) = F_2(x^(|k|))`, a subfield of `F_2(x)` of index `|k|`.
- Conjugation by `t` is a ring isomorphism `C_x -> C_(x^k)` carrying `x` to `x^k`. So
  `dim_K K ⊗_(F_2[x^k]) C_(x^k) = rho(x)`.
- `C_x <= C_(x^k)` is an `F_2[x^k]`-submodule, and localization is exact, so `dim_K K ⊗ C_x <= rho(x)`.
- `F_2[x]` is integral over `F_2[x^(|k|)]`, and every nonzero `p(x)` divides its norm, which lies in
  `F_2[x^(|k|)] - {0}`. So localizing `C_x` at `F_2[x^(|k|)] - {0}` already inverts `S_x`, and
  `K ⊗ C_x = S_x^(-1) C_x`, of `K`-dimension `|k| rho(x)`.
- So `|k| rho(x) <= rho(x)` with `rho(x) >= 1`, which forces `rho(x) = ∞`. ∎

## 3. Examples and data

- **North--south unit.** For `c = s_00 t_0 + s_01 t_10 + s_1 t_11`, `C_R(c^a) = F_2[c^(+-1)]`
  (`leavitt-north-south-thompson-unit-has-cyclic-centralizer`), so `rho(c) = 1`.
- **Diagonal copies.** `phi(x) = s_0 x t_0 + s_1 x t_1` identifies with `diag(x,x)` under `R ≅ M_2(R)`, so
  `C_R(phi(c)) = M_2(F_2[c^(+-1)])` and `rho(phi(c)) = 4`. Likewise `rho(phi^j(c)) = 4^j`.
- **Exact computation (MSI, `centralizer_dim.py` in `/projects/standard/hsiehph/sauer354/ex/ex-q34-unit-depth/`).** For several infinite-order units
  `u`, `dim(C_R(u) ∩ R_N)` was computed by exact linear algebra for `N = 1..4` (basis sizes 8, 40, 176, 736).

| unit | depth | `N = 4`: `dim C ∩ R_4` | powers of `u` in `R_4`, span |
| --- | --- | --- | --- |
| `A` (Thompson `0,10,11 -> 00,01,1`) | 2 | 7 | 7 |
| `ACB` | 3 | 9 | 9 |
| `UZ` | 2 | 7 | 7 |
| `AYPUw` | 2 | 7 | 7 |
| `phi(A)` | 3 | 20 | 5 |

  So for these units the centralizer at depth `<= 4` is exactly the span of the powers, consistent with
  `rho = 1`, and `phi(A)` shows the expected factor 4. The finite-order units `X` and `P` have centralizers of
  dimensions 304 and 208 in `R_4`.
- **Excess screen (MSI, `cen_screen.py`, seeds 21–26).**
  - Setup: 500 draws each, words of length 2–12 in the thirteen generators of the squaring screen, `N = 3`.
  - Units with `u^m = 1` for some `m <= 64` were discarded (317). Of the 2584 remaining, 218 (8%) have
    `dim(C_R(u) ∩ R_3)` larger than the span of their powers in `R_3`.
  - Probed with `N = 2..5`: `ZnRRpzpb`, `qbb`, `mmbzQ` and `Qb`. Their excess grows like the basis,
    `dim C ∩ R_N = 18, 109, 505` for `ZnRRpzpb` against basis sizes `176, 736, 3008`. Each has doubling depth
    along squares, and no order `<= 128` was detected.
  - `qbb` and `Qb` are the identity on the cylinder `[00]`. Their excess contains the corner `s_00 R t_00`,
    which is `F_2[u]`-torsion and does not count toward `rho`. For the other two no fixed cylinder of length
    `<= 3` was found.
  - **Torsion analysis (`rank_probe.py`).** Take a basis `z_1..z_d` of `C_R(u) ∩ R_3`, and record
    `dim span{ u^i z_k : i <= j }` for `j = 0..12`. For a module of rank `r` the increments tend to `r`.
    - Controls: `A` gives increments 1, `phi(A)` gives increments 4.
    - Eight excess units (`ZnRRpzpb`, `qbb`, `mmbzQ`, `yAam`, `PN`, `my`, `yxNW`, `BYxam`) all give
      increments exactly 1 at every step.
    - Most excess basis vectors have a `u`-orbit span that stabilizes, and so are `F_2[u]`-torsion. Examples:
      17 of 18 for `ZnRRpzpb` and 21 of 23 for `mmbzQ`.
    - `ZnRRpzpb` and `mmbzQ` have no `u`-invariant diagonal idempotent at level 5
      (`block_probe.py`: one invariant atom). So the torsion does not come from a finite-order block on an
      invariant cylinder set. It comes from non-diagonal commuting elements on which `u` has finite order.
  - **Reading.** Every excess centralizer found is torsion over `F_2[u]`, and every sampled unit has rank-1
    behaviour at depth 3. No unit with centralizer rank above 1 was found, except the diagonal copies
    `phi^j`.

## 4. The resulting reduction

A Heisenberg center or a `BS(1,k)` base in `Q` must satisfy both
- `lambda(c) = 0`, sublinear depth growth; and
- `rho(c) = ∞`, a centralizer containing infinitely many `F_2[c]`-independent elements.

Either of the open claims below excludes both subgroups.
- `leavitt-units-of-infinite-order-have-linear-depth-growth`: `lambda > 0`.
- `leavitt-unit-centralizers-have-finite-rank`: `rho < ∞`.

They are independent in form. The second is purely algebraic. By the torsion analysis of Section 3, the
excess centralizers seen at small depth are torsion and do not test it.
