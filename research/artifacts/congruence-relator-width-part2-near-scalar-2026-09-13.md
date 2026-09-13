# Congruence relator width, part 2: near-scalar residue tuples

Lane `ex2-weak-sofic-affine-targets`, 2026-09-13. Unreviewed. Notation from part 1
(`research/artifacts/congruence-relator-width-part1-hensel-2026-09-13.md`): `R` is a finite chain ring
with `m = pi R`, residue field `F_q` and `m^k = 0`; `Q = SL_n(R)`; `Z_T` is the group of Teichmueller
scalars; `Cons_K = Cons_K^Q(R(a))`.

**Case N.** `G = <X | R>` is an infinite finitely presented simple group that is not linear sofic over
finite fields, with uniform collapse constant `delta_0 <= 1`. `n >= D`, and
`1 <= P = max_x rho(abar_x) < n/(c_5 |X|)`. The constants `c_6`, `c_5 = 4 c_6` and `D` are fixed in
Section 5.

**The obstacle.** When every residue is near-scalar, no product of boundedly many relator conjugates
has a residue far from the scalars, so the Hensel lemma of part 1 cannot be applied in `SL_n(R)`. The
kernel parts of the generators can still have full rank at every level. What rescues the argument: the
big block of the kernel parts is an approximate homomorphism into a `p`-group. Its defects have rank at
most `d_0` per multiplication, and they do not grow along conjugators.

## 0. Rank over `R`

For a matrix `M` over `R`, let `rk M` be the least number of generators of `im M`. `R` is a principal
ideal ring with Smith normal form, so every submodule of an `s`-generated module is `s`-generated.
- (R1) `rk(M + M') <= rk M + rk M'`.
- (R2) `rk(M M') <= min(rk M, rk M')`.
- (R3) a map into or out of a free module of rank `d` has `rk <= d`.
- (R4) if `M` is invertible and `rk E <= e`, then `(M + E)^-1 = M^-1 + E'` with `rk E' <= e`, since
  `E' = -M^-1 E (M + E)^-1`.

## 1. Localizing the residues and lifting

- **Nearest scalars.** Choose `lambda_x in F_q^x` with `rk(abar_x - lambda_x) = rho(abar_x)`, put
  `bbar_x = lambda_x^-1 abar_x` and `b_x = lambda~_x^-1 a_x in GL_n(R)`. For every word, `u(a) = lambda~_u u(b)`
  with `lambda~_u = prod_x lambda~_x^(e_(u,x))` central.
- **Residue localization.** Section 5.2 of `simple-group-psl-width-is-finite-field-linear-soficity-proof`
  gives `F_q^n = Wbar (+) Wbar'` with `1 <= d_0 = dim Wbar <= 2|X| P`, and every word in `bbar` lies in
  `GL(Wbar) x 1`.
- **Lift.** Lift an adapted basis, so `R^n = W~ (+) W~'`. Put
  `E = {g in GL_n(R) : gbar in GL(Wbar) x 1}`, a subgroup containing every `b_x`.
- **Blocks.** Write `g in E` as `[[A_g, B_g], [C_g, D_g]]` with `Bbar = 0`, `Cbar = 0` and `Dbar = 1`. Put
  `psi(g) = D_g`, an element of the finite `p`-group `N = {D in GL(W~')(R) : Dbar = 1}`.

## 2. The big block is an approximate homomorphism

**Lemma 2.1.**
- (a) For `g, g' in E`, `psi(g g') = psi(g) psi(g') + C_g B_(g')`, and `rk(C_g B_(g')) <= d_0`.
- (b) `psi(g^-1) = psi(g)^-1 + E` with `rk E <= d_0`.
- (c) If `c in E` is block diagonal, `psi(c g c^-1) = D_c psi(g) D_c^-1` exactly.
- (d) For `g_1, ..., g_L in E`, `psi(g_1 ... g_L) = psi(g_1) ... psi(g_L) + E` with `rk E <= (L - 1) d_0`.

*Proof.*
- (a) Block multiplication. `C_g` maps out of `W~`, which is free of rank `d_0` (R3, R2).
- (b) Apply (a) to `g · g^-1 = 1`: `psi(g^-1) = psi(g)^-1 (1 - C_g B_(g^-1))`.
- (c) Block-diagonal conjugation preserves the blocks.
- (d) Induction, with (R1) and (R2).

**Corollary 2.2.** Put `D = (psi(b_x))_x in N^X`. For a word `w` of length `|w|`,
`psi(w(b)) = w(D) + E` with `rk E <= 2|w| d_0`.

*Proof.* Each letter contributes `psi(b_x^(+-1)) = D_x^(+-1) + (rk <= d_0)` by (b), and (d) adds
`(|w| - 1) d_0`. Products of perturbed factors differ from the product by rank at most the sum (R1, R2).

## 3. Matching the big block with the nilpotent template

Let `l = max_r |r|`, and for `u in F(X)` let `K(u) = sum_r |n_(u,r)| + 2|R|` be the constant of
`perfect-group-relator-width-over-nilpotent-groups` for `e_u = sum_r n_(u,r) e_r`.

**Lemma 3.1.** For every word `u` there are block-diagonal `c_i in E ∩ SL_n(R)` and the fixed pattern
`(r_i, eps_i)`, `i <= K(u)`, such that
```text
P_u := prod_i c_i r_i(a)^(eps_i) c_i^-1  in  Cons_(K(u)),     rho_u := P_u^-1 u(a)  in  E ∩ SL_n(R),
psi(rho_u) = 1 + E_u ,   rk E_u <= c(u) d_0 ,   c(u) = K(u)(2l + 2) + 2|u| + 2 .
```

*Proof.*
- **Template in `N`.** `N` is nilpotent. The nilpotent theorem's identity for the element `x = u` holds
  modulo `gamma_(c+1)(F)` with `c` the class of `N`. Evaluated at the tuple `D`, it gives
  `u(D) = prod_i d_i r_i(D)^(eps_i) d_i^-1` with `d_i in N`. The pattern has exponent sum `e_u`.
- **Conjugators.** Let `c_i` be `diag(det(d_i)^-1, 1, ..., 1)` on `W~` (in the lifted basis, `d_0 >= 1`) and
  `d_i` on `W~'`. Since `det d_i in 1 + m`, `cbar_i = 1`, `c_i in SL_n(R)`, and `c_i` is block diagonal
  with `D_(c_i) = d_i`.
- **Scalars.** `r_i(a) = lambda~_(r_i) r_i(b)`, and `prod_i lambda~_(r_i)^(eps_i) = lambda~_u` because the
  pattern has exponent sum `e_u`. So `rho_u = (P_u^b)^-1 u(b)` with `P_u^b = prod_i c_i r_i(b)^(eps_i) c_i^-1 in E`.
- **The block of `P_u^b`.** By Lemma 2.1(c), each factor has `psi = d_i psi(r_i(b)^(eps_i)) d_i^-1`. By
  Corollary 2.2, (b) and (R4), `psi(r_i(b)^(eps_i)) = r_i(D)^(eps_i) + (rk <= (2l + 1) d_0)`. With (d),
  `psi(P_u^b) = u(D) + E_1`, `rk E_1 <= K(u)(2l + 2) d_0`.
- **The remainder.** `psi(u(b)) = u(D) + E_2` with `rk E_2 <= 2|u| d_0`. By (a), (b) and (R4),
  `psi(rho_u) = (u(D) + E_1)^-1 (u(D) + E_2) + (rk <= 2 d_0) = 1 + E_u`.
- `rho_u in SL_n(R)` because `u(a)` and `P_u` are.

## 4. The remainders and the seed are localized

**Lemma 4.1.** If `g in E` and `psi(g) = 1 + E_D` with `rk E_D <= e`, then `rk(g - 1) <= e + 2 d_0`.

*Proof.* `im(g - 1) <= W~ + im [C_g  E_D]`, which is generated by `d_0 + d_0 + e` elements.

**Lemma 4.2 (displacement over `R`).** Item 3 of Section 0 of the PSL proof, for the tuple `bbar`, gives a
relator `r*` with `t = rk(r*(bbar) - 1) >= delta_0 P`. Also `t <= d_0`.
- Choose `Wbar_1 <= Wbar'` of dimension `d_0` (`n >= 2 d_0`), and lift to `W~_1`. Identify `W~` and `W~_1`
  through the lifted bases.
- Let `y` act as `[[0, -I], [I, 0]]` on `U_a = W~ (+) W~_1` and as `1` on the lifted complement `U_b`. Then
  `y in SL_n(R)`, and `h = [r*(a), y] in Cons_2`.

Then:
- (i) `hbar = r*(bbar)|_(Wbar) (+) sigma r*(bbar)|_(Wbar)^-1 sigma^-1 (+) 1`, with `rk(hbar - 1) = 2t`
  (Section 5.4 of the PSL proof);
- (ii) `rk(h - 1) <= 6 d_0`.

*Proof of (ii).* Scalars cancel, so `h = g y g^-1 y^-1` with `g = r*(b)`. In blocks for `U_a (+) U_b`, write
`g = [[alpha, beta], [gamma, delta]]` and `g^-1 = [[alpha', beta'], [gamma', delta']]`, and `y = z (+) 1`.
- The `(U_b, U_b)` block of `h` is `gamma z beta' + delta delta'`. Since `gamma beta' + delta delta' = 1`, it
  equals `1 + gamma (z - 1) beta'`, of rank at most `rk gamma <= 2 d_0`.
- The rows into `U_a` have rank at most `2 d_0`, and so does the `(U_b, U_a)` block.

So the displacement of Lemma 5.3 does double duty over `R`: it moves the relator's residue off itself,
and it cancels the relator's big block except for rank `2 d_0`.

**Lemma 4.3 (common localization).** Let `e_1, ..., e_s in GL_n(R)` with `sum_i rk(e_i - 1) <= f`. Then
`R^n = A~ (+) B~` with `A~`, `B~` free, `rank A~ <= 2f`, every `e_i` the identity on `B~`, and `e_i A~ <= A~`.

*Proof.*
- **Common kernel.** The stacked map `(e_i - 1)_i` has rank `<= f`. By Smith normal form it vanishes on
  a free summand `U_0` of corank `<= f`. Let `C_0` be a free complement.
- **Common image.** `I = sum_i im(e_i - 1)` is `f`-generated, so `I + C_0` is `2f`-generated. By Smith
  normal form it lies in a free summand `A~` of rank `<= 2f`.
- **Complement.** Since `C_0 <= A~`, the modular law gives `A~ = C_0 (+) (A~ ∩ U_0)`. So `M = A~ ∩ U_0` is a
  summand of `R^n` inside `U_0`. With `R^n = M (+) M'`, put `B~ = M' ∩ U_0`, so `U_0 = M (+) B~`.
  - `A~ + B~ ⊇ C_0 + U_0 = R^n`, and `A~ ∩ B~ <= M ∩ B~ = 0`.
  - Summands of free modules over a local ring are free.
- **Action.** `e_i` fixes `B~ <= U_0` pointwise, and `e_i(x) = x + (e_i - 1)x in A~ + I = A~` for `x in A~`.

## 5. Covering inside `SL(A~)`

Fix template words `u, v`. Apply Lemma 3.1 to `u` and `v`, and Lemma 4.2 for `h`.
- **Localize.** By Lemma 4.1, `rk(rho_u - 1) + rk(rho_v - 1) + rk(h - 1) <= f := (c(u) + c(v) + 10) d_0`.
  Let `c_6` be the maximum of `c(u) + c(v) + 10` over template pairs. Lemma 4.3 gives `A~` of rank `<= 2f`.
  Enlarge it by part of `B~` to rank `d' = max(2f, D)`. This needs `d' <= n`, which follows from
  `2f <= 4 c_6 |X| P < n` with `c_5 = 4 c_6`.
- **Restrictions.** `rho_u`, `rho_v` and `h` have determinant `1` and are the identity on `B~`. So their
  restrictions lie in `SL(A~) ≅ SL_(d')(R)`.
- **The seed is proportional in `A~`.**
  - `hbar = 1` on `Bbar`, so `rk(hbar|_(Abar) - 1) = 2t <= 2 d_0 <= d'/4`. The fixed space has dimension
    `>= d'/2`, so `rho(hbar|_(Abar)) = 2t`.
  - If `d' = 2f`, then `P >= d'/(4 c_6 |X|)` and `2t d' >= delta_0 d'^2/(2 c_6 |X|)`.
  - If `d' = D`, then `2t d' >= 2 delta_0 d'^2/D`.
  - Either way `2t d' >= eta'' d'^2` with `eta'' = delta_0/(2 c_6 |X| D)`.
- **Residue covering.** Take `D >= 16 c_6 |X|/delta_0`, so `eta'' D^2 >= 8`. By (2.1) of the PSL proof,
  `log|Sbar| >= (eta''/2) d'^2 log q`. Liebeck--Shalev gives `Sbar^(k_2) = PSL_(d')(q)` with
  `k_2 = ceil(2c/eta'')`.
- **Kernel covering.** Proposition 4.1 of part 1 in `SL_(d')(R)`, with conjugators in `SL(A~) x 1 <= Q`,
  gives `rho_u|_(A~) = z_u p_u` with `z_u` central in `SL(A~)` and `p_u in Cons_(5 k_2)(h)`. The same holds
  for `v`.
  - `[rho_u, rho_v]` is computed inside `SL(A~) x 1`, where `z_u (+) 1` is central.
  - So `[rho_u, rho_v] = [p_u, p_v] in Cons_(10 k_2)(h) <= Cons_(20 k_2)`.
- **Template commutator.** Use `[xy, w] = x [y, w] x^-1 · [x, w]` and `[y, zw] = [y, z] · z [y, w] z^-1`:
  ```text
  [P_u rho_u, P_v rho_v] = P_u ( [rho_u, P_v] · P_v [rho_u, rho_v] P_v^-1 ) P_u^-1 · [P_u, P_v rho_v] .
  ```
  Here `[P_u, ·] in Cons_(2K(u))` and `[rho_u, P_v] in Cons_(2K(v))`. So
  `[u(a), v(a)] in Cons_(2K(u) + 2K(v) + 20 k_2)`.

## 6. Assembly and what transferred

**Width bound.** With parts 1 and 2, every template commutator lies in `Cons_M` with
`M = max(20cD^2, 10 k_1, 2K(u) + 2K(v) + 20 k_2)`. The small-field constant `K(G, D)` and Case S bound `a_x`
directly. So `w_Q(a) <= max(K(G, D), max_x K(x), J M + J')`, independent of `n`, `q`, `k` and `R`.

**Transfer checklist from the classical covering lane.**
- *Displacement (Lemma 5.3 there).* Transfers verbatim over `R`, and cancels the big block (Lemma 4.2(ii)).
- *Commutator rank choice.* Unnecessary for `SL`. The residue step uses Liebeck--Shalev directly, and the
  kernel uses two Singer tori (part 1).
- *Greedy counts (Lemma 4.2 there).* Not used. Isometry groups over chain rings would need a Singer-type
  pair in the isometry Lie algebra with trivial common centralizer. Not written.
- *The abelian normal subgroup.* At level 1 the big block is an honest homomorphism, matched by exponent
  sums. At all levels it is matched by the nilpotent template in `N` with block-diagonal conjugators,
  whose defects cost rank `<= d_0` per multiplication and nothing per conjugator.
