# A linear invariant of the adjoint image, and the Klein target

Lane `gk-n-klein`, 2026-09-12. Supports the Cairn claims `ternary-adjoint-image-is-balanced`,
`klein-level-one-splitting-is-outside-adjoint-image`,
`klein-expectation-splits-in-balanced-algebra` and
`projective-ternary-level-two-klein-idempotent-is-full`. Builds on Sections 7 and 8 of
`invariant-output-descent-and-sensitivity-2026-09-12.md`.

## 1. Setup

`k = F_3`, `R = L_k(1,2)`, `G = R^x`, `PG = G/{±1}`, and `Q = R (x)_k R^op`, with product
`(a (x) b^op)(a' (x) b'^op) = a a' (x) (b' b)^op`. `Q` acts on `R` by `(a (x) b^op)(r) = a r b`.
Write `S[alpha] = s_(alpha_1)...s_(alpha_k)`, `T[beta] = t_(beta_l)...t_(beta_1)` and
`e_ij = s_i t_j`. For a prefix code `C`, `T[alpha] S[beta] = delta_(alpha beta)` when
`alpha, beta in C`. `C` is complete when `sum_(alpha in C) S[alpha] T[alpha] = 1`.

The adjoint evaluation `rho : k[PG] -> Q`, `rho([g]) = g (x) (g^-1)^op`, is a unital ring
homomorphism (Remark 7.5 of the cited artifact). It is well defined on `PG` because
`(-g) (x) (-g)^-1 = g (x) g^-1`.

Define linear maps `mu, mu' : Q -> R` by

```text
mu(a (x) b^op) = a b,        mu'(a (x) b^op) = b a.
```

`mu(T) = T(1)` is the invariant line of Lemma 8.3 there. `mu'` is new here.

## 2. The balanced invariant

**Theorem 1.** Every `T in rho(k[PG])` satisfies `mu(T) = mu'(T) = eps(T) 1`, where `eps` is the
augmentation.

*Proof.* `mu(g (x) g^-1) = g g^-1 = 1 = g^-1 g = mu'(g (x) g^-1)`. Both maps are linear. QED

**Lemma 2.** `N = {T in Q : mu(T) = mu'(T) in k 1}` is a unital subalgebra of `Q`, and
`T -> mu(T)` is a `k`-algebra character of `N`.

*Proof.* Put `T = sum a_i (x) b_i^op` and `T' = sum a'_j (x) b'_j^op`. Then
`TT' = sum a_i a'_j (x) (b'_j b_i)^op`, so

```text
mu(TT') = sum_i a_i mu(T') b_i = mu(T') mu(T),      mu'(TT') = sum_j b'_j mu'(T) a'_j = mu'(T) mu'(T')
```

whenever `mu(T')` and `mu'(T)` are scalars. `1 (x) 1` lies in `N`. QED

So `rho(k[PG]) <= N`. Any witness `b, c` of a corner equation in `k[PG]` has
`rho(b), rho(c) in N`.

## 3. The Klein expectation as a tensor

Let `w = e_01 + e_10`, `d = e_00 - e_11`, `wd = e_10 - e_01`, and let `K = <wbar, dbar> ~= C_2 x C_2`
in `PG`. Since `|K| = 4 = 1` in `k`, the averaging idempotent is `e_K = 1 + [wbar] + [dbar] + [wbar dbar]`.

**Proposition 3.** In `Q`,

```text
rho(e_K) = 2 (e_00 (x) e_00 + e_11 (x) e_11 + e_01 (x) e_10 + e_10 (x) e_01) = delta Psi,
delta = s_0 (x) t_0 + s_1 (x) t_1,        Psi = 2 (t_0 (x) s_0 + t_1 (x) s_1),
```

with op-superscripts omitted on the second factors. Also `Psi delta = 1 (x) 1`.

*Proof.* `w^-1 = w`, `d^-1 = d` and `(wd)^-1 = dw = -wd`. So

```text
rho(e_K) = (e_00 + e_11)^(x2) + (e_01 + e_10)^(x2) + (e_00 - e_11)^(x2) - (e_10 - e_01)^(x2),
```

where `x^(x2)` means `x (x) x^op`. Expanding and collecting gives coefficient `2` on `e_00 (x) e_00`,
`e_11 (x) e_11`, `e_01 (x) e_10` and `e_10 (x) e_01`, and `0` on the other eight.
`delta Psi = 2 sum_(i,j) s_i t_j (x) (s_j t_i)^op`, which is the same sum.
`Psi delta = 2 sum_(i,j) t_j s_i (x) (t_i s_j)^op = 2 sum_i 1 (x) 1 = 1 (x) 1`. QED

This verifies Proposition 8.4 of the cited artifact at the level of tensors, with no appeal to the
faithfulness of `Q` on `R`.

## 4. The one-level splitting fails the invariant

**Proposition 4.** Let `C` be a complete prefix code. Put `delta_C = sum_(alpha in C) S[alpha] (x) T[alpha]^op`
and, when `3` does not divide `|C|`, `Psi_C = |C|^-1 sum_(alpha in C) T[alpha] (x) S[alpha]^op`. Then:

- `mu(delta_C) = 1` and `mu'(delta_C) = |C| 1`;
- `mu(Psi_C) = 1` and `mu'(Psi_C) = |C|^-1 1`;
- `Psi_C delta_C = 1 (x) 1`.

So `delta_C`, respectively `Psi_C`, lies in `N` iff `|C| = 1 mod 3`. In particular
`delta = delta_({0,1})` and `Psi = Psi_({0,1})` satisfy `mu = 1`, `mu' = 2`, and neither lies in
`rho(k[PG])`.

*Proof.* Completeness gives `sum S[alpha] T[alpha] = 1`, and `T[alpha] S[alpha] = 1`. Also
`Psi_C delta_C = |C|^-1 sum_(alpha,beta) T[beta] S[alpha] (x) (T[alpha] S[beta])^op = |C|^-1 |C| 1 (x) 1`.
Theorem 1 finishes. QED

**Remark (operator level).** `R` is central simple over `k`, and a central simple algebra tensored
with a simple algebra is simple. So the action map `Q -> End_k(R)` is injective, and
Proposition 4 also says that the operators `delta` and `Psi` are not linear combinations of
conjugations `Ad(g)`, `g in PG`. Nothing below depends on this remark.

So the literal program "realize `delta Psi` in the span of the `Ad(g)`" dies. Neither factor of that
splitting is in the image.

## 5. The target survives: a balanced splitting at level two

**Proposition 5.** `delta^2 = delta_(C_2)` and `Psi^2 = Psi_(C_2)` for `C_2 = {00, 01, 10, 11}`. Both
lie in `N`, and

```text
Psi^2 rho(e_K) delta^2 = 1 (x) 1.
```

*Proof.* `delta^2 = sum_(i,j) s_i s_j (x) (t_j t_i)^op = sum_(|alpha| = 2) S[alpha] (x) T[alpha]^op`.
Likewise `Psi^2 = 4 sum T[beta] (x) S[beta]^op`, and `4 = 1`. Since `|C_2| = 4 = 1 mod 3`,
Proposition 4 puts both in `N`. `rho(e_K) delta^2 = delta (Psi delta) delta = delta^2`, and
`Psi^2 delta^2 = Psi (Psi delta) delta = 1 (x) 1`. QED

So the balanced invariant does not obstruct `projective-ternary-klein-idempotent-is-full`. Among
elements of the balanced algebra `N`, `rho(e_K)` is equivalent to `1`.

**Proposition 6 (the level-two Klein group).** Let `D = {sum_(|alpha|=2) eps_alpha S[alpha] T[alpha] : eps in {±1}^4}`
and `V_4 = {u_x = sum_(|alpha|=2) S[alpha xor x] T[alpha] : x in {0,1}^2}`. Let `K_4` be the subgroup
of `PG` they generate. Then:

1. `K_4 = Dbar x| V_4` has order `8 . 4 = 32`, and it contains `K`, since `w = u_(10)` and
   `d in D`.
2. `e_(K_4) = 2 sum_(k in K_4) [k]` is an idempotent with `e_(K_4) e_K = e_K e_(K_4) = e_(K_4)`.
3. `rho(e_(K_4)) = delta^2 Psi^2 = sum_(alpha,beta) S[beta] T[alpha] (x) (S[alpha] T[beta])^op`.

*Proof.* `V_4` permutes the level-two prefixes regularly and normalizes `D`, and `D` meets `V_4`
trivially. `D` contains `-1`, so `|Dbar| = 8`. `32 = 2 mod 3` is invertible, and `K <= K_4` gives
(2). For (3), the class average over `Dbar` is the average over `D`:

```text
(1/16) sum_eps d_eps (x) d_eps = sum_alpha e_(alpha alpha) (x) e_(alpha alpha),
```

because `(1/16) sum_eps eps_alpha eps_gamma = delta_(alpha gamma)`. Averaging over `V_4` then gives
`(1/4) sum_(x, alpha) e_(alpha xor x, alpha) (x) e_(alpha, alpha xor x) = sum_(alpha, beta) e_(beta alpha) (x) e_(alpha beta)`,
since `V_4` is regular and `1/4 = 1`. That tensor equals `delta^2 Psi^2`. QED

Since `e_(K_4) <= e_K`, fullness of `e_(K_4)` gives fullness of `e_K`: `(c e_(K_4)) e_K (e_(K_4) b) = c e_(K_4) b`.
The natural splitting of `rho(e_(K_4))` is `(delta^2, Psi^2)`, which is balanced. Its level-one
analogue `(delta, Psi)` is not. This is recorded as the open claim
`projective-ternary-level-two-klein-idempotent-is-full`.

## 6. What remains

- **Membership.** Do `delta^2` and `Psi^2`, or any pair `B, C in rho(k[PG])` with
  `C rho(e_K) B = 1 (x) 1`, lie in the adjoint image? No further linear invariant was found. The
  image contains `n (x) n^op` and `n (x) 1 - 1 (x) n^op` for every `n` with `n^2 = 0`, from
  `rho(1 + n) +- rho(1 - n)`, and it contains every product of these. For `R` there is no trace to
  give a `sl_n`-type invariant: `R = [R, R]` because `HH_0(L_k(1,2)) = k/(1 - 2)k = 0`. In the matrix
  analogue `M_n(k)` with `n` invertible, the span of `Ad(GL_n)` is exactly the balanced algebra.
- **The lift.** `rho` is not injective on `k[PG]`. The units `GL_2(k) <= R^x` (level-one matrices)
  give `24` classes in `PG`, whose images lie in the `16`-dimensional span of the `e_ij (x) e_kl`.
  So a splitting inside `rho(k[PG])` is necessary for the Klein target but not sufficient. Exact
  equality in `k[PG]` has to be arranged modulo `ker rho`, which is where direct finiteness does not
  pass back.
- **Screens that still bind** (Section 7 of the cited artifact):
  - supports must generate a nonamenable, non-locally-finite subgroup;
  - `PG` must not be `F_3`-linear sofic;
  - the forward table must have a nonsofic two-core.

**What this does not show.** It decides neither the Klein target nor the swap target, nor whether
`delta^2` lies in the adjoint image. It rules out one specific operator splitting and shows that a
balanced one exists.
