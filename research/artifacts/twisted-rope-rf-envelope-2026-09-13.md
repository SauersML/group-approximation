# The compiler's twisted rope is a central rope over a fixed residually finite envelope

Lane `ex3-pfg-second-rope`, 2026-09-13. Unreviewed.

Target: the second, twisted rope of the positive branch of
`sofic-safe-finite-presentation-compiler`,

```text
R_e = < Gamma_e x Q_e, u | u(s,1)u^-1 = (s, tau_e(s)), s in S_e >,
S_e = <F, F^v> = F *_(N_e) F^v <= Gamma_e.
```

Result: on `INF` the associated isomorphism is inner in one explicit
residually finite group `R-hat`, independent of `e`. So `R_e` embeds in a
centralizing HNN extension over an isomorphic copy of `S_e`, which is a free
generalized wreath product over one coset action. That removes the twist as an
obstacle. What remains is soficity of that coset action (and of `Gamma_e`).

## 0. Data (INF branch)

From items 3--8 of `research/artifacts/mf-fp-pi2-unconditional-assembly-2026-08-26.md`
and `three-bridge-is-cyclic-fiber-product-with-finite-cep`:

- `P = F(x_1,y) x F(x_2,t)`, `chi(g_1,g_2) = exp_(x_1)(g_1) - exp_(x_2)(g_2)`,
  and `H = B3(1) = ker chi <= P` (BCF1). `P` is residually finite.
- `F = F(x,y,t)` and `q_+ : F ->> H`, `x -> (x_1,x_2)`, `y -> (y,1)`,
  `t -> (1,t)`, with kernel `N_+`. On `INF`, `N_e = N_+`, so `Q_e = H` and
  `q_e = q_+`.
- `K_e = K_e^0 x K^g` with `K^g = F x P`, `L_e = L_e^0 x L^g` with
  `L^g = {(f, q_+(f))}`, and `F` embedded diagonally, `f -> (i_e(f), (f,1))`.
- `Gamma_e = < K_e, v | [v, L_e] = 1 >`, `S_e = <F, vFv^-1>`, and
  `tau_e : S_e -> H` is `q_e` on `F` and trivial on `vFv^-1`.

## 1. The group-level fold map

Put `G-hat = (P x P) x| <sigma>`, where `sigma` swaps the coordinates. Define
`Lambda : Gamma_e -> G-hat` by

```text
Lambda(K_e^0) = 1,   Lambda(f,p) = (q_+(f), p)  for (f,p) in K^g,   Lambda(v) = sigma.
```

**Well defined.** On `K_e` it is a product of homomorphisms. For the relators
`[v,l]`, `l in L_e`: `L_e^0` maps to `1`, and `(f, q_+(f)) in L^g` maps to the
diagonal element `(q_+(f), q_+(f))`, which `sigma` centralizes.

**On the edge.** `Lambda(f) = (q_+(f), 1)` and
`Lambda(vfv^-1) = sigma (q_+(f),1) sigma = (1, q_+(f))`. So
`Lambda(S_e) <= H x H` and

```text
tau_e(s) = pr_1(Lambda(s))       for every s in S_e.                  (L1)
```

Both sides are homomorphisms `S_e -> H` that agree on the generating set
`F u vFv^-1`. The finite maps `lambda_n` of assembly item 8 are `r_n o Lambda`,
so (L1) is the group-level form of (RTS1).

## 2. The envelope

```text
R-hat = < G-hat x H, w | w(s-hat,1)w^-1 = (s-hat, pr_1 s-hat),  s-hat in H x H >.
```

It does not depend on `e`.

**(E1) `R-hat` is residually finite.** Write `B = G-hat x H`,
`A = (H x H) x 1`, `A' = {(s-hat, pr_1 s-hat)}`, and
`theta(s-hat,1) = (s-hat, pr_1 s-hat)`.

For a finite quotient `r : P -> C`, put `B_r = ((C x C) x| <sigma>) x r(H)` and

```text
pi_r((p_1,p_2)sigma^eps, q) = ((r p_1, r p_2)sigma^eps, r q).
```

Then `pi_r(A) = (r(H) x r(H)) x 1` and `pi_r(A') = {(c, pr_1 c)}`, and `theta`
descends to the isomorphism `theta_r(c,1) = (c, pr_1 c)`. So `pi_r` extends
to `R-hat -> R_r = HNN(B_r, theta_r)`. That is an HNN extension of a finite
group, so it is virtually free, and hence residually finite.

Let `x = b_0 w^(e_1) b_1 ... w^(e_k) b_k` be Britton-reduced. If `k = 0`,
separate `b_0` in the residually finite group `B`. If `k >= 1`, every interior
`b_i = ((p_1,p_2)sigma^eps, q)` avoids `A` (pattern `w b_i w^-1`) or `A'`
(pattern `w^-1 b_i w`). That means:

- `b_i notin A`: `eps = 1`, or some `p_j notin H`, or `q != 1`;
- `b_i notin A'`: `eps = 1`, or some `p_j notin H`, or `q != p_1`.

Take `r = (r', chi mod m) : P -> C' x Z/m`, where:

- `m` divides none of the finitely many nonzero values `chi(p_j)` that occur;
- `r'` separates the finitely many nontrivial `q`, `q p_1^-1` that occur.

Since `r(H) <= C' x {0}`, `p_j notin H` gives `r(p_j) notin r(H)`. So
`pi_r(b_i)` avoids `pi_r(A)`, respectively `pi_r(A')`. The image word is then
Britton-reduced in `R_r`, hence nontrivial.

## 3. The inner envelope

Put `D_e = Gamma_e x R-hat` and

```text
iota : Gamma_e x H -> D_e,     iota(g, q) = (g, (Lambda(g), q)).
```

**(E2)** `iota` is an injective homomorphism. It is a homomorphism because
`Lambda(g')` and `q` commute in `G-hat x H`. It is injective because the first
coordinate recovers `g`, and then the last recovers `q`.

**(E3)** `u_0 = (1, w)` satisfies `u_0 iota(s,1) u_0^-1 = iota(s, tau_e(s))`
for every `s in S_e`. Indeed,

```text
u_0 (s, (Lambda s, 1)) u_0^-1 = (s, (Lambda s, pr_1 Lambda s)) = (s, (Lambda s, tau_e s))
```

by `Lambda(s) in H x H` and (L1).

## 4. Consequences

**(E4) Embedding.** Apply `asymmetric-hnn-embeds-in-central-hnn-of-inner-envelope`
(IE1) with base `iota(Gamma_e x H)`, `C_1 = iota(S_e x 1)`, overgroup `D_e` and
inner conjugator `u_0`. The result is

```text
R_e  <=  Omega_e = < D_e, z | [z, C_e] = 1 >,
C_e  =  iota(S_e x 1) = {(s, (Lambda(s), 1)) : s in S_e} ~= S_e,   u -> u_0 z.
```

**(E5) Wreath form.** By `centralizer-hnn-is-free-generalized-wreath`,
`Omega_e ~= Z wr^*_(D_e action D_e/C_e) D_e`.

**(E6) Sofic criterion.** Suppose `Gamma_e` is sofic. Then `D_e` is sofic,
since `R-hat` is residually finite. If in addition `D_e action D_e/C_e` is a
sofic action (GKP Definition 2.1(5)), then `Omega_e` is sofic by GKP Theorem
3.7 (`gkp-free-generalized-wreath-soficity`), and so is its subgroup `R_e`.

Model test. With `tau_e` trivial, `w` can be deleted and `u_0 = 1`, and (E4)
becomes the identity embedding of an ordinary central rope. If `tau_e` is not
trivial, no conjugator exists inside `Gamma_e x H`. The graph `{(s, tau_e s)}`
and `S_e x 1` have different projections to `H`, and every inner automorphism
of a direct product preserves both projections of a subgroup. So the
enlargement is necessary.

## 5. Where the question now sits

**The coset space.** `(g, rho) C_e -> g S_e` is a `D_e`-equivariant map onto
`Gamma_e/S_e`. The fibre over `S_e` is a copy of `R-hat`, because
`(s, rho) C_e = (1, rho (Lambda s, 1)^-1) C_e`, and `(1,rho)C_e = (1,rho')C_e`
only when `rho = rho'`. The stabilizer `S_e x R-hat` acts on that fibre by

```text
(s, rho) . x = rho x (Lambda(s), 1)^-1,
```

which is the pullback of the two-sided action `R-hat x R-hat action R-hat`
along `id x (Lambda, 1)`. So `D_e/C_e` is induced from a pulled-back
two-sided action of a residually finite group, over the base action
`Gamma_e action Gamma_e/S_e`. No recorded theorem makes induced set actions
sofic. The obvious attempt dies because a finite model of
`G action G/K` carries no `K`-valued cocycle labels with which to glue fibre
models.

**The sentence in `centralizing-hnn-sofic-strategy-route`.** It says "the
same free-edge argument applies to that edge because its base is then sofic
and the edge subgroup `S_e` acts with the required freeness in the
synchronized models". Checked 2026-09-13:

1. The free-edge argument (`centralizing-hnn-sofic-via-regular-edge-centralizer`,
   (CE1)) chooses the stable letter in the centralizer of one edge action. A
   twisted letter must conjugate two different restrictions of the base
   model to `S_e`, so (CE1) does not apply. One first needs those
   restrictions to be isomorphic `S_e`-sets, and the sentence never supplies
   that.
2. The synchronized models of assembly Section 3.3 are not faithful. The
   finite factor `r_n o Lambda` kills `K_e^0` (Section 3.4). The MF proof gets
   injectivity only through the universal HNN algebra (Ueda, Shulman), and a
   permutation model has no counterpart of that step.
3. What is true: exact conjugacy is free (Sections 1--3), and the edge acts
   freely wherever a sofic model of `Gamma_e` acts freely. The separation
   content is a centralizing-rope problem for the edge `C_e ~= S_e` inside
   `D_e`. It is not the first rope's edge `L_e` in `K_e`, and
   `centralizing-hnn-perturbed-edge-separation` does not imply it.

So the route as written would establish the compiler from the first rope
alone. It needs the twisted-rope claim as an explicit premise. That premise
was added on 2026-09-13.
