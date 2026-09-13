# Twisted rope, part 2: the envelope's coset action reduces to the edge coset action of the first rope

Lane `ex3-pfg-second-rope`, 2026-09-13. Unreviewed. This part continues
`research/artifacts/twisted-rope-rf-envelope-2026-09-13.md` and uses its
notation: `Lambda`, `G-hat`, `R-hat`, `D_e = Gamma_e x R-hat`,
`lambda = (Lambda, 1) : S_e -> R-hat`, and `C_e = graph(lambda)`.

Soficity of an action means GKP Definition 2.1(5). Section 2 uses these
permanence facts:

- restriction to a subgroup and restriction to orbits (GKP Propositions
  2.15(3) and 2.16, `gkp-sofic-action-toolkit`);
- (S1), (S2) and (C1) of `separating-sofic-quotient-sets-make-an-action-sofic`;
- composition with a quotient map `q : G ->> G_0`. This one is immediate: if
  `phi` is an orbit approximation for `G_0 action X`, then `phi o q` is one
  for `G action X`, with the same charts, since `g` and `q(g)` act identically
  on `X`.

Result:

```text
Gamma_e action Gamma_e/S_e sofic   ==>   D_e action D_e/C_e sofic.
```

Combined with part 1 (E6): **`R_e` is sofic whenever `Gamma_e` is sofic and
`Gamma_e action Gamma_e/S_e` is sofic.** Under those same two hypotheses GKP
Theorem 3.7 also makes the untwisted rope `< Gamma_e, z | [z, S_e] = 1 >`
sofic. So the twist adds no difficulty. The final edge is exactly as hard as
the coset action of the first rope on its edge.

## 1. Finite commuting extensions

**(F1) Lemma.** Let `alpha : G action X` be sofic, and let a finite group
`Phi` act on `X` commuting with `G`. Then the action of `G x Phi` on `X` is
sofic.

*Proof.* Let `F' <= G x Phi` be finite, `E <= X` finite, and `eps > 0`. Let
`F` be the projection of `F'` to `G`, and put `E' = Phi.E`. Take a unital
`(F,eps)`-multiplicative `phi : G -> Sym(A)` that is an `(F,E',eps)`-orbit
approximation. It comes with `B`, `S <= A` and injective charts
`pi_a : E' -> B`.

Put `A' = A x Phi` and `phi'(g,psi) = phi(g) x L_psi`. This map is unital and
`(F',eps)`-multiplicative. Take `S' = S x Phi`, the same `B`, and

```text
pi'_(a,chi)(x) = pi_a(chi^-1 x),     x in E.
```

Each `pi'_(a,chi)` is injective, since `chi^-1 E <= E'`. Suppose
`(g,psi) in F'`, `(phi(g)a, psi chi) in S'`, and `(g,psi)^-1 x in E`. Put
`y = chi^-1 psi^-1 x in E'`. Then `g^-1 y = chi^-1 ((g,psi)^-1 x)` lies in
`E'`. The chart identity for `phi` and the commutation of `G` with `Phi` give

```text
pi'_(phi(g)a, psi chi)(x) = pi_(phi(g)a)(y) = pi_a(g^-1 y)
                          = pi_a(chi^-1 (g,psi)^-1 x) = pi'_(a,chi)((g,psi)^-1 x).
```

This is the orbit-approximation identity for `phi'`. QED.

## 2. From the edge coset action to the envelope coset action

Assume `Gamma_e action Gamma_e/S_e` is sofic.

**(i) Graphs mod finite quotients.** `R-hat` is residually finite and
countable, so choose finite quotients `phi_n : R-hat -> Phi_n` whose kernels
decrease with trivial intersection. Put

```text
C_n = { (s, rho) in S_e x R-hat : phi_n(rho) = phi_n(lambda(s)) }.
```

Each `C_n` is a subgroup containing `C_e`. The `C_n` decrease, and their
intersection is `C_e`.

**(ii) Separation.** The maps `p_n : D_e/C_e -> D_e/C_n` are equivariant.
Given finite `E <= D_e/C_e`, the finitely many elements `d^-1 d'`, taken over
pairs of distinct points, all lie outside `C_n` for large `n`. So some `p_n`
is injective on `E`. By (S1) it suffices that every action
`D_e action D_e/C_n` is sofic.

**(iii) Quotient.** `1 x ker phi_n` is normal in `D_e` and contained in
`C_n`. So `D_e action D_e/C_n` factors through `Gamma_e x Phi_n`, which acts
on the cosets of `graph(mu_n)` with `mu_n = phi_n o lambda : S_e -> Phi_n`.
Composition with a quotient map preserves soficity.

**(iv) Finite factor.** `Phi_n` acts on `Y_n = (Gamma_e x Phi_n)/graph(mu_n)`
on the left, commuting with `Gamma_e`. By (F1) it suffices that
`Gamma_e action Y_n` is sofic.

**(v) Orbits.** The stabilizer in `Gamma_e` of `(1,chi) graph(mu_n)` is
`S''_n = ker mu_n`, because `(1,chi)^-1 (g,chi) = (g,1)`. So `Y_n` is, as a
`Gamma_e`-set, a finite disjoint union of copies of `Gamma_e/S''_n`. By
restriction to orbits it suffices that `Gamma_e action Gamma_e/S''_n` is
sofic.

**(vi) Injective map to a product.** Put `rho_n(s-hat) = phi_n(s-hat, 1)` on
`H x H` and `M_n = ker rho_n`, a finite-index normal subgroup of `H x H`.
Then `S''_n = S_e ∩ Lambda^-1(M_n)`. The map

```text
g S''_n  |->  ( g S_e, Lambda(g) M_n )
```

is well defined and `Gamma_e`-equivariant. It is injective: if `g' = gs` with
`s in S_e` and `Lambda(s) in M_n`, then `s in S''_n`. By (S1) it suffices
that the diagonal action on `Gamma_e/S_e x G-hat/M_n` is sofic.

**(vii) Product.** The diagonal action is the restriction to the diagonal
subgroup of the product action of `Gamma_e x Gamma_e`, the second factor
acting through `Lambda`. That product action is sofic by (S2), given soficity
of `Gamma_e action Gamma_e/S_e` (the hypothesis) and of
`Gamma_e action G-hat/M_n`.

**(viii) `M_n` is separable in `G-hat`.** `Lambda` is surjective, since
`Lambda(K_e) = H x P`, and together with `sigma` this generates
`(P x P) x| <sigma>`. So `Gamma_e action G-hat/M_n` is a composition with a
quotient map, and by (C1) it is enough that `M_n` is an intersection of
finite-index subgroups of `G-hat`.

- `H x H = ker(chi x chi)` with `(P x P)/(H x H) = Z^2`, so `H x H` is an
  intersection of finite-index subgroups `V_j` of `P x P`.
- `M_n` contains `(M_n ∩ H x 1) x (M_n ∩ 1 x H)`, a product of finite-index
  normal subgroups of `H`. By (BCF2) there are finite quotients `r_1, r_2` of
  `P` with `ker(r_i|H)` inside those factors. Put
  `W = ker r_1 x ker r_2`, a finite-index normal subgroup of `P x P` with
  `W ∩ (H x H) <= M_n`.
- `M_n W` has finite index in `(H x H)W`, which has finite index in `P x P`.
  By the modular law, `M_n W ∩ (H x H) = M_n`. So
  `M_n = ∩_j (M_n W ∩ V_j)` is an intersection of finite-index subgroups.

`P x P` has index 2 in `G-hat`. QED for Section 2.

## 3. The remaining question: `Gamma_e action Gamma_e/S_e`

By `centralizer-hnn-is-free-generalized-wreath`, `Gamma_e = F(X) x| K_e` with
`X = K_e/L_e` and `v = z_(x_0)`, where `x_0 = L_e`.

**Edge structure.** Since `f z_(x_0)^-1 f^-1 = z_(f x_0)^-1`,

```text
vFv^-1 = { z_(x_0) z_(f x_0)^-1 f },    S_e = A_Y x| F,
A_Y = < z_(x_0) z_y^-1 : y in Y >,      Y = F.x_0 ~= F/N_e.
```

Adjoining `z_(x_0)` to the elements `z_(x_0) z_y^-1`, `y != x_0`, gives a free
basis of `F(Y)`. So `A_Y` is a free factor of `F(Y)` with complement
`<z_(x_0)>`. `F` normalizes `A_Y`, and `A_Y ∩ K_e = 1`.

**Fibration.** `Gamma_e/S_e` maps equivariantly onto `K_e/F`. The fibre over
`kF` is `F(X)/A_(kY)`, based at `k x_0`.

- The base action `K_e action K_e/F` is sofic by (C1). `F` sits in `K_e` as
  the graph of `f |-> (w_f, 1, (f,1))` over the first free factor, so it is
  closed in the profinite topology of the residually finite `K_e`.
- Each fibre carries a coset action of a free group, and every action of a
  free group is sofic (GKP Theorem 2.19).

What is missing is the gluing. We need a set-action analogue of GKP
Theorem 3.7 for `F(X) x| K_e` acting on this induced family of free-factor
coset spaces, with lamps permuted through `K_e action X`. That is the same
free-wreath mechanism that makes `Gamma_e` itself sofic from
`K_e action K_e/L_e`, but now for an action instead of the group.
