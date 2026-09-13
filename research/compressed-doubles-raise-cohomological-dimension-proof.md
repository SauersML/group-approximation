---
rg: 2
id: compressed-doubles-raise-cohomological-dimension-proof
kind: route
title: Mayer--Vietoris on modules pulled back along the fold map, with a coinduced module split by Mackey
target: compressed-doubles-raise-cohomological-dimension
requires: [infranormal-nonnormal-has-infinite-compression-orbit]
---

All modules are left modules. The standard inputs are:
- the Mayer--Vietoris sequence of an amalgam;
- Shapiro's lemma for coinduced modules;
- the fact that group cohomology commutes with arbitrary products of modules;
- Swan's theorem that cohomological dimension one means free.

## Proof of (DB1)

Put `D = G_1 *_Gamma G_2`, with `G_i` two copies of `G`, and let `f : D -> G` be the fold map.

**Step 1: reduce to restriction.** For a `G`-module `M`, regard `M` as a `D`-module through `f`.
Both restrictions `H^n(G_i;M) -> H^n(Gamma;M)` are then the same map `res`. Mayer--Vietoris,

```text
H^n(G_1;M) + H^n(G_2;M) --(res, -res)--> H^n(Gamma;M) --> H^(n+1)(D;M),
```

embeds `coker(res)` into `H^(n+1)(D;M)`. So it suffices to find `M` with `res` not surjective.

**Step 2: a coinduced module.** Choose a `Gamma`-module `N` with `H^n(Gamma;N) != 0`. Put
`M = Hom_(ZGamma)(ZG, N)`, with `(g.phi)(x) = phi(xg)`.
- Shapiro's lemma says `ev_* o res : H^n(G;M) -> H^n(Gamma;N)` is an isomorphism, where
  `ev(phi) = phi(1)`.
- In particular `res` is injective, and `ev_*` is injective on its image.

**Step 3: Mackey decomposition.** As a `(ZGamma, ZGamma)`-bimodule, `ZG` is the direct sum of the
`Z[Gamma g Gamma]` over double cosets. So, as a `Gamma`-module,

```text
M = prod_(Gamma g Gamma) Hom_(ZGamma)(Z[Gamma g Gamma], N),
```

and `ev` is the projection onto the factor of the trivial double coset, followed by
`Hom_(ZGamma)(ZGamma, N) = N`.
- Put `Gamma_g = Gamma cap g^-1 Gamma g`.
- A `Gamma`-map `phi` on `Z[Gamma g Gamma]` is determined by `psi(gamma) = phi(g gamma)`, subject
  to `psi(x gamma) = (g x g^-1) . psi(gamma)` for `x in Gamma_g`.
- So the factor is `CoInd_(Gamma_g)^Gamma(N^g)`, where `N^g` is `N` with `x in Gamma_g` acting as
  `g x g^-1`. By Shapiro, `H^n(Gamma; factor) = H^n(Gamma_g; N^g)`.

Cohomology commutes with products, so `H^n(Gamma;M)` is the product of `H^n(Gamma;N)` (trivial
coset) and all `H^n(Gamma_g;N^g)` (nontrivial cosets), and `ev_*` is the first projection.

**Step 4: a nonzero nontrivial factor.** Take `g = u^-1`, which is not in `Gamma`.
- `Gamma_g = Gamma cap u Gamma u^-1 = u Gamma u^-1`.
- `x |-> u^-1 x u` is an isomorphism `u Gamma u^-1 -> Gamma`, and it carries `N^g` to `N`.
- So `H^n(Gamma_g;N^g) ~= H^n(Gamma;N) != 0`.

**Step 5: conclude.** Pick `y != 0` in that nontrivial factor, and put it in `H^n(Gamma;M)` with all
other coordinates zero.
- If `y = res(a)`, then `ev_*(res(a)) = 0`, so `a = 0` by Step 2, so `y = 0`. That is a
  contradiction.
- Hence `res` is not surjective, `H^(n+1)(D;M) != 0`, and `cd D >= n + 1`. `QED`

## Proof of (DB2)

- `Gamma` is infinite: by `infranormal-nonnormal-has-infinite-compression-orbit`, some compressor
  `u` has `u^k` outside `Gamma` for every `k >= 1`, so the chain of conjugates is strict.
- `Gamma <= K` is torsion-free with `cd Gamma <= 2`.
- A nontrivial free group maps onto `Z`, while a Kazhdan group has finite abelianization. So
  `Gamma` is not free, and by Swan `cd Gamma >= 2`. Hence `cd Gamma = 2`.
- The compressor `u` lies outside `Gamma`. By (DB1), `cd(G *_Gamma G) >= 3`.
- Subgroups of `K` have `cd <= 2`, so the double does not embed. `QED`

## Model tests

- **No compressor outside.** `G = F(a,b)`, `Gamma = <a>`: the normalizer of `Gamma` is `Gamma`, and
  no element outside compresses it. The double is `F_3`, of dimension one, so the hypothesis of
  (DB1) is needed.
- **Normalizing element outside.** `G = Z^2`, `Gamma = 2Z x Z`, `u = (1,0)`. With trivial `Z`
  coefficients the restriction `H^2(Z^2;Z) -> H^2(Gamma;Z)` is multiplication by two, so
  `H^3(D;Z) != 0`, as (DB1) predicts.
