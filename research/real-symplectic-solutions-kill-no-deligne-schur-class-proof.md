---
rg: 2
id: real-symplectic-solutions-kill-no-deligne-schur-class-proof
kind: route
title: Pull the host's central extension back along the adjunction and apply the centralized-collapse criterion
target: real-symplectic-solutions-kill-no-deligne-schur-class
requires:
  - central-extension-kl-schur-criterion
  - kervaire-laudenbach-holds-for-hyperlinear
---

**(RS1).** Let `A = (Q * <t>)/<<w>>`. Define `psi : Q * <t> -> H` by `rho`
on `Q` and `t -> T`. Since `w_rho(T) = 1`, `psi` factors through `A`; call
the induced map `psi-`.

Put `A^ = { (a, h) in A x H^ : psi-(a) = pi(h) }`, where `pi : H^ -> H`.
This is a central extension of `A` by `Z`. Its part over the image of `Q`
in `A` is `{ (q, h) : rho(q) = pi(h) }`, which is the pullback of `H^`
along `rho`, that is `E`. So `E -> A^` is injective and is the identity on
`Z`.

Choose `T^ in H^` over `T` and put `t^ = (t, T^) in A^`. Let `w~ in E * <t>`
be any lift of `w`. Under `E * <t> -> A^`, `t -> t^`, the word `w~` maps
over `w = 1 in A`, hence to a central element `(1, zeta)` with
`zeta in Z`. Because `Z <= E` is central, `w~' = w~ zeta^(-1)` is again a
lift of `w`, and it maps to `1`. Each `[z, t]` with `z in Z` maps to
`[z, t^] = 1`, since `z` is central in `A^`. So the homomorphism factors
through `(E * <t>)/<<w~', [Z, t]>>`, and its restriction to `Z` is
injective. Hence `Z` injects into that centralized quotient.

By item 2 of `central-extension-kl-schur-criterion`, this holds exactly
when `alpha_H(K_2(Q, w)) = 0`, for every lift. That criterion needs
`Q -> (Q * <t>)/<<w>>` injective, which is a hypothesis of (RS1). ∎

**(RS2).**
- **Injectivity.** `Sp_4(Z)` is a finitely generated linear group, so it is
  residually finite (Malcev), hence sofic and hyperlinear (standard). By
  `kervaire-laudenbach-holds-for-hyperlinear`, `Sp_4(Z)` injects into
  `(Sp_4(Z) * <t>)/<<w>>` for every nonsingular `w`.
- **Host.** `pi_1(Sp_4(R)) = Z`, so `Sp_4(R)` has a unique connected
  three-fold cover `H^`, a central extension of the abstract group `Sp_4(R)`
  by `Z/3`. By definition (`deligne-triple-cover-fd-central-invisibility`),
  `E_3` is the inverse image of `Sp_4(Z)` in `H^`. So the pullback of `H^`
  along the inclusion `rho` is `E_3`, compatibly with `<z> = Z/3`.
- Apply (RS1). ∎

**Remark (not used).** The same argument works with `Sp_(2g)(R)`, `g >= 2`,
in place of `Sp_4(R)`. The inclusion `U(2) -> U(g)` induces an isomorphism on
`pi_1` through the determinant, so the connected three-fold cover of
`Sp_(2g)(R)` restricts to that of `Sp_4(R)`.
