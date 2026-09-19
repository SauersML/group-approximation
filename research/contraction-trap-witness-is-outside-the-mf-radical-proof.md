---
rg: 2
id: contraction-trap-witness-is-outside-the-mf-radical-proof
kind: route
title: Map the trap onto a lamp group over the ascending HNN of the Magnus group along the Fox-Jacobian endomorphism, and certify non-surjectivity by one F_5 point where e_1 leaves the row space of D
target: contraction-trap-witness-is-outside-the-mf-radical
requires:
  - amenable-implies-operator-mf
  - mf-radical-functoriality
  - jacobson-el3-is-not-lef
---

Conventions.
* `F` is free on `x_1..x_n`, and `A = F_ab`, written multiplicatively.
* `Z[A]` is the Laurent polynomial ring, a domain whose units are `+-` monomials.
* `phi_ab` is the automorphism of `A` induced by `phi`, extended to a ring endomorphism of `Z[A]` and
  coordinatewise to `Z[A]^n`.
* Row vectors throughout.

## 1. The Magnus group and the Fox endomorphism

Let `G = Z[A]^n x| A`, with `(a, f)(b, h) = (ab, f + a h)`. This is a group, and `Z[A]^n` is an abelian
normal subgroup with abelian quotient `A`, so `G` is metabelian. Since `F` is free,
`mg(x_i) = (x_i, e_i)` defines a homomorphism `mg : F -> G`. The `f`-coordinate of `mg(u)` is the
abelianized Fox gradient of `u`, but only the homomorphism property is used below.

Define `D` by `mg(phi(x_j)) = (phi_ab(x_j), D_j)`, where `D_j` is row `j`. Then put

`Phi(a, f) = (phi_ab(a), phi_ab(f) D)`.

* **Phi is an endomorphism.** `Phi((a,f)(b,h)) = (phi_ab(ab), phi_ab(f) D + phi_ab(a) phi_ab(h) D)`,
  which is `Phi(a,f) Phi(b,h)`, since `phi_ab` is a ring map.
* **Phi o mg = mg o phi.** Both sides are homomorphisms `F -> G`, and they agree on each `x_j` by the
  definition of `D`. The script also checks this on random words.
* **Phi is injective when (FT-1) holds.** Suppose `Phi(a, f) = 1`. Then `phi_ab(a) = 1`, so `a = 1`,
  and `phi_ab(f) D = 0`. Since `det D != 0` over the domain `Z[A]`, `phi_ab(f) = 0`. Then `f = 0`,
  because `phi_ab` is injective on `Z[A]`: it is induced by an injective map of free abelian groups,
  hence injective on monomials, and it maps distinct monomials to distinct monomials.

## 2. The solvable quotient Q

Let `Q = < G, t | t z t^-1 = Phi(z) >` be the ascending HNN extension. For injective `Phi` the
standard facts are these (see also Section 0 of `alpha-amenably-separable-base-keeps-compression-witness-mf-proof`).
* `G` embeds in `Q`.
* `Q = G_inf x| <t>`, where `G_inf = union_k t^-k G t^k` is a directed union of copies of `G`.
* For `z in G`: `t^-1 z t in G` if and only if `z in Phi(G)`.

`G_inf` is a directed union of metabelian groups, so it is metabelian. `Q / G_inf = Z`. So `Q` is
solvable of derived length at most 3, hence amenable. It is countable.

The assignment `x -> mg(x)` (`x in F`), `g -> t` respects `g x g^-1 = phi(x)`, since
`t mg(x) t^-1 = Phi(mg(x)) = mg(phi(x))`. So it defines `pi : M = <F, g | g x g^-1 = phi(x)> -> Q`.
Put `P = pi(F) = mg(F)`, a subgroup of `G`.

## 3. Separation of y = g^-1 x g from P

Suppose `pi(y) = t^-1 mg(x) t` were in `P`. Then it would lie in `G`, so `mg(x) = (x, e_x)` would lie
in `Phi(G)`. That means `e_x = phi_ab(f) D` for some `f in Z[A]^n`, contradicting (FT-2).

**Certificate for (FT-2).** Let `z in (k^x)^n` be a point over a field `k`.
* Evaluation `ev_z : Z[A] -> k` is a ring map, because `z` has unit coordinates.
* The entries of `D` are Laurent polynomials.
* So `e_x = h D` with `h in Z[A]^n` would give `e_x = ev_z(h) D(z)`, putting `e_x` in the row space of
  `D(z)`.

So one point `z` with `e_x` outside that row space proves (FT-2).

## 4. The lamp quotient and the MF conclusion

Let `H = (Z/2)^(Q/P) x| Q`, with finitely supported lamps and `Q` acting by left translation. Define
`Theta : T(F, phi) -> H` by `x -> pi(x)`, `g -> pi(g) = t` and `e -> delta_P`.
* **The relations `g x g^-1 = phi(x)`** hold in `Q`.
* **The relations `[e, x] = 1`.** `pi(x)` lies in `P` and fixes the coset `P`, so it commutes with
  `delta_P`.
* **The witness.** `Theta(w_x) = delta_P + pi(y) . delta_P = delta_P + delta_{pi(y) P}`. By Section 3,
  `pi(y) P != P`, so `Theta(w_x) != 1`.

`H` is abelian-by-amenable, hence amenable, and countable. By `amenable-implies-operator-mf` it is MF, so
`Rad_MF(H) = 1`. Concretely, `||lambda(Theta(w_x)) - 1|| >= sqrt 2`, on the vector `delta_1`. By
`mf-radical-functoriality`, `Theta(Rad_MF(T)) <= Rad_MF(H) = 1`. Hence `w_x` is not in `Rad_MF(T(F, phi))`.
This proves (FT1).

## 5. The rank-three instance (FT2)

`Gamma_3 = T(F_6, phi_C)` is exactly the group of `jacobson-el3-is-not-lef`: the relations (C1)-(C6)
read `g x g^-1 = phi_C(x)`, and (Z1)-(Z6) read `[e, x] = 1`. Its witness `w = [e, g^-1 a1 g]` maps to
`x_23(-sq)`.

`fox_separation.py` computes `D` for `phi_C` symbolically and finds the following.
* `phi_ab` has exponent matrix of determinant 1.
* `det D = -x2^6 x3^2 P_C / (x1^6 x4^4 x6) != 0`.
* At `z = (4,4,2,1,4,1) in (F_5^x)^6`, `D(z)` has rows
  `(0,1,0,0,0,0)`, `(0,0,2,3,1,0)`, `(0,0,0,1,0,0)`, `(1,0,3,4,0,3)`, `(3,0,3,2,2,0)`, `(0,0,0,0,0,2)`.

**By hand.** Rows 1, 3 and 6 span `e2, e4, e6`. Modulo these, rows 2, 4 and 5 become `(0,2,1)`,
`(1,3,0)` and `(3,3,2)` in coordinates `(1,3,5)`. The third is `3 (1,3,0) + 2 (0,2,1)` mod 5.
Now suppose `(1,0,0) = a (0,2,1) + b (1,3,0)`. Then `b = 1` and `a = 0`, which forces `3 = 0`, false.
So `rank D(z) = 5` and `e_1` is not in the row space.

(FT1) now gives `w notin Rad_MF(Gamma_3)`. Injectivity of `phi_C` itself is not needed; it holds by
`contraction-trap-groups-are-sofic`.

## 6. Why the simpler quotients fail (FT3)

* **Nilpotent images.** Let `rho` be any quotient of `M` with `rho(F)` nilpotent. The map `phi_ab` is onto,
  so `rho(phi(F))` maps onto the abelianization of `rho(F)`, and therefore `rho(phi(F)) = rho(F)`. Then
  `rho(y) = rho(g)^-1 rho(x) rho(g)` lies in `rho(g)^-1 rho(phi F) rho(g) = rho(F)`.
* **Rank-one affine images.** Linear parts in `Aff(K)` commute, so `lambda o phi = lambda`. Solving
  this on `A` gives `lambda(a1) = lambda(a2) = alpha`, `lambda(a3) = lambda(a4) = beta` and
  `lambda(c) = lambda(d) = 1`. Let `T_P` be the translation subgroup of the image of `F`. It is a
  `Z[Lambda]`-module, where `Lambda = <alpha, beta>`, and it contains `mu(a1 a2^-1) = m1 - m2`.
  * For `g -> (gamma, 0)` with `gamma != 1`, the relation (C1) gives `m2 = gamma m1`. The image of `y` is
    `(alpha, gamma^-1 m1)`, which lies in the image of `F` if and only if `(gamma^-1 - 1) m1` lies in
    `T_P`. That element is `gamma^-1 (m1 - m2)`.
  * The script verifies `det(D - gamma) = (alpha^2 + beta gamma)(gamma - 1)^4 (gamma + 1) / beta` on
    the torus, so `gamma` is `-1` or `-alpha^2/beta`, and `gamma^-1` is in `+-Lambda`. Hence the
    element is in `T_P`.
  * For `g -> (1, nu)`, (C1) gives `m2 = m1 + (1 - alpha) nu`, and the image of `y` is
    `(alpha, m1 + (alpha - 1) nu) = (alpha, m1) (1, alpha^-1 (m1 - m2))`, again in the image.

  So `P_C`, which restricts to the unit `-alpha^2 beta` on this torus, is exactly what the Magnus
  quotient sees and the fixed-character quotients cannot see.

## 7. Remarks (not used)

* **Converse at the metabelian level.** The image of `mg` is `{(a, f) : a - 1 = sum_i f_i (x_i - 1)}`,
  by exactness of the Crowell sequence `0 -> F'/F'' -> Z[A]^n -> Z[A]`. Using this, (FT-2) is equivalent
  to `x notin phi(F) F''` when `Phi` is injective. So the Fox test is exactly the free metabelian
  separation test.
* **Calibration.** For `a -> a^m`, `D = 1 + x + ... + x^(m-1)` is a non-unit for `|m| >= 2`. So every
  Baumslag-Solitar trap passes, consistent with the amenable lamp quotient of the BS toy. An automorphism
  has `D` invertible over `Z[A]` and fails.
