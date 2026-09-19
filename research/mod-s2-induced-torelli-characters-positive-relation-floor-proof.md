---
rg: 2
id: mod-s2-induced-torelli-characters-positive-relation-floor-proof
kind: route
title: Characters of Lambda restrict to Ann(B), so the cube-root defect is a sup-distance to a closed subgroup of a torus from a 3-torsion point
target: mod-s2-induced-torelli-characters-have-positive-relation-floors
requires:
  - genus-two-torelli-freely-generated-by-separating-twists
  - genus-two-mapping-class-group-homology-and-symplectic-quotient
---

Notation is that of the target. The external standard inputs are:
- **(Tr)** `Sp_4(Z)` acts transitively on symplectic splittings of `Z^4`, since each splitting extends to a
  symplectic basis.
- **(Ch)** The chain relation `(t_a t_b)^6 = t_s` for curves `a, b` meeting once, with `s` the boundary of
  a regular neighbourhood of `a u b` (Farb–Margalit, *Primer*, Prop. 4.12).
- **(Conj)** `x t_s x^(-1) = t_(x(s))`.

**Step 1: the coinvariants.** By the first input node, `I` is free on one separating twist per splitting,
and twists about curves with the same splitting differ by conjugation in `I`.
- So `H_1(I)` is free on the splittings, and `Lambda` acts through `Gamma'` by (Conj).
- Hence `H_1(I)_Lambda = H_1(I)_(Gamma') = Z^r` on the `Gamma'`-orbits, and `r < infinity` by (Tr).
- The five-term sequence of `1 -> I -> Lambda -> Gamma' -> 1` reads
  `H_2(Gamma') -> Z^r -> H_1(Lambda) -> H_1(Gamma') -> 0`, so `B` is the image of `H_2(Gamma')` and
  `K = Z^r / B` embeds in `H_1(Lambda)`.

**Step 2: characters.** A unitary character of `Lambda` restricts to `alpha in (R/Z)^r` that vanishes on
`B`. Conversely, every `alpha in Ann(B) = Hom(K, R/Z)` extends to `H_1(Lambda)`, because `R/Z` is
divisible, and hence to a character of `Lambda`. The same holds with `R` in place of `R/Z`.
- For `rho = Ind phi` on `l^2(M/Lambda)`: since `I` is normal in `M` and `I <= Lambda`, every
  `x^(-1) t_s x` lies in `I`, so `t_s` fixes every coset `x Lambda`. Hence `rho(t_s)` is diagonal with
  entries `phi(x^(-1) t_s x) = exp(2 pi i alpha_(i(x^(-1) s)))`.
- As `x` runs over `M`, `x^(-1) s` meets every splitting by (Tr), so every orbit `i` occurs, and
  `||rho(t_s) - omega I||_op = 2 sin(pi max_i dist(alpha_i, 1/3))`, independent of `s`.
  So `D(Gamma') = dist_inf( (1/3) 1, Ann(B) )` in `(R/Z)^r`, and the infimum is attained because
  `Ann(B)` is compact.

**Step 3: (TD).** Fix the 3-torsion point `p = (1/3) 1`.
- (<=) Let `psi in Hom(B, Z)` with `psi = chi mod 3` and `||psi||_B = c`. The `l1`-dual norm on `B tensor R`
  is `c`. By Hahn–Banach, `psi/3` extends to `l in R^r` with `max_i |l_i| = c/3`, where `l1` is dual to
  `l_inf`. Put `alpha_i = 1/3 - l_i`. For `b in B`, `alpha(b) = (chi(b) - psi(b))/3`, which is in `Z`,
  so `alpha in Ann(B)` and `dist_inf(p, alpha) <= c/3`.
- (>=) Let `alpha in Ann(B)` with `dist_inf(p, alpha) = delta < 1/2`. Choose real representatives
  `l_i = 1/3 - alpha~_i` with `|l_i| = dist(alpha_i, 1/3)`. Then `alpha~(b)` is in `Z` for `b in B`.
  Define `psi(b) = 3 sum_i l_i b_i = chi(b) - 3 alpha~(b)`. It is integral, linear, `= chi mod 3`, and
  `|psi(b)| <= 3 delta ||b||_1`.
- The minimum exists because integral functionals on `B` form a lattice in the finite-dimensional normed
  space `Hom(B, R)`.

**Step 4: (RF).** Take `alpha in Ann(B)` and `l` as in Step 3. Then
`sum_i b_i alpha~_i = chi(b)/3 - sum_i b_i l_i` is in `Z`. So `||b||_1 max_i |l_i| >= dist(chi(b)/3, Z) = 1/3`
when `3 not| chi(b)`.

**Step 5: (PR).** Let `V : H_1(M) -> H_1(Lambda)` be the transfer. For `g = t_s`, every coset is fixed
(Step 2), so `V(t_s) = sum_x [x^(-1) t_s x]`. This is the image of `c = sum_x e_(i(x^(-1) s))`, with
`chi(c) = [M : Lambda] = [Sp_4(Z) : Gamma']`.
- By the second input node and (Ch), all nonseparating twists are conjugate and generate
  `H_1(M) = Z/10`. Then `[t_s] = 12 [t_a] = 2 [t_a]`, so `5 [t_s] = 0` and `V(t_s^5) = 0`.
- Hence `b_tr = 5c` is in `B`, with `b_tr >= 0` and mass `5 [Sp_4(Z) : Gamma']`.
- A real character `y in Ann_R(B)` (Step 2 with `R`) has `y(b_tr) = 0`, so it is not positive on every `e_i`.
- In the target, `c_i` counts the cosets `x` with `i(x^(-1) s) = i`, with cycle length 1 by Step 2.

**Step 6: (Base) and (Mono).**
- For `Gamma' = Sp_4(Z)`, `r = 1` by (Tr). The map `Z = H_1(I)_(Sp_4) -> H_1(M) = Z/10` sends `e` to
  `[t_s] = 2`, so `B = 5Z`.
- In (TD), `psi(5)` must be `= 5 = 2 mod 3`, and the least `|psi(5)|` is `1`, so `D = (1/3)(1/5) = 1/15`.
  Directly, the characters `t_a -> j/10` give `t_s -> j/5`, and `|2/5 - 1/3| = 1/15`. (RF) with `b = 5`
  gives `1/15`, so it is sharp.
- (Mono): a character of `Lambda'` restricts to `Lambda'' = pi^(-1)(Gamma'')`, with the same values on
  separating twists.
