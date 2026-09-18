---
rg: 2
id: mod-s2-induced-torelli-characters-have-positive-relation-floors
kind: claim
title: The cube-root defect of Mod(S_2) representations induced from Torelli-trivial-on-commutators characters is one third of a dual lattice norm, and every positive separating-twist relation of mass A gives the floor 1/(3A)
distinct_from:
  mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap: that is the uniform gap over all honest representations; this computes the gap exactly on the induced-character class and bounds it by positive relations, leaving uniformity open.
  deligne-monomial-cover-models-have-a-detecting-cycle-floor: that bounds approximate monomial models of the cover over Sp-sets by 2-cycles of the Schreier complex, with mass growing along towers; this concerns exact representations of Mod(S_2) and relations among separating twists in H_1 of the preimage, where positive relations of bounded mass are not excluded by any systole bound.
  deligne-congruence-monomial-models-need-growing-defect: that transfers a block cycle and dies when q divides the index; here the transfer gives the positive relation of mass 5[Sp_4(Z):Gamma'], which dies at exactly the same step when 3 divides the index, and the floor asks instead for short positive relations.
---

**ESTABLISHED** (`mod-s2-induced-torelli-characters-positive-relation-floor-proof`). Unreviewed.

**Setting.** Let `M = Mod(S_2)`, `pi : M -> Sp_4(Z)`, `I = ker pi`. Let `Gamma'` be of finite index in
`Sp_4(Z)` and put `Lambda = pi^(-1)(Gamma')`.
- `H_1(I)_(Gamma') = Z^r`, with basis `e_1, ..., e_r`, one for each `Gamma'`-orbit of symplectic
  splittings of `H_1(S_2)`. The class of a separating twist `t_s` is `e_(i(s))`.
- `chi : Z^r -> Z` is the coordinate sum.
- `B = B(Gamma') = ker( H_1(I)_(Gamma') -> H_1(Lambda) )`, the image of `H_2(Gamma')`.
- `D(Gamma')` is the infimum of `max_s dist(alpha_s, 1/3)` over unitary characters `phi` of `Lambda`, where
  `phi(t_s) = exp(2 pi i alpha_s)` and `s` runs over all separating curves.

For a character `phi`, `rho = Ind_Lambda^M phi` is an honest representation of `M`, of dimension
`[Sp_4(Z) : Gamma']`, and `||rho(t_s) - omega I||_op = 2 sin(pi max_s' dist(alpha_s', 1/3))`.

**Theorem.**
1. **(TD) Torsion-point duality.** With `||psi||_B = sup_(0 != b in B) |psi(b)| / ||b||_1`,
   ```text
   D(Gamma') = (1/3) min { ||psi||_B : psi in Hom(B, Z), psi = chi|_B mod 3 }.
   ```
2. **(RF) Relation floor.** For every `b in B` with `3 not| chi(b)`, `D(Gamma') >= 1 / (3 ||b||_1)`.
3. **(PR) Positive relations exist.** `B` contains the nonzero vector `b_tr = 5 c >= 0` of mass
   `5 [Sp_4(Z) : Gamma']`, where `c_i` counts the cosets `x Lambda` with `x^(-1) s` in orbit `i`.
   `t_s` fixes every coset, because `I <= Lambda` and `I` is normal. So no real character of `Lambda` is positive on all
   separating twists (Gordan's alternative).
4. **(Base)** For `Gamma' = Sp_4(Z)`: `r = 1`, `B = 5Z`, and `D = 1/15`, attained by `t_a -> exp(2 pi i 2/10)`.
   (RF) with `b = 5` is sharp.
5. **(Mono)** `D(Gamma'') <= D(Gamma')` for `Gamma'' <= Gamma'`.

**Consequence: a positive-relation criterion.** Put
`A_+(Gamma') = min { chi(b) : b in B, b >= 0, 3 not| chi(b) }` (infinity if there is none). Then
`D(Gamma') >= 1/(3 A_+(Gamma'))`. So `mod-s2-torelli-positive-relations-have-bounded-mass`
(`sup A_+ < infinity`) would give a uniform operator-norm floor `2 sin(pi/(3 sup A_+))` for the whole
induced-Torelli-character class. For `b >= 0` the mass is `chi(b)` itself, so this is a statement about
short products of separating twists, all with positive exponent, that die in `H_1(Lambda)`.

**Where the known mechanism dies.** The transfer relation `b_tr` has `chi(b_tr) = 5 [Sp_4(Z):Gamma']`.
Once `3` divides the index, `3 | chi(b_tr)` and (RF) says nothing. This is the same step at which
`deligne-congruence-monomial-models-need-growing-defect` stops for `q = 3`. Every
finite-index `Gamma'` has a subgroup of index divisible by 3, so by (Mono) any uniform floor must come
from positive relations that are not transfers.

**Calibration.** Wave-11 and wave-12 census runs (on the live bus, not yet landed) report
`D = 1/15` at the base and `D = 1/30` at level 4 with an `l1`-mass-10 certificate. That matches (RF)
with equality, `1/(3 * 10)`. Their mass-10 certificate is consistent with a positive relation of mass
`5m`, `m = 2`. Whether it is positive has not been checked here.
