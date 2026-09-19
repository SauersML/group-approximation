---
rg: 2
id: mod-s2-jones-rectangular-separating-twist-spectrum-proof
kind: route
title: Realize the rectangular Temperley-Lieb module on the Birman-Hilden presentation, read the separating twist off the three-strand subalgebra, and pin its weighted mean eigenphase to a fifth root
target: mod-s2-jones-rectangular-separating-twist-spectrum
requires: []
---

**Imports.**
- [MW] Margalit-Winarski, *The Birman-Hilden theory*, arXiv:1703.03448, Section 4, quoted verbatim from the
  arXiv text: "Birman and Hilden use the above isomorphism to derive the following presentation for Mod(S2). The
  generators are the Humphries generators for Mod(S2), and we denote them by T1,...,T5. The relations are:
  [Ti,Tj] = 1 for |i-j| > 2 [the extracted text reads so; the braid-group far-commutation is |i-j| >= 2, and the
  representation below satisfies the stronger form], TiTi+1Ti = Ti+1TiTi+1 for 1 <= i <= 4,
  (T1T2T3T4T5)^6 = 1, (T1T2T3T4T5T5T4T3T2T1)^2 = 1, [T1T2T3T4T5T5T4T3T2T1, T1] = 1." Section 5 of the same paper
  records that Jones' Hecke-algebra representation yields "a representation of Mod(S2) to GL5(Z[t,t^-1])".
- [BB] Bigelow-Budney, *The mapping class group of a genus two surface is linear*, AGT 1 (2001), Prop. 3.2 and
  Prop. 3.3, which give the same `Z/2` central extension of `Mod(S_(0,6))`. This is only a consistency check.
- [FM] Farb-Margalit, *A Primer on Mapping Class Groups*, Section 4.4.1 (chain relations, Prop. 4.12). The 2-chain
  relation is `(T_a T_b)^6 = T_d` for `i(a,b) = 1`, where `d` is the boundary of a regular neighbourhood of `a u b`.
  The statement was taken from a secondary summary; the book page was not re-read this session. `T_1, T_2` form such
  a chain, and in `S_2` the curve `d` bounds a one-holed torus on each side, so `t_s = (T_1 T_2)^6` is a separating twist.

**(P1) The module.**
- *Basis.* The five noncrossing perfect matchings of `{0,...,5}`. The operator `e_i` caps and cups the points
  `i, i+1`, and a closed loop contributes `delta`. These satisfy the TL relations `e_i^2 = delta e_i`,
  `e_i e_(i+-1) e_i = e_i`, and `e_i e_j = e_j e_i` for `|i-j| >= 2`.
- *Braid relations.* With `delta = -A^2 - A^(-2)`, the elements `g_i = A + A^(-1) e_i` satisfy the braid relations
  (Kauffman bracket).
- *Eigenvalues.* The eigenvalues of `e_i` are `0` and `delta`. So `g_i` has eigenvalues `A` and
  `A + A^(-1) delta = -A^(-3)`, both of modulus 1 when `|A| = 1`.
- *Unitarity.* `e_i` is self-adjoint for the Gram form. The script computes
  `det Gram = delta^5 (delta-1)^4 (delta+1)^4 (delta^2-2)` exactly with sympy. The form is positive definite at
  `delta = 2`, where it is the permutation-module form, and it has no zero on `(sqrt 2, 2]`. So it is positive
  definite there, and `g_i` is unitary for it. For `A = exp(i(pi/2 + x))` we get `delta = 2 cos 2x`, so the
  condition is `|x| < pi/8`.

**(P2) The genus-two relations.**
- *Scalars.* `C = (g_1...g_5)^6` is central in the image of `B_6`. On the rectangular (3,3) module it is a scalar
  `c` (Schur, since the module is irreducible for `delta` in the arc). The Jucys-Murphy element
  `J = g_1...g_5 g_5...g_1` is also a scalar `j`: restricting the (3,3) shape to 5 strands leaves only (3,2).
- *Rescaling.* Replace `s_i` by `beta g_i`. The relations of [MW] then become `beta^30 c = 1` and `beta^20 j^2 = 1`,
  and the commutator relation holds because `J` is scalar.
- *Count.* The script finds exactly 10 solutions for every `x` checked. They differ by tenth roots of unity, which
  matches `H_1(Mod(S_2)) = Z/10`.
- *Numerical check.* All [MW] relations and unitarity hold to `1e-13` across the arc, as printed by `jones_tl6.py`.
  This gives (J1).
- *Infinite image.* For `x/pi` irrational, `rho(T_1)` has eigenvalue ratio `-A^(-4) = -exp(-4 i x)`, which has
  infinite order.

**(P3) The spectrum of `t_s` (J2).**
- *The three-strand algebra.* `g_1, g_2` generate the image of `TL_3`. The module `V` restricts to `TL_3` as one copy
  of the 3-through-strand module (dimension 1, `e_1 = e_2 = 0`) plus two copies of the 1-through-strand module
  (dimension 2).
- *First block.* On the 1-dimensional block, `(g_1 g_2)^6 = A^12`.
- *Second block.* On each 2-dimensional block the full twist `(g_1 g_2)^3` is central in `B_3`, hence a scalar `z`.
  Its square satisfies `z^2 = det(g_1 g_2)^3 = (A * (-A^(-3)))^6 = A^(-12)`. So `(g_1 g_2)^6 = A^(-12)`, with
  multiplicity 4.
- *Rescaling.* After rescaling, the eigenvalues are `beta^12 A^(+-12)`. Since `A^(+-12) = exp(+-12 i x)`, writing
  `zeta = beta^12 exp(-36 i x/5)` gives eigenvalues `zeta exp(96 i x/5)` (multiplicity 1) and `zeta exp(-24 i x/5)`
  (multiplicity 4).
- *Check.* The script confirms the closed form to `2e-13` on a grid of `x` and all rescalings, and also confirms that
  `zeta^5 = 1`.
- *Why `zeta^5 = 1`.* The eigenphase offsets satisfy `96/5 - 4 * 24/5 = 0`, so `det rho(t_s) = zeta^5`. Since
  `det rho` is a character of `M` and `H_1(M) = Z/10`, the value `zeta^5` is a tenth root of unity. `zeta` depends
  continuously on `x` and the set of possible values is discrete, so `zeta` is constant along the arc. At `x = 0` it
  lies in `mu_5`, as the script's `delta = 2` line shows.
- *(J3).* The two eigenvalues differ by the factor `exp(24 i x)`. The operator distance from a unitary with two
  eigenvalues at angular separation `gamma` to the nearest scalar is `2 sin(gamma/4)`.

**(P4) The sharp gap (J4).** Suppose `||rho(t_s) - omega I|| < 2 sin(theta/2)` with `theta < pi/2`.
- *Lifts.* Choose real eigenphases `psi_1` (multiplicity 1) and `psi_2` (multiplicity 4) in the interval
  `(2pi/3 - theta, 2pi/3 + theta)`. Then `psi_1 = phi + 96x/5 + 2 pi m_1` and `psi_2 = phi - 24x/5 + 2 pi m_2`,
  where `zeta = exp(i phi)` and `m_1, m_2` are integers.
- *Weighted mean.* `(psi_1 + 4 psi_2)/5 = phi + 2 pi (m_1 + 4 m_2)/5`, because `96/5 - 4 * 24/5 = 0`.
- *Conclusion.* The left side lies in the same interval, since it is a convex combination. The right side is the
  phase of an element of `zeta mu_5 = mu_5`. So some fifth root of unity is within angle `theta` of `2 pi/3`, which
  forces `theta >= 2 pi/15`. The same holds for `omega^(-1)`.
- *Bound.* Therefore `||rho(t_s) - omega^(+-1) I|| >= 2 sin(pi/15)`. Equality holds at `x = 0`, where
  `rho(t_s) = zeta I` with `zeta = exp(2 pi i * 2/5)`.
- *Scope.* The bound does not use `|x| < pi/8` except to have unitarity, so it holds on the whole arc, including the
  second scalar point `x = pi/12`. The script's scan agrees: its minimum is `0.41582`.

**(P5) The tensor closure (J5).**
- *Reductions.* The operator distance of a direct sum is the maximum over its summands, so it suffices to treat one
  word `rho = chi (x) rho_(x_1) (x) ... (x) rho_(x_n)`. A complex conjugate `rho_x-bar` has the (J2) form with
  `x -> -x` and `zeta -> zeta-bar`, so all factors may be taken of that form.
- *Spectrum.* The eigenvalues are `lambda_S = Z exp(i sum_k c_k x_k)`. Here `Z` is a fifth root of unity,
  `c_k in {96/5, -24/5}`, and every one of the `2^n` patterns occurs.
- *Setup.* Suppose all `lambda_S` lie within angle `theta < pi/2` of `omega`. Otherwise the distance is already at
  least `2 sin(pi/4)`.
- *Step 1 (one flip).* Changing one `c_k` multiplies the eigenvalue by `exp(24 i x_k)`. So we can write
  `24 x_k = 2 pi m_k + 24 y_k` with `|24 y_k| <= 2 theta`.
- *Step 2 (absorb the integer parts).* Because `(96/5)(2 pi m/24) = 8 pi m/5` and `(-24/5)(2 pi m/24) = -2 pi m/5`
  agree modulo `2 pi`, we get `lambda_S = Z' exp(i sum_k c_k y_k)` with `Z'` again a fifth root of unity.
- *Step 3 (one lift).* Walk from the minimizing pattern to the maximizing pattern one flip at a time. Each step moves
  the real phase `sum c_k y_k` by at most `2 theta`, which is less than the length `2 pi - 2 theta` of the complement
  of the arc. So all real phases stay in one lift of the arc.
- *Step 4 (bound the midpoint).* The real spread is therefore `sum_k 24 |y_k| <= 2 theta`. The midpoint of the
  spectrum is `arg Z' + sum_k (36/5) y_k`, and `|sum (36/5) y_k| <= (36/5)(2 theta/24) = 0.6 theta`. The midpoint is
  within `theta` of `2 pi/3`, so `arg Z'` is within `1.6 theta` of `2 pi/3`.
- *Conclusion.* This forces `1.6 theta >= 2 pi/15`, that is `theta >= pi/12`. Hence the distance is at least
  `2 sin(pi/24)`.

**Limits.**
- *Scope.* This covers one family together with the direct sums and tensor words built from it, its conjugates and
  the characters. It does not cover subrepresentations of the tensor words, which are treated only as a conditional
  sketch in the claim. It does not cover mixtures with other families.
- *Weighted-mean pinning.* The weighted-mean pinning of (P4) is fixed-dimensional. The attraction argument of (P5)
  is not, but it uses the fact that each factor's spectrum consists of exactly two eigenvalues whose ratio
  `exp(24 i x)` is shared across the family.
