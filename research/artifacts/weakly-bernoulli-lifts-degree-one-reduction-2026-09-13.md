# Weakly Bernoulli liftable actions (part 3): the flip trick and a reduction to degree one

Lane ex2-rokhlin-almost-cocycle, 2026-09-13. Unreviewed. Parts 1--2:
`weakly-bernoulli-lifts-extension-class-norm-2026-09-13.md` and `weakly-bernoulli-lifts-sofic-transfer-and-sp4-2026-09-13.md`.

## 12. Setting

- `Gamma = <S | R>` is finitely presented, infinite, and w-rigid, so Popa's theorem applies. w-rigid groups are
  non-amenable. `ell` is the maximal relator length, `A` is finite abelian, and `alpha in H^2(Gamma, A)` is a central
  class. `a_r in A` is the value of relator `r` on fixed lifts, and `alpha_0 = (a_r)_r`.
- For a p.m.p. action `Z` and `M = L^0(Z, A)`, the degree-1 and degree-2 cochains are `C^1 = M^S` and `C^2 = M^R`
  (presentation complex, one vertex). `delta_0 f = (f∘s^-1 - f)_s`, and `delta_1` is the linearized relator sum along
  the words. Measure the size of a cochain by `|c|_max = max_cells mu(c != 0)`. It is bi-Lipschitz to the
  Gohla--Thom length.
- `Bern = [0,1]^Gamma`, and `X^k` is the product of `k` independent copies with the diagonal shift. `X^k` is
  Bernoulli with base `[0,1]^k`.
- **Degree-1 cocycle expansion with rate `rho`** (`rho(eps) -> 0` as `eps -> 0`). For every `c in C^1(Bern, A)` there
  is `z in Z^1` with `|c - z|_max <= rho(|delta c|_max)`. With `rho` linear this is Gohla--Thom Definition 2.8(ii)
  for `i = 1` and the family `{Bern}`.

**Spectral input.** `Gamma` is non-amenable, so there is `K = K(Gamma, S)` such that for every character
`theta : Gamma -> S^1` and every `eta in L^2_0(X^k)`, `||eta|| <= K max_s ||pi(s)eta - theta(s)eta||`. The reason: the
Koopman representation on `L^2_0` of a Bernoulli shift is weakly contained in `lambda^(oo)`, and
`lambda ⊗ theta ≅ lambda` has no almost invariant vectors.

## 13. Theorem R0: an exact Bernoulli lift of a central extension over a w-rigid base forces splitting

**Theorem R0.** If `theta_*^Bern(alpha) = 0`, that is, if `Bern` is liftable, then `alpha = 0`: the extension splits.

*Proof.*
1. **Two copies.** Let `delta b = alpha_0` with `b in C^1(Bern, A)`. On `X^2` put `d = b∘p_1 - b∘p_2`. Then
   `delta d = alpha_0 - alpha_0 = 0`, so `d` is a 1-cocycle into `A`.
2. **Popa.** `d = delta f + chi` with `f in L^0(X^2, A)` and `chi in Hom(Gamma, A)`.
3. **Three copies.** On `X^3` put `F = f_12 + f_23 - f_13`. The telescoping identity `d_12 + d_23 - d_13 = 0` gives
   `delta F + chi = 0`.
4. **`chi = 0`.** `F` is invariant under the finite-index subgroup `ker chi`, which acts ergodically on `X^3`. So `F`
   is constant, and then `chi = 0`.
5. **Separate variables.** `delta F = 0` makes `F` constant, `F = c`. For a.e. `y`, `f(x,x') = g(x) - g(x') + c` with
   `g = f(., y)`.
6. **Independence.** `(b - delta g)(x) = (b - delta g)(x')` a.e. on `X^2`, so `b - delta g = a` is a constant cochain.
7. **Splitting.** `alpha_0 = delta b = delta a`, so changing the lifts by `a` makes every relator hold. QED

**Comparison.** `bernoulli-lifts-across-finite-kernels-force-virtual-splitting` gives virtual splitting for every
finite normal kernel. For central kernels, R0 gives splitting outright. It is consistent with virtually split nonzero
classes, because their obvious liftable actions (induced from a split finite-index subgroup) have a finite factor and
are not Bernoulli.

## 14. Theorem R1: degree-1 expansion excludes weakly Bernoulli lifts

**Theorem R1.** Suppose `Bern` has degree-1 cocycle expansion with coefficients `A` and some rate `rho`. Then there is
`eps_0 = eps_0(Gamma, S, R, A, rho) > 0` with `|||theta_*^Bern(alpha)||| >= eps_0` for every `alpha != 0`. So no
liftable free action is weakly contained in Bernoulli unless the extension splits
(`bernoulli-maximizes-extension-class-norm`, item 4).

*Proof.* Let `|delta b - alpha_0|_max <= eps`. Constants `C_i` depend only on `(Gamma, S, R, A, K)`.
1. **Two copies.** `d = b∘p_1 - b∘p_2` on `X^2` has `|delta d|_max <= 2 eps`. By expansion there is `z in Z^1(X^2)` with
   `|d - z|_max <= rho(2 eps) =: eps_1`.
2. **Popa.** `z = delta f + chi` exactly, with `f in L^0(X^2, A)` and `chi in Hom(Gamma, A)`.
3. **Three copies.** `F = f_12 + f_23 - f_13` on `X^3`. Since `d_12 + d_23 - d_13 = 0` and each `z_ij` is `eps_1`-close to
   `d_ij`, `mu(F∘s^-1 - F + chi(s) != 0) <= 3 eps_1` for every `s`.
4. **Spectral gap kills `chi` and `F`.**
   - For a character `psi` of `A`, `Phi = psi∘F` has `||pi(s)Phi - psi(-chi(s))Phi||_2 <= 2 sqrt(3 eps_1)`.
   - Write `Phi = m + Phi_0` with `Phi_0 in L^2_0`. The spectral input with `theta = psi∘(-chi)` gives
     `||Phi_0|| <= C_1 sqrt(eps_1)`. So `|m| >= 1 - C_1 sqrt(eps_1)`, and `|1 - psi(chi(s))| <= C_2 sqrt(eps_1)`.
   - Nontrivial `|A|`-th roots of unity are at distance `>= c_A` from 1. So once `C_2 sqrt(eps_1) < c_A`,
     `psi∘chi = 1` for all `psi`, hence `chi = 0`.
   - Fourier inversion on `A` then gives `c in A` with `mu(F != c) <= C_3 eps_1 =: eps_2`.
5. **Fubini.** Some `y` has `mu^2{(x,x') : f(x,x') != g(x) - g(x') + c} <= eps_2` with `g = f(., y)`.
6. **Compare across copies.** For each `s`, `d_s = z_s = f∘s^-1 - f` off `eps_1`, and `f = g∘p_1 - g∘p_2 + c` off
   `eps_2` at both `(x,x')` and `s^-1(x,x')`. So `h_s := b_s - (g∘s^-1 - g)` satisfies `h_s(x) = h_s(x')` off
   `eps_3 = eps_1 + 2 eps_2`.
7. **Near constant.** `sum_a mu(h_s = a)^2 >= 1 - eps_3`, so some `a_s` has `mu(h_s != a_s) <= eps_3`.
8. **Splitting.** `delta h = delta b` exactly, since `delta delta_0 g = 0`. So `delta a = alpha_0` off
   `eps + ell eps_3` at every relator. Both sides are constants, so once `eps + ell eps_3 < 1`, `delta a = alpha_0`
   and `alpha = 0`.
9. **Conclusion.** For `alpha != 0` this forces `eps >= eps_0`, where `eps_0` solves the finitely many threshold
   inequalities above. QED

**What R1 changes.** The degree-2 question about one class (positivity of a norm) becomes a degree-1 stability
property of the Bernoulli shift alone. It is independent of `alpha` and of the extension, and any rate function
suffices, not only a linear one. Popa and the spectral gap supply the equivariant rigidity. The remaining input is
quantitative.

## 15. Degree-1 expansion as a measurable filling problem

- **Filling form.** `c in C^1(Bern, A)` has sparse defect `e = delta c`, a 2-cocycle of density `eps` on each orbit
  complex. Expansion asks for a measurable equivariant `c'` with `delta c' = e` and density `rho(eps)`; then
  `c - c'` is a cocycle. In a triangulated 6-dimensional model (dimension of `Sp_4(R)/U(2)`), `e` is dual to a
  sparse 4-cycle and `c'` to a 5-chain bounding it.
- **Plane test (`Gamma = Z^2`, `A = Z/2`, not w-rigid).** Defects are point charges of density `eps`. Pairing them by
  strings of length `~ eps^(-1/2)` gives `rho(eps) ~ sqrt(eps)`. A nonlinear rate, as R1 allows.
- **Where it dies for Sp_4(Z).**
  - (i) Minimal supports of 2-cocycles are closed membranes that need not break into finite clusters, so local
    filling needs a measurable selection among infinite fillings.
  - (ii) Quantitative higher filling inequalities for `Sp_4(Z)` itself (non-cocompact) in the relevant dimension are
    not in the sources read.
  - (iii) Property (T) gives no filling bound for 2-cocycles.
  - Recalled, not checked: filling in dimensions at least the rank is linear for cocompact higher-rank geometry, and
    `Sp_4(Z)` is a duality group of dimension 4 (Borel--Serre), so finite exact 2-cocycles have finite primitives.
- **Relation to part 2.** R1 needs no finite quotient. It is the Bernoulli analogue of "expansion in dimension 1"
  that Gohla--Thom use on finite actions through Lemma 2.13.

## 16. Model tests

- **R0, hypothesis side.** Take `alpha = beta(chi)`, the Bockstein of a hom `chi : Gamma -> Z/3` that does not lift
  to `Z/9`. The liftable action `Bern x Z/3(chi)` exists, and R0 does not apply to it, because it is not Bernoulli: it
  has a finite factor. R0 still says `Bern` itself is not liftable, which is consistent.
- **R0, conclusion side.** For `alpha = 0`, `Bern x A` lifts, as it should.
- **R1, trivial model.** For a free group (no 2-cells), every cochain is a cocycle and expansion holds with `rho = 0`.
  `H^2(F_n, A) = 0`, so R1 is vacuous there, as it should be. Free groups are not w-rigid anyway.
- **R1, real object.** Over the Gohla--Thom lattices the conclusion is known independently (Theorem G), so R1 is
  consistent there. Whether those lattices have degree-1 Bernoulli expansion is not known to the lane.
