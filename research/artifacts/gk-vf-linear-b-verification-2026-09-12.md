# Linear verification, second verifier (w4-vf-linear-b)

Lane `w4-vf-linear-b`, 2026-09-12. Verifier for w3-corner-f4, w3-corner-cohn-a, w3-corner-cohn-b,
w3-free-neg, w4-binary-cyclic, w4-hadamard-f3, w4-cohn-gram, w4-kap-join and w4-clifford-df. Every item
below was re-derived on paper. No compute was run.

## 0. Coverage map (main at 9f63e6cd3f)

- **w3-corner-f4.**
  - Theorem 2.1 and the two binary-corner routes: `w3-vf-linear` Section 2, PASS.
  - Artifact Section 4 (phase lifts and the Haar obstruction): Section 3 below.
  - The open target's statement: Section 4 below.
- **w3-corner-cohn-a** (artifact blob 5837c75433). Lemma 2.1, Remarks 2.2–2.3 and Theorem 3.1 were
  re-derived by `w3-vf-linear` (PASS, landing in its own artifact). My independent pass agrees on the
  mathematics, but found one false displayed formula in the claim and route prose: Section 1.
- **w3-corner-cohn-b** (artifact blob 136a93c518). Theorem 1.1, Propositions 2.1–2.3, Lemma 3.3 and the
  three routes: `w3-vf-linear`, PASS. I re-derived Lemma 2.0 and Propositions 2.1–2.3 independently and
  agree:
  - `[[1,1],[1,-1]]^2 = -I` and `[[1,0],[1,-1]]^2 = I`;
  - `u h u = [[-1,-1],[-1,1]] = -h`;
  - `(i[h])^2 = 1_-`, `8 = 2`;
  - over `F_9` the rank of an `F_3`-matrix is unchanged, so the state filter extends.
- **w3-free-neg.** The three established Clifford-cover claims already carry PASS verdicts from
  `w3-vf-nonlinear` (its Sections 3.1–3.3). Its wiring note (`kun-thom-wreath-stably-finite` in
  `requires`) is applied on main. Nothing further.
- **w4 lanes.** No landings yet.

## 1. `natural-leavitt-pair-lifts-have-partial-symmetry-defect`: theorem PASS; the correction factor displayed in the claim and route is FALSE as written, corrected forward

**Re-derivation of Lemma 2.1.** Conventions: `([g]f)([k]f') = [gk](k^-1.f)f'` and `g.P_C = P_(gC)`.
- **Grades.** The identity grade is `P_0 + P_1 = 1`. The cross grades are `[h]1_(W_1)` and `[h^-1]1_(W_2)`.
  `A ⊆ 0` because `g_1` maps `1` onto `01`, and `B' ⊆ 1` because `g_0` maps `0` onto `00`.
- **`W_1` nonempty.** `g_1` maps `0` onto `00 ∪ 1`, so `0 \ A = g_1^-1(1)` is nonempty. The values
  `(1,1,1)` on the atoms `(A, 0\A, 1)` are odd. No Dirac measure lies in `W_1`, since `A ⊆ 0`.
- **Disjointness.** `h W_1 = W_2`, `h^-1(1) = 1 ∪ (0\A)` and `h(0) = 0 ∪ (1\B')`. Both disjointness
  statements follow by total mass.
- **Products.** The four products give `D^2 = F` and `DF = FD = D`.
- **`e' ≠ 0`.** `h ≠ 1`, since `g_0 = g_1` would map `X` onto `00 ∪ 01`. So the identity grade of `e'` is
  `2F ≠ 0`.
- **Idempotents.** `(F ± D)^2 = 2(F ± D)`, `e` and `e'` are orthogonal idempotents, and `e + e' = F`.

**The defect.**
- **What main says.** The claim's bullet reads "`tau'' = ((1 - F) + 2(F + D)) tau` is another lift of
  `t_0` with `tau'' sigma = 1 - e'`". The route reads "The correction `c = (1 - F) + 2(F + D)` satisfies
  `c tau sigma = c^2 = 1 - e'`". Both are false.
- **Why.** Put `c' = (1 - F) + 2(F + D) = (1 - F) + e`. The cross terms `(1 - F)(F + D)` and
  `(F + D)(1 - F)` vanish, and `tau sigma = (1 - F) + (F + D) = (1 - F) + 2e`. So

```text
c' tau sigma = ((1 - F) + e)((1 - F) + 2e) = (1 - F) + 2e = tau sigma = 1 + D,
```

  not `1 - e'`. (`c'` itself equals `1 - e'`.)
- **The correct form.** The artifact's Lemma 2.1 item 5 is right: `c = (1 - F) + 2e = (1 - F) + 4(F + D) = 1 + D`, and

```text
c tau sigma = (1 + D)^2 = 1 + 2D + F = 1 - 2(F - D) = 1 - e'.
```

  So the corrected lift is `tau'' = (1 + D) tau = tau sigma tau`. It kills `e'`:
  `c e' = e' + 2D(F - D) = e' + 2(D - F) = 0`.

**Consequence: none.** Every conclusion uses only `tau'' sigma = 1 - e'`, which the corrected factor
gives: `sigma` is left invertible iff `e' ∈ S_- sigma`, `e' ~ 1_(W_1)`, and `e' ≲ P_0`. The formula is
replaced forward on both nodes, with a correction line quoting the old text.

**Remark 2.3.** `x = f_1 - u` and `y = 2(f_1 - v)` give `xy = e'` and `yx = 4 f_1 = f_1`. This uses
`f_1 u = 0`, `v f_1 = 0`, `f_1 v = v`, `u f_1 = u`, `uv = f_2` and `vu = f_1`.
- `1 ~ 1_(W_1)` would give `1 ≲ P_0`. With the swap `P_0 ~ P_1 ⊥ P_0`, that is a Cohn family in `B`.
- The `F_3` Haar trace gives `Tr(1_(W_1)) = 1/4 = 1`, so it obstructs nothing.

## 2. `no-equivariant-lattice-lift-of-cylinder-idempotents`: PASS, with a sharper form

I agree with `w3-vf-linear` that hypothesis 3 is unused. Here is a sharper form, derived independently.

**The trace.** Let `lambda` be the Haar measure of `M_-`, with values `2^-(2^n - 1)` in `F_3` on the atoms
at depth `n`. Put `Tr(sum [g] f_g) = lambda(f_1)` on `B`. This is a trace because `lambda` is `V`-invariant:
`Tr(([g]f)([g^-1]f')) = lambda((g.f) f')` and `Tr(([g^-1]f')([g]f)) = lambda((g^-1.f') f) = lambda(f' (g.f))`.

**Sharper statement.** No map `Phi : Clopen(X) -> B` exists that is finitely additive on disjoint unions,
`V`-equivariant (`[g]Phi(C)[g]^-1 = Phi(gC)`), and has `Phi(X) = 1`. The values need not be idempotents.

**Proof.** `Tr ∘ Phi` would be a `V`-invariant `F_3`-valued finitely additive measure of total mass 1. The
replacements `0 -> 00` and `0 -> 01` give `nu(0) = 2 nu(0)`, so `nu(0) = 0`. The swap gives `nu(1) = 0`,
and then `nu(X) = 0`, a contradiction.

**What this settles.**
- It proves the claim's "Equivalently" sentence about lifts inside `B`, which Stone duality alone does not
  reach, because commuting idempotents of `B` need not be clopen indicators.
- Multiplicativity and Dirac compatibility are not needed.

## 3. w3-corner-f4 artifact Section 4 (phase lifts and the Haar obstruction): findings PASS

- **Phase lift.** `u_p = 1 + omega^2 p` acts by `1 + omega^2 = omega` on the range of `p`.
  `E_p = 1 + omega^2 [u_p] + omega [u_p^2]` is the `omega`-isotypic idempotent of `<u_p>` (`1/3 = 1`), and
  `pi(E_p) = p`. For orthogonal `p, q`, `u_p u_q = u_(p+q)`.
- **Fourier picture.** `F_4[E] ≅ C(Ehat, F_4)`, because `|<omega>| = 3` is invertible and `F_4` contains the
  cube roots of unity. `Ehat` is the space of `Z/3`-valued finitely additive measures, and `eps_iota` cuts
  out `mu(X) = 1`. `E_p` maps to the indicator of `mu(C_p) = 1`: its values are `0, 1, 0` at
  `mu(C_p) = 0, 1, 2`.
- **Fourier conjugation, exactly.** Put `h e_j = sum_i omega^(ij) e_i` and `g e_j = e_(j+1)`. Then
  `g (h e_j) = omega^(-j) h e_j`, so `h^-1 g h = diag(omega^2, omega, 1) = delta^-1`. `h^2` is the
  permutation `e_j -> e_(-j)`, so `h g h^-1 = h^2 delta^-1 h^-2 = diag(omega, omega^2, 1) = delta`. There is
  no scalar twist.
- **Measure 1/3.** `[delta]` maps to `omega^(mu(C_1) + 2 mu(C_2))`. So `(1 + [delta] + [delta^2]) eps_iota`
  is the indicator of `mu(C_1) + 2 mu(C_2) = 0`, which has Haar measure `1/3`.
- **What dies.** Honest compressions die by `V`-invariance of the Haar measure. The mod-2 Haar trace
  (`1/3 -> 1`) obstructs nothing.

## 4. `binary-cyclic-averaging-idempotent-is-full-on-leavitt-units` (OPEN): statement check

- `g = s_2 t_1 + s_3 t_2 + s_1 t_3` has `F_2` coefficients, so `g ∈ R^x`. `e = 1 + [g] + [g^2]` is
  idempotent in `F_2[R^x]`.
- **Image equation.** `g s_i = s_(i+1)`, so `g b = b` for `b = s_1 + s_2 + s_3`. Then `pi(e) b = 3b = b`,
  and `c b = sum t_i s_j = 3 = 1` for `c = t_1 + t_2 + t_3`.
- Not a decision; the claim stays OPEN.

## 5. Re-check of the revised `no-equivariant-lattice-lift-of-cylinder-idempotents` (w3-corner-cohn-a, 1f2baa84d7): PASS

**(a) Theorem 3.1 without Dirac compatibility.** The theorem now assumes only (1) a Boolean homomorphism
and (2) `V`-equivariance. Re-derived:
- `{C : mu in Phi(C)}` is an ultrafilter, because `Phi` preserves `X`, intersections and complements. So
  `r(mu)` is a point, and `r^-1(C) = Phi(C)` makes `r` continuous.
- (2) gives `r(g mu) = g r(mu)`, so `r_* lambda` is a `V`-invariant probability measure on `X`.
- The replacements `0 -> 00` and `0 -> 01`, together with the swap, rule such a measure out.
- Dirac compatibility is never used. PASS.

**(b) Remark 3.2 and the companion statement in the claim.** Take `Phi : Clopen(X) -> B` additive on
disjoint unions, with `Phi(X) = eps_-` and `Phi(gC) = [g] Phi(C) [g]^-1`.
- `Tr([g] f) = delta_(g,1) ∫ f dlambda` is a trace (Section 2 above), and `Tr(eps_-) = 1`.
- So `Tr ∘ Phi` is a `V`-invariant `F_3`-valued measure of mass 1, and halving gives
  `Tr Phi(0) = Tr Phi(1) = 0`, a contradiction.
- The `F_3` values of `lambda` are consistent under refinement. A depth-`n` odd function has `2^(2^n)`
  odd extensions to depth `n + 1`, and `2^(2^n) · 2^-(2^(n+1) - 1) = 2^-(2^n - 1)`. PASS.

**Wording remark** (no change requested). The `distinct_from` entry still describes the claim as
forbidding "Boolean sections of the Dirac evaluation". After (a), the claim forbids every `V`-equivariant
Boolean homomorphism, those sections included.

## 6. The Clifford-cover refutation chain (w3-free-neg): route PASS, ahead of w4-clifford-df

`clifford-cover-nonsurjunctive-from-anti-half-df-failure` is the route through which a direct-finiteness
failure in `A_S` would refute Gottschalk's conjecture. It is checked now, before any witness exists.
- **Padding.** Use the product `F_3[E_S] = F_3[W] × A_S` of the established
  `clifford-cover-group-algebra-splits-into-wreath-and-skew-ring`. If `b a = 1 != a b` in `A_S`, then
  `(1, b)(1, a) = (1, 1)` is the unit and `(1, a)(1, b) = (1, ab) != (1, 1)`. So `F_3[E_S]` is not
  directly finite.
- **Automaton.** `stable-finiteness-failure-refutes-surjunctivity` at `n = 1` turns this into an
  injective, non-surjective linear automaton over the alphabet `F_3`.
  - `tau_a tau_b = id`, so `tau_b` is injective.
  - If `tau_b` were onto, it would be bijective with inverse `tau_a`, so `tau_b tau_a = id`. The group ring
    acts faithfully, so `ab = 1`, a contradiction.
- **What the chain delivers.** It yields `kun-thom-clifford-cover-nonsurjunctive`, and with it a refutation
  of the goal and of `finite-normal-subgroups-do-not-affect-surjunctivity`. The only input still open is
  the witness pair itself.
- **Quantifier check.** The route needs one graph `S` and one pair. The root claim says "some `G`-invariant
  graph `S`". That matches.

## 7. `mixed-depth-leavitt-lift-is-a-left-zero-divisor` (w4-cohn-gram, 74c21d92f7): PASS

Re-derived independently from the conventions of Section 1 and `1_U [k] = [k] 1_(k^-1 U)`.

**Item 1, `sigma F`.** `P_0 F = 1_(W_2)` and `P_1 F = 1_(W_1)`, so `sigma F = [g_0]1_(W_2) + [g_1]1_(W_1)`.

**Item 1, `sigma D`.**
- `P_0 [h] = [h] 1_(U_(h^-1(0)))` with `h^-1(0) = A`, and `W_1 ⊆ U_A`. So the first term is
  `[g_0 h] 1_(W_1) = [g_1] 1_(W_1)`.
- `P_1 [h^-1] = [h^-1] 1_(U_(h(1)))` with `h(1) = B'`, and `W_2 ⊆ U_(B')`. So the last term is
  `[g_1 h^-1] 1_(W_2) = [g_0] 1_(W_2)`.
- **The first cross term vanishes.** On `W_2`, `mu(0) = mu(B') = 1` forces `mu(1) = 0`, so
  `mu(1 \ B') = 1` and `mu(h(0)) = mu(0 ∪ (1 \ B')) = 0`.
- **The second cross term vanishes.** On `W_1`, `mu(A) = mu(1) = 1` forces `mu(0 \ A) = 1`, so
  `mu(h^-1(1)) = mu(1 ∪ (0 \ A)) = 0`.
- Hence `sigma (F - D) = 0` and `sigma e' = 0`.

**Item 2.**
- `*` is the anti-automorphism `[g] -> [g^-1]` of `F_3[G]`. It fixes `eps_-` and each `P_C`, because
  `tau_C` is an involution. So it fixes `C(M_-, F_3)` pointwise, since those functions commute.
- `sigma* = [g_0^-1] 1_(U_(g_0(0))) + [g_1^-1] 1_(U_(g_1(1))) = tau`.
- `([h]1_(W_1))* = [h^-1] 1_(h W_1) = [h^-1] 1_(W_2)`, so `D* = D`.
- Hence `e' tau = (sigma e')* = 0`.

**Items 3 and 4.**
- `e' != 0`, since its identity grade is `2F` and `W_1, W_2 != ∅`.
- If `z sigma = 1` in any overring, then `e' = z sigma e' = 0`, and dually for `tau`.
- **Gram matrices.** Put `Sigma = (sigma_1, sigma_2)`, a row, and `T = (tau_1, tau_2)^t`, a column. An
  inverse `N` of `T Sigma` gives `(N T)(Sigma v) = v` for columns `v`. With `sigma_j = sigma`, the column
  `v` with `e'` in slot `j` has `Sigma v = sigma e' = 0`, a contradiction. Dually,
  `w (T Sigma) N = w` for rows `w`, and the row with `e'` in slot `i` has `w T = e' tau = 0`.

**Scope.**
- The claim concerns the natural lifts `sigma`, `tau` for every choice of `g_0, g_1`, and every Gram matrix
  that uses one of them. It does not touch Cohn families built from other lifts of `s_0`, `t_0`.
- The remark that the natural lift of `s_1` is a left zero divisor cites Section 3 of the artifact, which
  is not on main at 74c21d92f7. That remark has not been checked. (It now follows from Theorem 3.1; see
  Section 8.)

## 8. Fibre detection and the monomial dichotomy (w4-cohn-gram): PASS

### 8.1 `crossed-product-zero-divisors-are-detected-on-fibres` (Theorem 2.1, Corollary 2.2, Lemma 2.3): PASS

**Covariance.**
- `rho_mu([g]) rho_mu(f) rho_mu([g])^-1 delta_k = f(g^-1 k mu) delta_k = rho_mu(g.f) delta_k`.
- So `rho_mu` is a representation of the algebraic crossed product, with
  `x_mu delta_k = sum_g b_g(k mu) delta_(gk)`.

**1 ⇒ 2.** `xi = rho_mu(y) delta_1 = sum_k d_k(mu) delta_k` is nonzero for a `mu` where some `d_k` is
nonzero, and `x_mu xi = rho_mu(xy) delta_1 = 0`.

**2 ⇒ 1.**
- Choose a clopen `W ∋ mu` on which the finitely many `eta -> b_g(k eta)` are constant.
- Then `x (sum_k xi_k [k] 1_W) = sum_(g,k) xi_k [gk] (k^-1.b_g) 1_W = sum_m [m] 1_W (x_mu xi)_m = 0`.
- The element `y` is nonzero by uniqueness of the normal form.

**2 ⇔ 3.**
- For fixed `xi`, `{mu : x_mu xi = 0}` is clopen, so the non-injectivity locus is open.
- A basic clopen of `M_-` prescribes an odd vector on a finite partition. One point in each atom with
  value `1` gives an odd Dirac sum realizing it, so odd Dirac sums are dense.

**Lemma 2.3.**
- A left invertible element is not a left zero divisor.
- If `xy = 0`, then `(u x v)(v^-1 y) = 0` for units `u, v`.
- Zero divisors of `B` stay zero divisors in `S_-`.

### 8.2 `monomial-crossed-product-elements-are-units-or-zero-divisors` (Theorem 3.1, Corollaries 3.2–3.3): PASS

**Measure facts.**
- `∫ c_x = sum_g lambda(supp b_g) = sum_g lambda(g supp b_g) = ∫ n_x`, by `V`-invariance of the real Haar
  probability.
- `x* = sum_g [g^-1](g.b_g)` gives `c_(x*) = n_x` and `n_(x*) = c_x`.
- Full support: a locally constant function `>= 0` with integral `0` vanishes.

**Cases.**
- **(a)** `x 1_(c_x = 0) = 0`.
- **(b)** `c_x >= 1 >= n_x` with equal integrals forces `c_x = n_x = 1`.
- **(c) Setup.** Let `c_x = 1` and `n_x(nu) >= 2`, with `g != g'` and `mu = g^-1 nu`, `mu' = g'^-1 nu`.
  Then `mu != mu'` because `c_x(mu) = 1`. Put `k = g'^-1 g`, so `k mu = mu'`.
- **(c) Computation.** On a small clopen `W`:
  - `x 1_W = epsilon [g] 1_W`;
  - `x [k] 1_W = sum_(g'') [g'' k](k^-1.b_(g''))1_W = epsilon' [g' k] 1_W = epsilon' [g] 1_W`, since only
    `g'` is supported on `kW`;
  - so `x (epsilon' 1_W - epsilon [k] 1_W) = 0`, and the second factor is nonzero because `k != 1`.
- **(d) Signed permutation.**
  - `x* x = sum [g^-1 g'] ((g'^-1 g).b_g) b_(g')`. A nonzero term at `mu` needs
    `g' mu ∈ g A_g ∩ g' A_(g')`, hence `g = g'`, and then `b_g^2 = 1_(A_g)` sums to `eps_-`.
  - `x x* = sum_g 1_(g A_g) = eps_-`, using `b_g b_(g') = 0` for `g != g'`.

**Case split and right side.** Both case splits are exhaustive. The right side follows from the left side
applied to `x*`, since the hypothesis is `*`-symmetric.

**Corollary 3.2.**
- A unit `sigma_1` forces `tau_2 = 0`, and symmetrically for the other entries.
- A covered non-unit is a two-sided zero divisor, and so is `u x v`, which Lemma 2.3 excludes.

**Corollary 3.3.**
- `q_[0] b'` is left invertible, so it is not a left zero divisor.
- It is not a unit, since `q_[0] x = x` would force `q_[0] = eps_-`.
- So neither `c_x <= 1` nor `n_x <= 1` holds everywhere.

**The `s_1` remark of Section 1.** The natural lift `[g_0]P_0 + [g_1]P_1` with `g_0(0x) = 10x` and
`g_1(1x) = 11x` has `c = 1`, and it is not a unit because `pi` sends it to `s_1`. So it is a two-sided zero
divisor by Theorem 3.1. PASS.

**Scope.** These are filters on entries lying in `B = C(M_-, F_3) x| V` and on their unit multiples. Cohn
entries with supports outside `E x| V` in non-multiplicative form (sums mixing `B` with non-monomial units)
are not covered, and the lane says so.

## 9. `hadamard-spectral-half-is-constant-conjugate-to-swap-idempotent` (w4-hadamard-f3): PASS

**Setup.** Constants `sum c_ab s_a t_b` multiply as matrices. The matrices are:
- `w = [[0,1],[1,0]]`, `d = [[1,0],[0,-1]]` and `wd = [[0,-1],[1,0]]`;
- `h = [[1,1],[1,-1]]`, `u = [[1,0],[1,-1]]` and `hu = [[-1,-1],[0,1]]`;
- `c = [[-1,0],[1,1]]`.

**Item 1**, by hand mod 3:
- `c^2 = I`;
- `cd = [[-1,0],[1,-1]]`, so `cdc = [[1,0],[1,-1]] = u`;
- `c(wd) = [[0,1],[1,-1]]`, so `c(wd)c = [[1,1],[1,-1]] = h`;
- `cw = [[0,-1],[1,1]]`, so `cwc = [[-1,-1],[0,1]] = hu`.

So `q = [c] e_- [c]^-1 = 2 eps_-(1 + [hu])`.

**The span.**
- `[h]^2 = -1_-`, `[u]^2 = 1_-` and `[u][h] = [zhu] = -[hu]`. So `span{1_-, [h], [u], [hu]}` is a subalgebra.
- Its evaluation images `I, h, u, hu` are linearly independent. Coordinates `(1,2)`, `(2,1)`, `(1,1)` and
  `(2,2)` force `b = d`, `c = -b`, `a = b` and `a = -b`, hence all zero. So evaluation is injective on it, and
  on its `F_9`-span.
- `<h, u>` is dihedral of order 8: `h^4 = 1`, `u^2 = 1` and `uhu = zh = h^-1`.

**Item 2.**
- For idempotents `p, q`, put `v = pq + (1-p)(1-q)` and `v' = qp + (1-q)(1-p)`. Then `vq = pq = pv`, and
  expanding gives `v v' = pqp + (1-p)(1-q)(1-p) = 1 - (p-q)^2`. The same holds for `v' v`.
- In `M_2(F_9)`: `p = f_+ -> 2(I + ih) = [[-1-i,-i],[-i,-1+i]]` and `q -> 2(I + hu) = [[0,1],[0,1]]`.
- So `p - q = [[-1-i,-1-i],[-i,1+i]]`. Squaring by hand gives `(1,1) = (2i) + (i - 1) = -1`,
  `(1,2) = 2i - 2i = 0`, `(2,1) = 0` and `(2,2) = (i - 1) + 2i = -1`. So `(p-q)^2 = -I`.
- Hence `v v' = v' v = -1_-`, and `v^-1 = -v'`.

**Item 3.** `W e_- W^-1 = v q v^-1 = f_+`, using `vq = pv`.

**Route `f9-hadamard-fullness-from-swap-corner-fullness`.**
- `(c W^-1) f_+ (W b) = c e_- b = 1_-`. PASS.
- The claimed equivalence with `ternary-anti-invariant-swap-corner-is-full` closes through the existing
  chain `hadamard-spectral-fullness-gives-f9-cohn-family` -> `f9-cohn-family-descends-to-anti-central-summand`
  -> `anti-central-cohn-family-gives-swap-corner-fullness`. Its first two links are PASS by `w3-vf-linear`.
  The last link was not re-checked here.

**Reading.** The `F_9` Hadamard line is the swap corner itself, up to an explicit constant unit. This agrees
with w3-corner-cohn-b's collapse audit.

## 10. `simple-group-rank-functions-are-augmentation-or-detecting` (w4-binary-cyclic): PASS

**`N_rk` is a normal subgroup.**
- `1 - [xy] = (1 - [x]) + [x](1 - [y])`, subadditivity, and invariance of `rk` under multiplication by units
  close `N_rk` under products.
- `1 - [x^-1] = -[x^-1](1 - [x])` gives inverses, and `1 - [g x g^-1] = [g](1 - [x])[g^-1]` gives conjugates.

**Descent.**
- The kernel of `K[Γ] -> K[Γ/N]` is the left ideal spanned by `[y](1 - [n])`, all of rank 0.
- A matrix whose entries all have rank 0 has rank 0, by subadditivity over single-entry matrices.
- So `rk` is constant on lifts and descends to a Sylvester matrix rank function on `K[Γ/N]`.

**The dichotomy.**
- If `N = Γ`, the quotient is `K`. Every matrix over `K` is equivalent to `diag(I_r, 0)`, so `rk` is the
  normalized rank of the augmentation.
- If `Γ` is simple, then `N ∈ {1, Γ}`.

**The consequence.**
- The null ideal `I = {a : rk(a) = 0}` is two-sided, and `K[Γ]/I` carries a faithful rank.
- `c e_H b = 1` forces `rk(e_H) = 1`, hence `rk(1 - e_H) = 0` and `[h] ≡ 1` modulo `I`. So `h ∈ N_rk`.
- On a simple `Γ` that forces the augmentation rank, which is consistent because `ε(e_H) = 1`.
- The input `full-averaging-idempotent-kills-its-element-in-rank-models` was not re-checked here. The step
  it supplies is the one just displayed.

## 11. `sofic-amalgam-finite-subgroup-idempotent-traces-are-strict` (w4-kap-join): PASS, with one precision

**Embedding.** The inclusions `H_i ⊆ G` agree on the `D_ij`, so `A -> G` exists.
- `H_i -> A -> G` is the inclusion, so `H_i -> A` is injective.
- An element of `ι_i(H_i) ∩ ι_j(H_j)` maps into `H_i ∩ H_j = D_ij`, so it lies in `ι(D_ij)`.

**Rectangles.** `ab = a'b'` with `a, a' ∈ H_i` and `b, b' ∈ H_j` gives `a'^-1 a = b' b^-1 ∈ D_ij`, which already
holds in `A`. So `A -> G` is injective on `ι_i(H_i) ι_j(H_j)`. That rectangle contains the supports of `x_i x_j`,
`x_i` and `x_j`, and `H_j H_i` contains those of `x_j x_i`. So the laminar table holds in `F_p[A]`.

**Precision, on step 2 of the route.** The members `x_i`, and `1`, may satisfy linear relations in
`M_n(F_p[G])` that do not hold in `A`. Some atoms may even vanish in `G` and not in `A`. The proof must lift `d`
through its atom expansion, not through its coefficients, and step 2 does exactly this.
- `d = sum eps_k a_k` with `eps_k ∈ {0,1}`, because the nonzero atoms are orthogonal idempotents.
- `d_A = sum eps_k a_k^A` is an idempotent. It is nonzero because it maps onto `d`.
- The class identity `[a_k] = [y] - sum [children]` holds in both rings with the same integers.

**Rank.**
- The Elek–Szabó rank of a sofic approximation of `A` is faithful and additive on orthogonal idempotents.
- On each finite `H_i` the approximation may be taken exact and free on a density-one union of regular
  orbits. There `F_p^N ⊗ F_p^n` is `F_p[H]^n` per orbit, so `rk(x) = dim(x F_p[H]^n)/|H| = r(x)`, with
  `rk(I_n) = n`.
- Hence `rk(d_A) = m n + sum m_i r(x_i) = t_p([d S^n])`, and faithfulness makes it positive.
- A defect `I - ac` with `ca = I` has class `[S^(n+m)] - [ac S^(n+m)] = 0`, hence lifted trace 0.

**Forests.** When the nontrivial intersections form a forest, `A` is a free product of trees of finite groups,
hence virtually free and sofic. The case `k = 1` is always a forest. So a difference of two nested
finite-subgroup idempotents is never a defect, at any join.

**Reading.** This closes the "infinite join" survivor of `mixed-finite-subgroup-defects-need-infinite-generation`
for two subgroups. A literal laminar defect needs three or more finite subgroups whose intersection graph has
a cycle, and a non-sofic amalgam.

**Addendum (be33019479).**
- The lane's revised step 2 now lifts `d` through its atoms and says why the coefficient expression can fail. This
  is the precision above, already incorporated.
- **New Theorem 2.6 (sofic realizations): PASS.** Let `A -> Γ` be a homomorphism to a sofic group that is injective
  on `U = ∪ H_s`.
  - It induces a ring map, which carries the table and the atoms.
  - It is injective on each `H_s`, so each `r(x_i)` is unchanged.
  - `d_A` is supported on `U`, so its image is nonzero.
  - The faithful sofic rank of `Γ` then gives `t_p([d S^n]) > 0`.

## 12. `anti-central-k0-states-equal-lifted-trace-on-signed-thompson` (w4-hadamard-f3): PASS

**Part 1.**
- `tau_(X\C) = z tau_C` gives `[tau_(X\C)] = -[tau_C]` in `S_-`, so `P_(X\C) = 1_- - P_C`.
- `V` is transitive on proper nonempty clopens, so `P_(X\C)` is conjugate to `P_C`. Hence `s(P_C) = 1/2`
  for every proper `C`.
- At a prefix code with `N` atoms, let `x_v = s(1_v)` over the `2^(N-1)` odd vectors `v`. Then
  `sum_(v(T)=1) x_v = 1/2` for every proper `T`, and `sum_v x_v = 1`.
- So `xhat(T) = sum_v x_v (-1)^(v(T))` vanishes on proper `T`, `xhat(∅) = 1` and `xhat([N]) = -1`. The
  characters of the odd coset are indexed by `T` modulo complement, so inversion gives `x_v = 2^-(N-1)`,
  the Haar mass.
- Every clopen of `M_-` is a finite union of atoms at some level.

**Part 2.**
- Embed `K`, up to `Γ`-conjugacy, in `E^(m') x| F` with `F` permuting level-`m'` cylinders.
  - That finite subgroups of `V` are conjugate into level permutation groups is standard and was not
    re-derived here.
  - The lifted trace `2 dim(p F_3[K]^n)/|K|` is unchanged by enlarging `K`, because `F_3[K']` is free over
    `F_3[K]`.
- The anti-central algebra is `C(O_(m'), F_3) x| F`, a sum of orbit blocks. On a free block `M_|F|(F_3)` a
  minimal idempotent is conjugate to a point atom `1_v`.
  - `s(1_v) = lambda(v) = 2^(1 - 2^(m'))`, by Part 1.
  - `t(1_v) = 2|F| / (2^(2^(m')) |F|) = 2^(1 - 2^(m'))`, since `1_v B'` has dimension `|F|`.
- Split `p = p 1_f + p 1_(nf)` along the central free and non-free idempotents. Then
  `|s([p]) - t([p])| <= 2 n lambda(nf)`.
- Under refinement a nontrivial `g` moves `2^j` times as many cylinders, so the fixed odd vectors have mass
  at most `2^-(2^(j-1))`. So `lambda(nf) -> 0`, and `s = t` on `[p]`.

**Scope.** This fixes every state on the locally finite part of `H`. The remark about the semidihedral group
`<w, d, h>` (split `t` open) is prose and was not checked.

## 13. Routes into Kaplansky failure and into the binary rank function: PASS

**`laminar-finite-subgroup-defect-gives-kaplansky-failure`** (w4-kap-join).
- `[P] = 0` gives `P (+) S^m ≅ S^m`.
- With `a = phi^-1 iota` and `c = pi phi`, `c a = pi iota = I_m`, while `a c` has kernel `phi^-1(P (+) 0) != 0`.
- So `M_m(S)` is not directly finite, and `leavitt-stable-finiteness-equals-direct-finiteness` gives the scalar
  failure.
- The route is decision-level in shape. Its only input is the open defect claim, which Section 11 restricts to
  cyclic, non-sofic configurations.

**`nonaugmentation-rank-function-from-f2-linear-soficity`** (w4-binary-cyclic).
- A linear sofic embedding into a rank ultraproduct, with `rho(1 - g) >= κ > 0` for `g != 1`, pulls back to a
  Sylvester matrix rank function on `F_2[R^x]` with `rk(1 - [x]) >= κ`.
- The augmentation rank of `1 - [x]` is 0, so the pulled-back rank is not the augmentation rank.

## 14. `oriented-clifford-skew-rings-embed-in-matrix-lamp-wreath` (w4-clifford-df): PASS; one false Attempts line corrected

**Spin embedding.** Take `s_x = diag(1,-1)` and `p_x = [[0,1],[1,0]]` at each site, so `s^2 = p^2 = 1` and `sp = -ps`.
- **Square.** `iota(c_x)^2 = (p_x s_x^q)^2 · prod s_y^2 = (-1)^(q(x))`, since `(ps)^2 = -1`.
- **Signs.** `iota(c_x)` and `iota(c_x')` anticommute at site `x` iff `x ∈ N+(x')`, and at site `x'` iff
  `x' ∈ N+(x)`. So the total sign is `(-1)^(b_S(x,x'))`, because each edge is oriented exactly once.
- **Equivariance.** It follows from the invariance of the orientation and of `q`. `G` acts on the lamps by
  `c_x -> c_(gx)`, and this is well defined because the relations are invariant.
- **Injectivity.** `iota(c_T)` is, up to sign, a Pauli string whose `p`-support is exactly `T`. Pauli strings
  form a basis of `tensor M_2`, and both crossed products are free over their lamp algebras.

**Compressor graph.** `psi(gΓ) = g u^-1 Γ` is well defined because `uΓu^-1 ⊆ Γ`.
- `u ∉ Γ`, since otherwise `uΓu^-1 = Γ`.
- `u^2 ∉ Γ`, since `u^2 Γ u^-2 ⊆ uΓu^-1 ⊊ Γ`.
- So there are no fixed points and no 2-cycles, and the orientation is invariant with out-degree 1.
- **Nondegeneracy.** Let `T` be finite and nonempty, and `t ∈ T`. Then `t` has infinitely many children, and at
  most `|T|` points are parents of points of `T`. So some child `c ∉ T` has no child in `T`, and
  `N(c) ∩ T = {t}` is odd.

**Matching and complete graph.**
- `tensor_X M_2(k)` is the Clifford algebra of the perfect matching on `X × {s,p}`.
- Over the complete graph, even subsets pair by `|v ∩ w| mod 2`. So `c_(x1)c_(x2)` and `c_(x2)c_(x3)` generate a
  quaternion algebra at each `x`, commuting across different `x`.
- Quaternion algebras over finite fields split. A uniform choice of anticommuting involutions inside each copy
  gives an equivariant unital map `tensor M_2 -> C_K`. It is injective because the source is simple.

**Commutative form.** `M_2(k) = k^2 x| Z/2` when `char k != 2`.

**Route `oriented-clifford-skew-rings-sf-from-matrix-lamp-wreath`: PASS.**
- The Kun–Thom `G` is residually finite, so `F_p[G]` is stably finite.
- A unital subring of a stably finite ring is stably finite.

**Correction to `matrix-lamp-wreath-algebras-are-stably-finite` (OPEN), `## Attempts`, "Sofic base".**
- **What main says.** "`H_X` is locally finite. So when `G` is sofic, `H_X semidirect G` is amenable-by-sofic,
  hence sofic".
- **Why it is false.** Amenable-by-sofic does not imply sofic.
  - The Kun–Thom wreath `F_2 wr_X G` has abelian lamps and residually finite `G`, and it is not sofic.
  - It is a subgroup of `(H_X/Z) x| G`, since `H_X/Z = (F_2^2)^(X)` contains the `s`-lamps.
  - A quotient of a sofic group need not be sofic, but the bullet's conclusion would make `B_X` stably finite
    for the Kun–Thom pair. That would settle the open claim, contradicting the lane's own next sentence.
- **Correct form.** `B_X` is stably finite whenever `H_X x| G` is sofic, for example when `G` is amenable
  (sofic-by-amenable is sofic). For the Kun–Thom pair this gives nothing.
- Landed forward on the node with a correction line. The open status is unchanged.

## 15. `anti-central-k0-states-can-be-chosen-transpose-invariant` (w4-hadamard-f3): PASS

**Item 1.** Put `alpha(g) = (g*)^-1`, with `s_i* = t_i`. This is an automorphism of `G`.
- A monomial unit `sum S[α_i]T[β_i]` has `g* = g^-1`, so `alpha(g) = g`.
- `tau_C* = tau_C = tau_C^-1`, so `alpha(tau_C) = tau_C`.
- `delta(g)* = delta(g*)` and `delta` is a homomorphism, so `alpha∘delta = delta∘alpha`.

**Item 2.** On constants `*` is the transpose.
- `h` is symmetric, so `alpha(h) = h^-1 = h^3 = zh`.
- `alpha(wh) = w·zh = z wh` and `alpha(dh) = z dh`, so `[wh] -> -[wh]` and `[dh] -> -[dh]` in `S_-`.
- `c_2 = -eps_-(1 + [wh] + [dh])` goes to `-eps_-(1 - [wh] - [dh]) = eps_-(2 + [wh] + [dh]) = eps_- - c_2 = c_1`.

**Item 3.**
- `s -> s∘alpha_*` and `s -> 2 s∘F_*` map states to states. They commute because `alpha_*` commutes with `F_*`,
  as it fixes `e_-` and `[d]` and commutes with `delta_*`.
- The state space is compact and convex, so Markov–Kakutani gives a common fixed point.
- Invariance gives `s(c_1) = s(c_2)`, and `c_1 + c_2 = eps_-` gives the values `1/2`.

## 16. Further Clifford landings (w4-clifford-df) and binary-cyclic Section 2.2: PASS

### 16.1 `nondegenerate-clifford-skew-rings-have-no-finite-dim-reps`: PASS

- **Simplicity.** Take `a = sum lambda_v c_v` of minimal support in a nonzero ideal, with `v0 != v1` in its
  support.
  - Nondegeneracy gives `w` with `b(v0 + v1, w) = 1`.
  - `a - (-1)^(b(v0,w)) c_w a c_w^-1` has coefficient `lambda_v (1 - (-1)^(b(v0,w) + b(v,w)))`. That is `0` at
    `v0` and `2 lambda_(v1) != 0` at `v1`, which contradicts minimality.
  - So `a` is a unit monomial, and the ideal is everything.
- **No finite-dimensional representations.** A unital map `C_S -> M_n(L)` extends `L`-linearly to
  `C_S tensor L`. It is injective because the source is simple, which is impossible because the source is
  infinite-dimensional.
- **Targets.** Algebras with a character, and marked-site rings over residually finite bases, have
  finite-dimensional representations.
- **Scope.** Only unital maps are excluded. A non-unital map into a corner killed by the augmentation is not
  addressed, and the claim does not assert it.

### 16.2 `clifford-skew-ring-rank-models-give-linear-sofic-wreath`: PASS

**Doubling.**
- `(c_x tensor c_x^op)^2 = 1`.
- In `c_x c_y tensor (c_y c_x)^op` the two signs `(-1)^b` cancel, so different lamps commute.
- `u_g tensor (u_(g^-1))^op` is a homomorphism, and conjugation sends `c_x tensor c_x^op` to
  `c_(gx) tensor c_(gx)^op`.
- Distinct `vg` give distinct first tensor factors, so the map is injective.

**Gate.**
- `X tensor X^-T` acts on `M_n` by `M -> X M X^-1`, so its `±1`-eigenspace is `{M : XM = ±MX}`.
- That space has dimension at most `n max_λ g_X(λ)`, so the normalized rank distance is at least
  `min_λ rho(X - λ)`.
- If this tends to 0, `c_v u_g` is rank-central, hence central in `A_S` by injectivity. That is impossible
  for `vg != 1`: faithfulness handles `g != 1`, and nondegeneracy handles `g = 1, v != 0`.

**Converse.** It relies on the linear-sofic group algebra embedding recorded in
`linear-sofic-group-algebra-is-stably-finite`, which was not re-checked here, then compression by `(1 - eps)/2`.

### 16.3 binary-cyclic artifact Section 2.2 (no detecting maps into `M_n(D)`): PASS

- A detecting `rk` makes `φ` injective on `R^x`.
- For `x` of order `2^k > 2n`, `N = φ(x) - 1` is nilpotent, so `N^n = 0`.
- With `2^(j-1) < n <= 2^j`, `φ(x)^(2^j) = 1 + N^(2^j) = 1` in characteristic 2. So `x` has order at most
  `2^j < 2n < 2^k`, a contradiction.
- Section 2.1 (no rank function on `R`) is the standard `[1] = 2[1]`.

## 17. HNN transfer for triangular lifts (w4-kap-triangular; a43847b206, a9a225b5d6): PASS

### 17.1 `finite-subgroup-idempotent-ideals-admit-no-proper-group-shift`: PASS

- **Equivalences.** `[g]eB ⊆ eB` iff `e[g]e = [g]e` iff `(I - e)[g]e = 0`.
- **Transfer.**
  - In `G`, `agb = a'gb'` iff `a'^-1 a ∈ g K g^-1 ∩ K = D`, so `k[K] tensor_(k[D]) k[K] -> k[KgK]` is injective.
    The matrix tensor `(I - e) tensor e` therefore vanishes in the tensor product.
  - In the HNN extension `H`, the same linear map to `k[KtK]` is well defined. (By Britton's lemma it identifies
    exactly `D`.) So `(I - e)[t]e = 0` in `M_n(k[H])`.
- **Invertibility.** With `x = [t]e + (I - e)` and `y = e[t^-1] + (I - e)`, `yx = I + N`, where
  `N = e[t^-1](I - e)` satisfies `N^2 = 0`. Direct finiteness makes `x` invertible, so `xB_H = B_H`.
- **Modular law.** `[t]eB_H ⊆ eB_H` gives `eB_H = [t]eB_H + (eB_H ∩ (I - e)B_H) = [t]eB_H`.
- **Back to `G`.** Push `e = [t]e b` down to `G`.
- **Corollary B.** An HNN extension of a finite group is virtually free, so its matrix algebras are directly finite.

### 17.2 `finite-support-triangular-two-piece-s0-lifts-do-not-exist`: PASS

- **First case.** If `Ê[h](1 - Ê) = 0`, then `[h](1 - Ê)A ⊆ (1 - Ê)A`, and Corollary B makes it an equality.
  Evaluation gives `q R = P_1 R` for `q = P_(h(1))`, which forces `q = P_1`. But `h(1) = g_1^-1(01)` is a proper
  subset of `1`, because `g_1` maps `1` onto `01 ∪ 1`.
- **Second case.** `P_(h^-1(0)) = P_(g_2^-1(00))` is a proper subset of `P_0`.
- These are the strict containments of `[TP]` Remark 2.5. They were re-derived here from the cylinder data, not
  read from the source.

### 17.3 `triangular-piece-lifts-need-non-directly-finite-shift-group`: PASS

- **Left inverse.** `b = sum E_i[g_i^-1]` gives `ba = I + N`, with `N = sum_(i != j) X_ij` supported on an acyclic
  digraph. Path products vanish after `m` steps, so `a` is left invertible.
- **Transfer.** Each `X_ij = 0` with `(i,j) ∈ Z` lives on one double coset and transfers to `H`, as in 17.1. Then
  `a_H = sum [t_i]E_i` is left invertible in `F_2[H]`.
- **Contradiction.** If `F_2[H]` were directly finite, `a_H` would be invertible, and its image `s_0` would be
  invertible in `R`, which is false.
- **Forest corollary.** Change the letters along a spanning forest of `Γ`. Relations for `(i,j)` and `(j,i)`
  coincide, and each remaining relation is an HNN relation with a finite associated subgroup. So `H_Z` is
  virtually free.
- The cycle case, "one 2-cell per cycle", is descriptive and was not re-derived.

## 18. Peeling and hyperfinite graphings (w4-cohn-gram): PASS

### 18.1 `triangular-crossed-product-elements-are-units-or-zero-divisors`: PASS for parts 1–2

- **Back-substitution.** A point removed in round `s` is the one live point of a unique column `k_s`. So `δ_p` is
  `x_mu δ_(k_s)` minus terms on earlier points, and by induction every vector on removed points is in the image of
  earlier columns.
- **Stops.**
  - A dead column gives the kernel vector `δ_k - η`.
  - Two columns sharing their one live point, with entries `d` and `d'`, give `d' δ_k - d δ_(k') - η`.
  - Both vectors are nonzero, and Theorem 2.1 finishes.
- **Termination.**
  - `D` has `c_D = 1`. It also has `n_D <= 1`, since a shared removal point would have stopped the peeling. Haar
    balance gives `n_D = 1`, so `D` is a signed permutation unit.
  - `D^-1 N` maps each round-`r` column to earlier columns, so it is nilpotent in every fibre. The fibres are
    faithful, so it is nilpotent in `B`.
- **Not re-derived.** Part 3 (equal live measures) and Example 4.3 (the three-piece lift stops in round two).

### 18.2 `hyperfinite-coefficient-graphing-excludes-corner-witnesses`: PASS

- **Expansion.** Left inverses in `B` act on every orbit module, so the columns at `J` are injective:
  `2|J| <= |N_1(J) ∪ N_2(J)|` in case 1, and `|J| <= |N_x(J) ∩ U_[0]|` in case 2.
- **Exhaustion.** Suppose `R_Γ = ∪ R_n`. The degree is bounded, so `lambda(∂_n) -> 0`. Interior points have all
  their column points in their class.
- **Transport.** `R_n` is a finite measure-preserving subrelation of the `V`-orbit relation. So
  `lambda(interior) = ∫ |C°|/|C| <= 1/2`, which contradicts `lambda(∂_n) < 1/2`.
- **Case 2 graphing.** The graphing of `x = q_[0] b'` is a subgraph of that of `b'`.
- **Degree two.**
  - A finite component `K` gives `2|K| <= |K|`, and a segment of `m >= 3` points has at most `m + 2 < 2m` column
    points.
  - In case 2, every infinite class meets `U_[1]` in at most two points, so `U_[1]` is null. That contradicts
    `lambda(U_[1]) = 1/2`.

## 19. `infinite-clique-clifford-algebras-have-no-bounded-spin-models` (w4-clifford-df): PASS

- **Supports meet.** If `a` and `b` have disjoint supports they commute. With `ab = -ba` that gives `2ab = 0`, so
  `ab = 0`. Since `a^2` is invertible, `a` is invertible, hence `b = 0`, which is impossible. So supports pairwise
  meet.
- **Kernel.** An infinite family of sets of size at most `d` contains an infinite Δ-system. Its kernel `K` is
  nonempty because the supports pairwise meet.
- **Kernel spaces.** Write `x = sum π_i tensor q_i` with the `q_i` independent in `M_petal`. On disjoint petals the
  `q_i tensor q'_j` are independent, so `xy = -yx` iff `π_i π'_j = -π'_j π_i` for all `i, j`. So `Π_x` and `Π_y`
  anticommute elementwise.
- **Pigeonhole.** `M_K` is finite over a finite field, so `Π_x = Π_y = Π` for some `x != y`.
  - Then `Π` anticommutes with itself, and `a^2 = -a^2` forces `a^2 = 0` in odd characteristic.
  - Products of more than `dim Π` basis elements repeat a letter, so the algebra `N` generated by `Π` is
    nilpotent.
- **Contradiction.** `x^2 ∈ N tensor M_petal` is nilpotent, but it is invertible.
- **Scope.**
  - Equivariant maps with finitely many site orbits have bounded supports.
  - Maps with unbounded supports are not excluded.
  - The invalidated route `kun-thom-clifford-skew-rings-sf-from-matrix-lamp-wreath` relied on bounded-support
    local embeddings.

## 20. Section 6 of the zero-divisor artifact (w4-cohn-gram, 3432f94fb0): PASS

- **Lemma 6.1.**
  - `F_3[G \ H]` is an `F_3[H]`-sub-bimodule, and `eps_-` is central. So `P(ζ x) = P(ζ) x` for `x ∈ B`, and
    `P(ζ) = eps_- P(ζ) ∈ B`.
  - A left inverse in `S_-` therefore projects to one in `B`.
- **Proposition 6.2.** `x_mu` has finite radius, so the identity `ρ_mu(ζ) ρ_mu(x) = 1` holds entrywise as matrix
  identities, hence on all of `F_3^V`. So `x_mu` is injective on all functions.
- **Corollary 6.3.**
  - **Regularity.** Equal live measures give `∫ mult = 2 λ(Col_r) = 2 λ(Pt_r)`, and `mult <= 2` forces
    `mult = 2`. So each component is a cycle or a bi-infinite line.
  - **Lines.** Propagation along a line gives an infinite kernel vector of the live operator. Locally finite
    back-substitution extends it to a kernel vector of `x_mu` on `F_3^V`, which Proposition 6.2 forbids.
  - **Cycles.** Cycles have bounded length. A singular block gives a finite kernel vector. If every block is
    invertible, `x` is a unit, which is excluded.
- **Dependency.** This uses part 3 of Theorem 4.1 (equal live measures), which Section 18.1 did not re-derive.
  It is plausible, since removed columns and removed points correspond through `V`-translates.

## 21. `triangular-piece-lifts-need-non-directly-finite-shift-group`, artifact Theorem 5.1 (w4-kap-triangular): PASS

- `c x = I` in `F_2[H]` maps to `ψ(c) ψ(x) = I` in `F_2[Γ]`, which is directly finite because `Γ` is sofic.
- So `ψ(1 - xc) = 0`.
- `1 - xc` is supported on `S = {1} ∪ supp(x) supp(c)`, and `ψ` is injective on `S`, so `1 - xc = 0`.
- Then `x` is invertible, and its image `s_0` would be invertible in `R`, a contradiction.
- The matrix version is the same, using stable finiteness of `F_2[Γ]`.

## 22. Deligne triple cover (w4-deligne-twisted, 54ff69eb94): Lemma 1.1 and Proposition 3.1 PASS; Theorem 2.1 pending

- **Lemma 1.1.** A nonzero finite-dimensional `A_j`-module gives `E_3 -> GL_n(F)` with `z -> w^j ≠ 1`. The image is
  finitely generated and linear, hence residually finite (Malcev). So some finite quotient of `E_3` keeps `z`,
  which contradicts `Res_fin(E_3) = ⟨z⟩`.
- **Proposition 3.1.**
  - Følner sets of `X` give almost invariant unit vectors in `l^2(X)`. Property (T) of `Γ = Sp_4(Z)` then gives an
    invariant vector, hence a finite orbit.
  - The stabilizer of a basis line has finite index. Its preimage `L` acts on the line by `χ` with `χ(z) = w^j`.
  - `L` has (T), since `E_3` does as a finite central extension, so `L^ab` is finite. So `ker χ` has finite index
    in `E_3` and misses `z`, a contradiction.
- **Theorem 2.1: PASS**, every constant re-derived.
  - **2 => 1, tensor camouflage.**
    - The defect equals `w^(j(i+k)) (ρ(g)ρ(h) - w^(ja) ρ(gh)) tensor π(gh)`, so its rank is at most `ε`.
    - A cyclic block `C_o` gives `v_(i+1) = X v_i` and `X^o v_0 = v_0`, so the kernel has dimension at most `d`
      with no eigenvalue argument, even when `p | o`. Hence `r >= 1 - 1/o >= 1/2`.
    - For `z^i`, invertibility of `ρ(1)` gives `r(ρ(1) - 1) <= ε`, so `r(σ(z^i) - 1) >= 1 - ε`.
  - **1 => 2, cutting into a sector.**
    - `M^3 - 1 = (M^2 - σ(z^2))M + (σ(z^2)M - σ(1)) + (σ(1) - 1)` has rank at most `3ε`. With `U` the kernel of
      `M^3 - 1`, `Z = M|_U (+) 1_W` has `Z^3 = 1` and `r(Z - M) <= 3ε`.
    - The commutator bounds are 8ε, 16ε and 24ε. The heavy sector has `r(P_j) >= (δ - 3ε)/2`, because
      `Z - 1 = (w - 1)P_1 + (w^2 - 1)P_2`.
    - **Compression.** The error terms are 24ε from `E_1`, then `ε + ε`, then `7ε` from `σ(z^a)` to `Z^a`
      (`r(M^2 - Z^2) <= 6ε`), for a total of 33ε.
    - **Invertibility.** The nullity of `ρ(g^-1)` is at most 34ε. Repairing three factors adds 102ε, for 135ε
      in all.
    - **Uniform `j`.** One `j` works everywhere, by monotonicity in `(B, ε)` and directedness.
  - **2 <=> 3.** `ρ^v = (ρ^T)^-1` has multiplier `w^((3-j)a)`, and `r(X^-1 - Y^-1) = r(X - Y)`.
  - **Scope.** The separation constant `δ` of the linear sofic model is fixed, so `66ε/(δ - 3ε) -> 0`. The
    corollary's appeal to `linear-sofic-group-algebra-is-stably-finite` was not re-checked.

## 23. Addenda and further requests

### 23.1 Section 12 addenda (w4-hadamard-f3): the trust input is removed, and Remark 2.3 passes

**No normal form needed.** The author's path does not use "finite subgroups of `V` are conjugate into level
permutation groups".
- `E^(m)` is generated by `z`, the `F`-translates of the `e_k`, and the `F`-translates of `τ_β` with `|β| = m`.
  So it is `F`-invariant by construction.
- For `g != 1`, pick a cylinder `[α]` with `g[α] ∩ [α] = ∅`. The `2^(m-|α|)` elements `τ_β + g·τ_β`, for `β`
  extending `α`, have disjoint supports. So `dim (1 - g)E^(m) >= 2^(m-|α|)`, and the odd characters fixed by
  `g` have mass at most `2^(1 - 2^(m-|α|))`.
- So Section 12, Part 2, holds without the standard fact.

**Remark 2.3: `<w, d, h>` is not conjugate into `E x| V`. PASS.**
- **Freeness.** Take `a = τ_C f` with `a^4 = z`. Then `f^4 = 1` and `C + fC + f^2C + f^3C = X`, so every orbit
  sum is odd. At a fixed point of `f^2` the sum is even. So `<f>` acts freely.
- **Conjugacy.** Take a clopen fundamental domain `D_0` and put `D = D_0 ∪ f^2 D_0`. Then `D + fD = X`, so
  `τ_D a τ_D = τ_(D + fD) τ_C f = z a`. So every such `a` is conjugate to `-a`.
- **`hw` is not.** `hw = [[1,1],[-1,1]]` has trace 2 and determinant 2, so it satisfies `x^2 + x - 1 = 0` in
  `R`. If `hw` were conjugate to `-hw`, then `-hw` would satisfy it too, and subtracting gives `2hw = 0`,
  which is impossible.

### 23.2 Theorem 4.1 part 3 and Example 4.3 (w4-cohn-gram): PASS

**Part 3.** The removal sets `E_(r,g)` are clopen. Their translates `g E_(r,g)` are disjoint, since no shared
removal point survives without a stop, and `lambda(g E) = lambda(E)`. So removed columns and removed points
have equal measure, and so do the live ones.

**Example 4.3.** Use types on `(000, 001, 01, 1)`, with `g_1: 00->000, 01->001, 10->01, 11->1`,
`g_2: 00->000, 01->001, 11->01, 10->1`, and `g_3: 01->1, 1->01`, fixing `000` and `001`.
- **Incoming columns.** A point `ν = (a, b, c, d)` receives column `i = 1` iff `a = 1`, `i = 2` iff `b = 1`, and
  `i = 3` iff `c = 1`. The weights are:
  - `w_1 = 1 + b + [c + d odd]`;
  - `w_2 = a + 1 + [c + d odd]`;
  - `w_3 = [a + b odd] + d + 1`.
- **Round one.**
  - Types `(1,0,0,0)`, `(0,1,0,0)` and `(0,0,1,0)` each receive a single column, of weight 1.
  - Types `(1,1,1,0)`, `(1,0,1,1)` and `(0,1,1,1)` each receive exactly one weight-one column, plus weight-three
    columns.
  - `(0,0,0,1)` receives none, and `(1,1,0,1)` receives two weight-three columns. Those two stay live.
- **Round two.** A weight-three `μ` has `g_1 μ` and `g_2 μ` of types `(1,1,μ10,μ11)` and `(1,1,μ11,μ10)`, so
  exactly one of them is `(1,1,0,1)`. `g_3 μ` has `c = 1`, so it is not live. That point has two live columns,
  `g_1^-1 ν != g_2^-1 ν`, so the peeling stops.

### 23.3 `homomorphic-solvable-alphabet-ca-reduce-to-stable-finiteness` (w3-strategist-neg, 8d715c6082): PASS

- **Filtration.** A homomorphic automaton has a homomorphic local rule `μ: K^S -> K`. Since
  `[K^S, K^S] = [K,K]^S` and homomorphisms preserve derived subgroups, `μ` preserves the derived series. On
  abelian layers it preserves the `p`-primary parts and `p^j L`, so the layers are `F_p`-spaces with `F_p`-linear
  induced automata.
- **Induction.**
  - If `τ` is injective, `τ_N` is injective, hence surjective by induction.
  - `τ_Q` is injective: if `τ(x) ∈ N^G`, then `τ(x) = τ(n)`, so `x = n`.
  - Given `y`, write `y = τ(x) m` with `m = τ(n)`, so `y = τ(xn)`.
- **Base case.** Linear surjunctivity over `F_p^n` from direct finiteness of `M_n(F_p[G])`. This is the
  Ceccherini-Silberstein–Coornaert equivalence and was not re-derived.
- **Converse.** It is the existing node.
- **Scope.** A homomorphism `S^m -> S` with `S` nonabelian simple is trivial, or a projection followed by an
  automorphism, because normal subgroups of `S^m` are products of factors. Excluding these layers is correct.
- Section 1.5 (the anticommuting pair in `G_3`) was not checked.
