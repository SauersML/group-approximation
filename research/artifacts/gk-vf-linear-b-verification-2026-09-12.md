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
  - **Scope.** The separation constant `δ` of the linear sofic model is fixed, so `66ε/(δ - 3ε) -> 0`.
  - **Corollary 2.5: PASS.** An `F_p` rank model is an `F`-model for every `F` of characteristic `p`, because normalized
    rank is invariant under extension of scalars. `linear-sofic-group-algebra-is-stably-finite` is established on main,
    and that step was not re-derived here.

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

## 24. `anti-central-state-exists-iff-lifted-trace-relatively-positive` (w4-trace-state, 3a85cf1f0f): PASS

**Proposition 1.1.**
- **Parts 1–2.** `t_3` is additive and equals `dim/|K|` on finite-subgroup projectives. `t_3(eps_-) = 1/2` over `<z>`, so
  `s_3(u) = 1`.
  - *Clopens.* `E_c` has order `2^n` and `2^(n-1)` odd characters, so `trl(1_U) = 2m/2^n = lambda(U)`.
  - *Semidihedral blocks.* `eps_- F_3[SD]` has dimension 8 and equals `M_2 x M_2`. Each block unit has
    `trl = 2·4/16 = 1/2`.
- **Part 3, halving.**
  - *Idempotent.* `e~_- = (1-z)(1+w)/4` is idempotent, since `((1±x)/2)^2 = (1±x)/2` for involutions. It lifts
    `e_- = eps_-·(1+w)/2`, because `2 = 1/2` in `F_3`.
  - *Commutation.* `w δ(g) = s0 g t1 + s1 g t0 = δ(g) w`, and `z` is central. So `e~_- δ_*(P)` is an idempotent lifting
    `psi(p)`.
  - *Identity coefficient.* It equals `(a_1 - a_z + a_w - a_(zw))/4`, where all four elements are involutions.
    - `a_w = a_(zw) = 0`, because `M(δ(g))` is diagonal and `M(w)`, `M(zw)` are off-diagonal.
    - `a_z = -a_1`, because `e~_- P = P` forces `zP = -P`.
    - So the coefficient is `a_1/2`, and summing over `i` gives `t_3(psi(p)) = t_3(p)/2`.
  - *Not re-derived.* The Morita step `F_*([p]) = [psi(p)]` was read from census §7.2 as stated.
- **Part 4.** `alpha` fixes `z` and preserves identity coefficients.

**Corollaries 1.2–1.3.**
- *No equality relation.* `Q -> Q_3` is injective.
- *Witness class.* With `f = (e_- b)(c e_-)`, `f^2 = f`, `f <= e_-`, and `f ~ eps_-` via `x = e_- b`, `y = c e_-`.
  So `[e_-] = [eps_-] + [h]` and `s_3([h]) = 1/2 - 1 = -1/2`.

**Lemma 2.1 (relative states extend).**
- *Bounds.* Both bound sets are nonempty (`m = -nu`, `m' = nu`), so `α >= -n` and `β <= n`. `k'(kx - m) + k(m' - k'x) = km' - k'm`
  lies in `M ∩ P`, so `α <= β`.
- *Well defined.* If `jx = m_0 ∈ M` with `j > 0`, then `g(m_0)/j` belongs to both bound sets. So `α = β = g(m_0)/j = γ`.
- *Positivity.* `j > 0` gives `g(-m)/j <= α <= γ`, `j < 0` gives `γ <= β <= g(m)/|j|`, and `j = 0` is immediate.
- *Maximality.* Zorn's lemma finishes.

**Theorem 2.2.**
- *Order unit.* Every finitely generated projective is a summand of some `S_-^n`, so `u` is an order unit.
- *Part 2.* A state is `>= 0` on `K_0^+`. Conversely, apply Lemma 2.1.
- *Part 3.* `anti-central-k0-states-equal-lifted-trace-on-signed-thompson` (PASS, Section 12 and 23.1) forces
  `s = trl` on `H_fin(H)`.
- *Part 4.* The input `twisted-leavitt-corner-fullness-equals-absence-of-k0-states` (Theorem E) was not re-checked
  here. With it, `x = [P] - [Q] = [X]` with `trl(x) < 0` is the displayed stable isomorphism. For the witness,
  `trl(e_- S_-) = 1/2 < 1 = trl(eps_- S_-)`.

**Reading.** The swap corner is full iff some stable isomorphism among finite-subgroup projectives of `E x| V`, with a
finitely generated projective complement `X`, not necessarily free, drops the lifted trace. (Corrected
2026-09-12: an earlier version of this sentence said "free complement". The theorem allows any finitely generated
projective `X`.) The claim node's sentence "Parts 4 and 5 use … which is not yet verified" was out of date, and
w4-trace-state updated it at 59f40d9b4e.

## 25. Deligne rank rigidity (w4-deligne-projective; b5d74fa414, 70a38c933e): PASS

### 25.1 Lemma 0.1 (window lemma): PASS

- **Presentation.** `E_3` is finitely presented, as an extension of the finitely presented `Sp_4(Z)` by a finite
  group. So its finite-index subgroup `E_Λ` is finitely presented.
- **Generators.** `s(n)`, for `n ∈ Y_Λ`, together with `z` generate `E_Λ`.
- **Positive words.** `s(n)s(n^-1) = z^(a(n,n^-1)) s(1) = z^(a(n,n^-1))`, so `s(n)^-1 = z^(-a(n,n^-1)) s(n^-1)`, and
  `z^-1 = z^2`. So every relator is a positive word.
- **Invariant.** `σ(y_1 … y_i) = w^(j k_i) ρ(g_i)`.
  - For a letter `s(n)`: `s(g_i) z^(k_i) s(n) = s(g_i n) z^(k_i + a(g_i,n))`, then (EX) at `(g_i, n)`.
  - `ρ(1) = 1` from `(1,1)`, since `a(1,1) = 0` and `ρ(1)` is invertible.
- **Relators.** At the end of a relator, `s(g_L) z^(k_L) = 1` with `s(1) = 1` forces `g_L = 1` and `k_L ≡ 0 mod 3`.
  So `σ` is a homomorphism with `σ(z) = w^j ≠ 1`.
- **Contradiction.** Malcev gives a finite quotient of `σ(E_Λ)` separating `σ(z)`, hence a finite-index
  `L ≤ E_Λ` missing `z`. Its normal core in `E_3` has finite index and misses `z`, which contradicts
  `Res_fin(E_3) = ⟨z⟩`.
- **Uniformity.** `B_Λ` and `R_Λ` depend only on the presentation, not on `K`, `j` or `W`.

### 25.2 Proposition 1.1 (no bounded block mass): PASS

- Every pair of `R_0` has `g, h, gh ∈ B_0`, so each defect operator preserves every `V_i`, and its rank adds over
  the blocks.
- The restrictions are invertible. Lemma 0.1 gives every block some pair with integer defect at least 1.
- So the number of blocks is at most `Σ_(R_0) D_ρ <= |R_0| ε d`, and blocks of dimension at most `m` carry at most
  `m |R_0| ε d`.
- This bounds the number of all invariant summands, not only the small ones.

### 25.3 Proposition 2.1 (no fixed-level scalar sectors): PASS

- **Lemma 2.0.** `μ ≠ 0` gives `XV = V`, so `rank X >= dim V`.
- **Proof.** On `V` the defect operator at `(n, n')` is a scalar. If that scalar is nonzero, its rank is at least
  `dim V > εd`. So `λ` is exact on `R_Λ`.
  - `λ(n) ≠ 0`, since `ρ(n)` is invertible.
  - `V ≠ 0`.
  - Lemma 0.1 with `W` one-dimensional is contradicted.

### 25.4 Proposition 2.2 (invariance under class shifts): PASS

- **Tensoring.** The defect operator of `ρ ⊗ π` is the old defect operator tensored with the invertible
  `β(g,h)π(gh)`. Its rank is `e` times the old rank, so the normalized defect is unchanged.
- **Contragredient.** `π^v(g)π^v(h) = ((π(g)π(h))^T)^-1 = β(g,h)^-1 π^v(gh)`.
- **Rescaling.** Multiplying each `ρ(g)` by `λ(g)` multiplies the defect operator at `(g,h)` by `λ(g)λ(h)`.
- **Fields.** On a finite `B` the entries of `π` lie in a finite field, so the models stay over finite fields.

### 25.5 Section 3, the conditional rank Schur transfer: implications PASS, conditional claims OPEN

**Lemma 3.2 (extension).**
- `ι` is unital and preserves rank, so it maps `I` into `I'`, `G(R)` into `G(R')` and `A(R)` into `A(R')`.
- It is injective on `A(R)`: distinct scalars differ by rank distance 1.
- The product of lifts of `φ(c_i)` with `t_n` is within rank `1/n` of `λ_n 1`, so it lies in `A(R')`. Changing the
  lifts changes the product only by a central scalar.

**Lemma 3.3 (projective classes vanish on the Schur kernel).**
- `ι` is a morphism of central extensions over `ιbar`, with kernel map `ι|_A`.
- Naturality gives `ev(f_* c) = f ∘ ev(c)` and `ev(q^* c) = ev(c) ∘ q_*`. So `ι|_A ∘ β_φ = β_(φ') ∘ q_*`, and
  injectivity of `ι|_A` finishes.

**Theorem 3.4 (Schur kernel in the rank radical).**
- **Characters.** `Z` is central, finite abelian, of order prime to `p`, so `Fbar[Z]` splits into characters. The
  `E_χ` commute with `ψ(E)` and sum to 1, with `ψ(z) = Σ χ(z)E_χ`.
- **Idempotent rounding.** For `x ∈ M_d(Fbar)`, let `e` be the spectral idempotent of the generalized
  1-eigenspace. Then `rank(x - e) <= rank(x^2 - x)`:
  - on the generalized 0-space, `x` is nilpotent and `x - 1` is invertible;
  - on the generalized 1-space, `x` is invertible;
  - elsewhere, both factors are invertible.
  So corners are rank ultraproducts with renormalized rank, and `rk(E_χ) > 0`.
- **Corner.** `ψ_χ` is multiplicative, and `ψ_χ(z) = χ(z)1`.
- **Classes.** A morphism of central extensions with kernel map `χ` gives `φ^*[G(R_χ)] = χ_* α`, hence
  `β_φ = χ ∘ α_H`. Lemma 3.3 then forces `χ(z_0) = 1`.

**Corollary 3.5 (Deligne).**
- `C_3` has order prime to `p`, and `α_H(x) ≠ 0` generates it.
- An `F_p`-linear sofic approximation, after extending scalars, gives a homomorphism into `G(R)` with
  `rk(ψ(z) - 1) >= δ`.

**Routes.** `char-p-schur-radical-from-rank-root-solvability`, `deligne-rank-collapse-via-sp4-schur-kernel` and
`non-linear-sofic-via-deligne-rank-central-collapse` PASS as implications.

**Equivalent forms in `deligne-central-mark-dies-in-char-p-rank-models`: correct.**
- `Rad_rk,p(E_3) ⊆ ⟨z⟩`, because `Sp_4(Z)` is residually finite, hence `F_p`-linear sofic, and separates every
  element outside `⟨z⟩` through the quotient.
- If some homomorphism separates `z`, it also separates `z^2`: an element of order 3 has
  `rank(ψ(z)^2 - 1) = rank(ψ(z) - 1)`. A weighted block sum with an embedding of `Sp_4(Z)` then separates every
  nontrivial element.

**Power words (Section 3.3, Attempts on an OPEN claim).** `N_(ps)^p` has kernel dimensions `min(pk, ps)`, so it
has `p` Jordan blocks of size `s`. Consistent.

## 26. Radu's BMW lattice (w4-radu-f2; 9455d4a271, 85b6407404, eb6760902f): PASS

### 26.1 Relations and first-level actions: PASS

**Relations.** Each relator gives its relations:
- `axax` gives `ax = xa`; `ayay` gives `ay = ya`; `bxbx` gives `bx = xb`;
- `azbz` gives `az = zb` and `za = bz`;
- `bycy` gives `by = yc` and `yb = cy`;
- `cxcz` gives `cx = zc` and `xc = cz`.

All fourteen listed relations check.

**First-level actions.**
- `A` on `{xA, yA, zA}`:
  - `a` and `b` fix all three;
  - `cxA = zcA = zA`, `czA = xcA = xA` and `cyA = ybA = yA`;
  - so `c -> (x z)`.
- `V` on `{aV, bV, cV}`:
  - `x -> id`;
  - `ybV = cyV = cV` and `ycV = byV = bV`, so `y -> (b c)`;
  - `zaV = bzV = bV`, `zbV = azV = aV` and `zcV = cxV = cV`, so `z -> (a b)`;
  - the image is `S_3`.

### 26.2 Theorem A and Corollary A′ (two amalgam splittings): PASS

**Normalizers.**
- `yay = a`, `yby = c` and `ycy = b`, so `P_y = A x| <y>`.
- `x(cac)x = cz a zc = c(zaz)c = cbc`, using `zaz = b` from `za = bz`. So `x` normalizes `A_ev`.

**Stabilizers.**
- `A_y = A`, since every letter fixes `yA`.
- `A_x = A_ev`, the kernel of the `c`-parity.

**Kurosh counts.**
- `A_ev`: `a` and `b` each fix two cosets, and `c` fixes none. So `A_ev ≅ C_2^(*4)`, with `χ = -1`.
- `V_a`: `x` fixes three cosets, and `y`, `z` fix one each. That gives 5 involution classes. The index-three
  subgroup has `χ = -3/2 = χ(C_2^(*5))`, so there is no free factor.

**Bass–Serre.**
- Vertically: two edge orbits `{y}` and `{x, z}`. Half-edge groups `A` and `A_ev`, and a segment quotient. So
  `Γ_R = P_y *_A A *_(A_ev) E_x = P_y *_(A_ev) E_x`.
- Horizontally: one edge orbit, and `Γ_R = V *_(V_a) E_a`.

**Euler characteristic.** `1/4` three ways:
- `-1/4 - 1/2 + 1`;
- `-1/2 - 3/4 + 3/2`;
- `1 - 6/2 + 9/4`.

**Corollary A′.** `k[-]` carries pushouts of groups to pushouts of algebras.

### 26.3 Theorem B (the edge-group filter): PASS, with one literature input not re-read

**Case analysis.**
- *All elements elliptic.* A finitely generated group then fixes a vertex (Serre).
- *A hyperbolic element and a fixed end `ω`.*
  - An elliptic element fixing `ω` and a vertex `v` maps the ray `[v, ω)` to itself, so it fixes that ray pointwise.
  - Finitely many rays to `ω` share a subray. So the Busemann kernel is locally elliptic, hence locally virtually
    free, and the quotient is contained in `Z`.
- *Otherwise.* The minimal subtree has a finite quotient graph.
  - Vertex groups are subgroups of virtually free groups.
  - A nonamenable subgroup of a virtually free group contains `F_2`.

**Literature input.** The combination theorem for sofic vertex groups and amenable edge groups (Elek–Szabó,
Ciobanu–Holt–Rees) was not re-read here, as the lane flags.

### 26.4 Lemma C1 and Proposition C2 (no finite-subgroup defect): PASS

**Order bound.** A finite `H` fixes a point, preserves its open cell, and permutes that cell's vertices freely. So
`|H| <= 4`.

**Involutions.**
- An involution fixing an edge midpoint is a letter conjugate.
- On a square, an involution carrying a corner to an adjacent corner is a letter.
- One carrying it to the opposite corner is `hv`. It has order 2 iff `hv = vh`, which gives the rows `(a,x)`,
  `(a,y)` and `(b,x)`, from `axax`, `ayay` and `bxbx`.

**Order four.**
- *No `C_4`.* A generator carrying a corner to an adjacent corner is a letter, of order 2.
- *Klein.* Closure forces `v' = v` and `h' = h`, a commuting square.

**Abelianization.**
- `azbz` gives `a = b`, `bycy` gives `b = c`, and `cxcz` gives `x = z`. Basis `a, x, y`.
- The letters map to `a, a, a, x, y, x`.
- `ax`, `ay` and `bx` map to `a+x`, `a+y`, `a+x`, all nonzero, and the three pairs are independent.
- So every finite subgroup injects.

**Proposition C2.**
- *`p = 2`.* `F_2[H]` is local, so idempotent matrices are similar to `diag(I_r, 0)`, and the augmentation decides
  both parts.
- *Odd `p`.* `F_p[H]` is a product of copies of `F_p` over `±1` characters. They extend to `Γ_R` by injectivity into
  `(Z/2)^3`, and both parts follow.

## 27. Implication routes owed a verdict line, and one amendment: PASS

**`multi-piece-triangular-lift-gives-left-invertible-s0-lift`** (w4-kap-triangular).
- `X_ij X_kl = 0` unless `j = k`. So `N^m` is a sum over directed paths of length `m`, and it vanishes for an acyclic
  digraph on `m` vertices.
- `(ba)^-1 b` is a left inverse.
- `π(a) = Σ g_i P_(β_i)` acts as `s_0` cylinder by cylinder.

**`f9-hadamard-fullness-from-swap-corner-fullness`** (w4-hadamard-f3). `(c W^-1)(W e_- W^-1)(W b) = c e_- b`
(Section 9).

**`oriented-clifford-skew-rings-sf-from-matrix-lamp-wreath`** (w4-clifford-df). Section 14.

**`kun-thom-clifford-skew-rings-sf-from-f3-linear-soficity`** (w4-clifford-df).
- The target is over `F_3` for every graph, and so is the input.
- `M_n(F_3[E_S]) = M_n(F_3[W]) x M_n(A_S)`, so a one-sided pair in `A_S`, padded, is one in `F_3[E_S]`.

**`deligne-cover-nonsurjunctive-from-twisted-algebra-failure`** (w4-deligne-twisted).
- *Padding.* Through the central idempotents of `<z>`, which exist when `w ∈ F` and `p != 3`.
- *Finite field.* The automaton lemma needs `F` finite. A witness over any field of characteristic `p` descends to
  one:
  - the entries generate a finitely generated `F_p`-domain `D`;
  - a nonzero entry of `AB - I` is not nilpotent, so it survives modulo some maximal ideal `m`, since `D` is a
    Jacobson ring;
  - `D/m` is finite.

**`deligne-cover-stable-finiteness-from-rank-projective-models`.** The characteristics match the target: every `p != 3`
through the rank-projective claim, and `p = 3` directly. An `F_p`-model is an `F`-model.

**`non-linear-sofic-via-deligne-twisted-algebra-failure`.** This is the contrapositive of
`linear-sofic-group-algebra-is-stably-finite`, and the target only asks for some field.

**Amendment fe98f9469e** to `clifford-skew-ring-rank-models-give-linear-sofic-wreath`.
- A central `c_v u_g` forces `gx = x` for all `x`, then `b(x, v) = 0` for all `x`, hence `v = 0` by nondegeneracy, and
  `g` central.
- Faithfulness gives `g = 1`.
- For residually finite `G`, block-sum at stage `n` with the regular representation of a finite quotient separating
  the first `n` such elements. Each fixed `g` is separated at distance at least `1/4` on a cofinite set of stages. PASS.

## 28. Triangular identity certificates (w4-upg-kill, c1b9da39b8): PASS

This lane is not on this verifier's roster. It asked for verification directly.

### 28.1 `sylvester-rank-functions-iff-no-triangular-certificate` (Theorems 2.1–2.2): PASS

**(a) Rank functions are monotone matrix states.**
- *Rank function to state.* `XMY` is a product, so a Sylvester rank function is `<~`-monotone. It is monotone for
  triangular moves by the triangular axiom, and additivity and transitivity extend monotonicity to all of `<=_T`.
- *State to rank function.*
  - `MN <~ M` and `MN <~ N` give the product axiom.
  - Zero matrices of all sizes, the empty one included, are mutual minors. So `d(0) = 2d(0) = 0`, and `0 <~ M` gives
    `d >= 0`.

**Monoid and cone.**
- `~` is compatible with `(+)`, permutation matrices make `(+)` commutative, and the zero matrix is equivalent to the
  empty matrix.
- Monotone matrix states are exactly the additive maps on the Grothendieck group that are `>= 0` on `P` and 1 at `u`.

**Order unit.** For `X` of size `p x c`, `X <~ I_c <~ I_c (+) Y`, so `c u - ([X] - [Y]) ∈ P`.

**States exist iff `-u ∉ P`.**
- *Necessity* is immediate.
- *Sufficiency.* If `-u ∉ P`, then `-ku ∉ P` for every `k >= 1`, since `u ∈ P` and `P + P ⊆ P`. So `f(nu) = n` is
  well defined and `>= 0` on `Zu ∩ P`. The one-step extension lemma extends it to a state (Section 24, Lemma 2.1).

**Absorption.** `[N] + [I_1] = [M]` in the Grothendieck group means `N (+) I_1 (+) K ~ M (+) K` for some `K`. With
`X = N (+) K`, this gives `I_1 (+) X ~ M (+) K <=_T X`.

**Identities.**
- By induction, `I_k (+) X <=_T X`.
- `X <~ I_q`, where `q` is the number of columns of `X`, and `I_(q+1) <~ I_(q+1) (+) X`.
- So `I_(q+1) <=_T I_q`.

**(c) Chains.** The chain relation contains both generators and is transitive. It is compatible with `(+)`: a minor
step `(+) K` is a minor step, and a triangular step absorbs `K` into `Z`.

**Theorem 2.2.**
- `I_(q+1) = XY`, with `X` of size `(q+1) x q`, is a split epimorphism `A^q -> A^(q+1)`. That is equivalent to
  `-[A] ∈ K_0^+`.
- So matrix states, `K_0` states and the rank condition coincide.

**Remark "The summand".** Sylvester rank functions pull back along the unital projection `F_3[G] -> S_-`. In the other
direction, they restrict to the corner `S_-`, divided by `rk(eps_-) > 0`.

### 28.2 `split-identity-minors-survive-triangular-moves`: PASS

**`⊑`.**
- Minor steps preserve it: `Y <~ Y'` gives `Y (+) I_s <~ Y' (+) I_s`.
- It adds over `(+)`, up to permutation.

**Proposition 3.1 (split minors survive).**
- After permutation, `T (+) I_(s+t) = [[A (+) I_s, C'], [0, B (+) I_t]]`, where `C'` is `C` bordered by zeros.
- `diag(X_1, X_2)` on the left and `diag(W_1, W_2)` on the right give `[[I, D], [0, I]]`.
- Right multiplication by `[[I, -D], [0, I]]` gives the identity.

**Corollary 3.2 (split chains flatten).** Induction runs from `I_(q+1) ⊑ Y_0`, with `s = 0`, to `I_(q+1) ⊑ I_q`.

**Remark 3.3 (idempotent steps).**
- `T^2 = T` gives `A^2 = A`, `B^2 = B` and `C = AC + CB`.
- Multiplying by `A` on the left and `B` on the right gives `ACB = 2ACB`, so `ACB = 0`.
- With `x = AC - CB`: `Ax = AC` and `xB = -CB`, so the corner `C - Ax + xB` is 0.

**Remark 3.4.** Over `K`, `I_(1+s) <~ e_11 (+) I_s` would give `2 + 2s <= 1 + 2s` in `K`-rank.

**Consequence.**
- Replace idempotent triangular steps by minor steps (Remark 3.3).
- If every remaining triangular step split, Corollary 3.2 would flatten the chain.
- So a certificate over a ring with the rank condition and no Sylvester rank function has a non-idempotent step with
  no split. PASS.

## 29. The state upgrade at weakly finite images (w4-upg-state; 93ed389c3f, fcad1e6913): PASS

This lane asked for verification directly.

### 29.1 `sylvester-rank-function-quotients-are-weakly-finite` (Lemma A.1, Theorem A): PASS

- **Factorizations.** Multiplying out, both `[[I_n,0],[B,I_m]]·[[I_n,A],[0,I_m-BA]]` and
  `[[I_n,A],[0,I_m]]·[[I_n-AB,0],[B,I_m]]` equal `[[I_n,A],[B,I_m]]`.
- **The identity.** Invertible factors leave `N` unchanged, so `n + N(I_m - BA) = N(I_n - AB) + m`.
- **Rank-zero entries.** `x + y = [1 1]·diag(x,y)·[1 1]^T` gives subadditivity. Reading entries as
  `e_i^T X e_j`, and writing `X = Σ E_ij x_ij`, shows a matrix has rank 0 iff its entries do.
- **Weak finiteness.** Apply Lemma A.1 with `m = n`.

### 29.2 Corollary A.2 (the anti-central summand): PASS

- `X -> X eps_-` is unital, and `rk(1 - [z]) = N(2 eps_-) = 1`.
- A normal subgroup missing `z` meets `<z>` trivially. Its image in the simple group `PG` is `1` or `PG`. `PG` would
  give `G_3 = N_rk × <z>`, which has a quotient of order two, against perfection.
- Perfection of `G_3` and simplicity of `PG` are established nodes, not re-derived here.
- **Injectivity.** `(1 - [k]) eps_-` has positive rank for every `k ≠ 1`.

### 29.3 Proposition B (states pin regular elements): PASS

- **Retracts.** If an idempotent `f` factors as `a e b`, the maps `f a e` and `e b f` compose to `f`, so `fA^(k')` is a
  retract of `eA^k` and `s(f) <= s(e)`.
- **Regular elements.** For `X = XYX`: `e = XY` is idempotent, `X = eX`, and `e = I·X·Y`.
- **`F_3[C_3]`.**
  - It is local, so its only idempotents are 0 and 1, and `K_0 = Z`.
  - The normalized ranks on `F_3[x]/(x-1)^j` give `0`, `1/2` and `2/3`, and convex combinations fill the interval.
  - With `u^3 = 0`, the Sylvester inequality `N(u^2) + 1 >= 2N(u)` and the Frobenius inequality
    `N(u^3) + N(u) >= 2N(u^2)` give `N(u) <= 2/3`.
  - `ρ^s(u) = 0`, by the augmentation on idempotent matrices over the local ring. `ρ_s(u) = 1`.

### 29.4 Lemma C.1 and Theorem C (rank condition gives a weakly finite image): PASS

**Lemma C.1.**
- *Sizes.* `X` is `n × (n+1)`, `Y` is `(n+1) × n`, and `K = UẼV` with `Ẽ` a direct sum of null idempotents, `U` of size
  `(n+1) × R` and `V` of size `R × (n+1)`.
- *Retract.* `X' = [[X],[ẼV]]` and `Y' = [Y, -UẼ]` give `Y'X' = YX - UẼ^2V = I_(n+1)`.
- *State-null form.* `n + 1 <= n + s(Ẽ) = n`.
- *Class-zero form (the route).* `[ẼA^R] = 0` gives `ẼA^R ⊕ A^r ≅ A^r`, hence `A^(n+r) ≅ A^(n+1+r) ⊕ P`: an
  epimorphism `A^(n+r) -> A^(n+1+r)`.

**Theorem C.**
- *Easy direction.* Pad a failure `YX = I_(n+1)` with a zero row and column. Weak finiteness would then force
  `XY ⊕ 0 = I_(n+1)`, which is impossible in a nonzero ring.
- *Zorn.* A failure uses finitely many entries. Every ideal in the family is proper, since the zero ring fails the rank
  condition.
- *Maximal quotient.* States are faithful, by Lemma C.1 plus maximality. For weak finiteness, `AB = I_n` makes
  `I_n - BA` an idempotent of class zero.
- *Literature.* Possibly Malcolmson (1980). Not checked here either.

### 29.5 Corollary C.2 and routes: PASS

- **Equivalences.** 1–3 are the census equivalences, not re-derived here. 3 ⟺ 4 is Theorem C.
- **Embedding.** `1 - z` maps to `2·1_W ≠ 0` in the nonzero `F_3`-algebra `W`. Then the normal subgroup argument
  applies.
- **`nonpositive-unit-class-from-no-weakly-finite-image`.** No weakly finite image means the rank condition fails, so
  there is no state, so `k[eps_-] <= 0`. PASS as an implication.
- **`weakly-finite-image-from-state-upgrade`.** `1 - [z] = 2 eps_-` gives `rk(eps_-) = rk(1 - [z]) > 0`, then corner
  normalization. PASS as an implication.
- **`sylvester-rank-functions-from-weakly-finite-images`.** Pullback along the unital quotient map. PASS as an
  implication.
- **Section 4 prose.** Consistent:
  - a cube-zero `4 × 4` matrix over a division ring has at least two Jordan blocks, hence rank at most 2;
  - the Sylvester bound generalizes to `N(u) <= 2n/3`;
  - the one-by-one case collapses, since `uv = 1` gives `u^3 v^3 = 1`.

## 30. RGR_p cyclic reduction (w5-rgr-p, a026618e23): two claims PASS; one passes in the sufficiency direction, with a false sentence corrected forward

### 30.1 `rgr-p-reduces-to-cyclic-twist-system`: sufficiency PASS; the "no loss" sentence is FALSE as written and is corrected

**Sufficiency.**
- *Block-diagonality.* The coefficients are block-scalar, and each `t^(±1)` moves the block index by `±1`. The net shift
  is `e ≡ 0 mod |e|`.
- *Negative total exponent.* Amplify by `|e|`. The node says `k = e`.
- *Block values and rank additivity.* Re-derived. So a solution of the cyclic system is an RGR_p witness.

**The false sentence.**
- *What main says.* The claim: "any RGR_p witness at amplification `e` has this block form". Route step 4: "solving
  the system is equivalent to RGR_p at that amplification".
- *Why it is false.* A general `t ∈ GL_(de)` is not a twisted cyclic shift. For `c_0 t c_1 t c_2`, a block-diagonal
  `t = diag(u, u)` with `u c_1 u = K` is a witness at amplification 2 that is not of shift form.

**Correct form: no loss up to one more amplification.**
- If `t ∈ GL_(dk)` is a witness at amplification `k`, let `S_e` be the cyclic permutation of `|e|` blocks. Then
  `t~ = t ⊗ S_e` is a twisted cyclic shift with every twist equal to `t`.
- `t~` commutes with nothing it needs to: the coefficients act on the first tensor factor, so
  `w(t~) = w(t) ⊗ S_e^e = w(t) ⊗ 1`, with the same normalized error.
- So RGR_p holds for `w` iff, for every `ε`, some amplification of the coefficients admits an `ε`-solution of the
  cyclic system.
- The claim that the cyclic system "is as hard as RGR_p itself" stands.

### 30.2 `scalar-target-power-words-have-exact-roots`: PASS

- `C e_i = e_(i+1)` and `C e_e = λ e_1` give `C^e e_i = λ e_i`.
- `det C = (-1)^(e-1) λ`: a cyclic permutation times `λ`.
- **Precision.** For `e < 0`, use the companion matrix of `x^|e| - λ^(-1)` and invert.

### 30.3 `two-syllable-nonsingular-words-are-exactly-solvable`: PASS

**`c_0 t c_1 t c_2`.**
- With `t(w_0, w_1) = (b_1 w_1, b_0 w_0)`, tracking blocks gives `P_0 = c_0 b_1 c_1 b_0 c_2` and
  `P_1 = c_0 b_0 c_1 b_1 c_2`.
- `b_0 = c_1^(-1)` and `b_1 = K = c_0^(-1) λ c_2^(-1)` give `b_1 c_1 b_0 = b_0 c_1 b_1 = K`, so `P_0 = P_1 = λ 1`.

**Equal exponents.** `u c_1 u = K` iff `(c_1 u)^2 = c_1 K`.

**General power words, re-derived here.** `t^m = M` is exactly solvable after amplification by `p^r`, where
`m = p^r m'` with `p ∤ m'`:
- take the Jordan blocks `μ(1 + N_s)` of `M`;
- take an `m`-th root of `μ`;
- take the binomial `m'`-th root of `1 + N_(p^r s)`;
- `(1 + N_(p^r s))^(p^r) = 1 + N_(p^r s)^(p^r)` has `p^r` Jordan blocks of size `s`.

This upgrades the power-word Attempts line of `rank-ultraproduct-unit-groups-solve-nonsingular-equations` from
"consistent" (Section 25.5) to re-derived. The equations are stable under amplification of the coefficients, so the
two amplifications compose.

## 31. Overfilled stars (w5-laminar-cycle): PASS

### 31.1 `laminar-defects-localize-to-a-nonsofic-overfilled-star` (Theorem 1.1, Corollaries 1.2–1.3): PASS

**Theorem 1.1.**
- *Atom traces.* `y = α_y + Σ_(C(y)) z` is an orthogonal sum, and the lifted trace is additive. So
  `t_p(α_y) = r(y) - Σ r(z)`, with `r(1) = n`.
- *A nonpositive term.* A nonpositive sum over distinct nonzero atoms has a nonpositive term.
- *The star is laminar.* Children of one parent are pairwise orthogonal: if one child lay below another, it would have
  a closer parent. So within `F_y` the children of `y` are exactly `C(y)`, and `α_y` is an atom of `F_y`.
- *No sofic realization.*
  - A compatible realization of `Star(y)` is injective on the union of the images, because `K_s ∩ K_t` is the image
    of `H_s ∩ H_t`.
  - So the image of `α_y` has the same coefficients as `α_y`, and it is nonzero.
  - Theorem 2.6 then makes its trace positive, a contradiction.

**Corollary 1.2 (shape).**
- TFR1 for each strict pair `z_i < Y` gives `m >= 2`.
- If `Φ_y` were a forest, the amalgam would be virtually free and contain `Star(y)`, hence sofic.
- A cycle needs three distinct vertices, and at most one of them is the parent's subgroup.

**Corollary 1.3 (hosts).** A common finite overgroup, or a sofic overgroup, is a realization with the actual
intersections.

**Wording remark.** "Occurs in no sofic group" means no compatible realization with matching intersections, as the
artifact defines. Finite groups themselves always embed in sofic groups.

## 32. The binary cyclic corner and its complement corner (w5-binary-upg; 3277b6da2b, 7a22750be7): PASS

### 32.1 Setup and Lemma 1.1: PASS

- **`D`.** `D(h)D(h') = Σ_i s_i h h' t_i`, `D(1) = 1` and `t_1 D(h) s_1 = h`. Every ternary permutation unit
  `Σ s_σ(i) t_i` commutes with `D(h)`.
- **Translations.** `g = τ_(1,0)` and `D(g) = τ_(0,1)` on the nine cylinders, and `π_M τ_b π_M^-1 = τ_(Mb)` by
  re-indexing.
- **`F_2[A_9]`.** It is semisimple. `f_K = e_K - e_(A_9)` is the primitive idempotent of the two characters with
  kernel `K`, `1 = e_(A_9) + Σ_K f_K`, and `f = f_(K_2) + f_(K_3) + f_(K_4)`.
- **Lemma 1.1.** `ψ` and `ψ'` are unital homomorphisms, because `D(x)` commutes with `e`.

### 32.2 Lemmas 1.2 and 1.3: PASS

- **(a)** `e·D(E_k)` is the averaging idempotent of `<g>·D(C_3^k) = C_3^(k+1)`, a product of commuting subgroups that
  meet trivially.
- **(b)** Conjugation by `π_M` permutes the `f_K <= f`, and `f_(K_1) = E_1 - E_2`.
- **(c)** Telescoping `e = E_(k+1) + Σ_(l=1..k) (E_l - E_(l+1))`, with `Σ 3^(k-l) = (3^k - 1)/2`.
- **(d)** `D(e) = e_(K_2)`, `f_(K_i) e_(K_2) = δ_(i2) f_(K_2)` and `f_(K_2)[D(g)] = f_(K_2)`.
- **Lemma 1.3.** `c = φ(e) = ce`, and `1 = c e m`.

### 32.3 Theorem B (the binary Theorem E): PASS

- **2 ⇒ 3 ⇒ 4.** Cancellation in `K_0`, then positivity.
- **4 ⇒ 5.**
  - `x = f_(MK) π_M f_K` and `y = f_K π_M^-1 f_(MK)` lie in `T`, with `xy = f_(MK)` and `yx = f_K`.
  - So each `f_K` has `s_T`-value `1/3`, and the pulled-back state gives `[f]` the value `2/3`.
- **5 ⇔ 6.** The state criterion (as in Section 28.1): `-[T] ∈ K_0^+` iff `T ⊕ Q ⊕ T^N ≅ T^N`.
- **6 ⇒ 2, in `V(A)`.**
  - `N v + v + q = N v` iterates to `N v + j v + j q = N v`.
  - Applying `F^k` with `j = 3^k` gives `N d_k + v + x = N d_k`.
  - Choose `k` with `(3^k - 1)/2 >= N`. Then `p = N d_k + c`, so `p + v + x = p` and `u + x = p`.
- **Scope.** The result holds for `D`-stable subgroups containing `g` and the `π_M`: every construction stays inside.

### 32.4 Proposition C, Corollary 4.2 and the chain route: PASS

- **(a)** `(f_(K_3) + f_(K_4))(1 - [D(g)])` is a unit of the corner `(f_(K_3) + f_(K_4)) F_2[A_9] ≅ F_4 × F_4`. So its rank
  equals the rank of the corner unit, `2/3`.
- **(b)**
  - `(1 - [g]) e = 0` gives `1 - [g] = (1 - [g]) f`.
  - `rk(f) = 0` forces `g ∈ N_rk`, and simplicity then forces `rk = rk_ε`.
  - The input `binary-leavitt-unit-group-is-simple` was not re-derived.
- **Corollary 4.2.** Composing with `ψ'` contradicts Section 16.3.
- **Route `binary-counterexample-from-rank-kill-and-state-realization`.** PASS as an implication:
  - (NR) ⇒ (NR_T) by (a);
  - U1_T turns (NR_T) into (NS_T);
  - Theorem B gives fullness.
- **Proposition 4.1 (prose).** `ψ'|_T` is a non-unital endomorphism, with `ψ'(f)` of state value `2/3`, so
  `(3/2) s_T ∘ K_0(ψ'|_T)` is a state. Consistent.

## 33. Essential cycles, canonical partitions of V, label realization (w5-laminar-cycle; 24f4cc3b9a, c4a3e6ec31): PASS

### 33.1 `intersection-edges-inside-a-third-subgroup-are-redundant`: PASS

**Lemma 2.1.**
- `A' -> A` exists because the diagram of `A'` has fewer relations.
- In the other direction, `g ∈ D_ij <= H_l` lies in `D_il` and `D_lj`, so `ι_i(g) = ι_l(g) = ι_j(g)` in `A'`.
- The two maps are inverse on generators.

**Corollary 2.2.**
- Each deletion uses edges `{i,l}` and `{l,j}` of the current diagram. The same proof applies, since
  `D_il, D_lj ⊇ D_ij ≠ 1`.
- If `Φ^ess` is a forest, `A` is a free product of trees of finite groups: virtually free, hence sofic. Theorem 2.1
  of the `w4-kap-join` artifact then applies.

**Corollary 2.3.** `D_ij <= H_l` iff `D_ij = H_0 ∩ H_1 ∩ H_2`. Deleting that edge leaves at most a path.

**Example 2.4 (a degenerate cycle).**
- *`D_01 = <(c d)>`.* An element of `H_1` moving `[0]` sends `[00]` to a depth-three cylinder, so only `[0]`-fixing
  elements lie in `H_0`.
- *`D_12 = <(c d)>`.* `[0]` is the only piece of `P_1` that is a union of three pieces of `P_2`, so it is fixed
  pointwise.
- *`D_02 = Sym{b,c,d}`.* `a` is the only piece of `P_0` that is a union of two pieces of `P_2`.
- *Triple intersection.* It is `<(c d)>`.
- *Infinite order.* `g = σ ∘ (a c)` maps `10x -> 00x -> 100x`, so `g(1 0^k y) = 1 0^(k+1) y` for `k >= 1`.

### 33.2 `finite-subgroups-of-thompson-v-permute-a-canonical-partition`: PASS

- **Invariance.** `g|_(h(c)) = (gh)|_c ∘ (h|_c)^-1` is a prefix replacement onto a cylinder.
- **Partition.**
  - A common refinement of the pieces `D_h` puts every point in some cylinder of `C_H`.
  - The chains of cylinders above a given cylinder are finite, so maximal elements exist.
  - Maximal elements are disjoint, since cylinders are nested or disjoint. Compactness makes them finitely many.
- **Action.** If `h(c) ⊊ c'`, then `h^-1(c') ∈ C_H` strictly contains `c`, which contradicts maximality.
- **Coarsest.** The pieces of any `P` with `H <= Σ(P)` lie in `C_H`.
- **Intersections.** `p ∩ q` is the smaller cylinder or empty, and `g` restricts to a prefix replacement there.

### 33.3 `v-hosted-stars-without-block-symmetries-occur-in-finite-groups`: PASS

**Proposition 4.1.**
- *Injectivity.* An element of `Σ(P_s)` fixing every piece is a prefix replacement of each piece onto itself, hence
  the identity.
- *Agreement.* For `g ∈ H_s ∩ H_t`, `g` maps common pieces to common pieces, and both labelings apply the same
  geometric action there. On non-common labels, the hypothesis handles one side and "fix outside its own partition"
  the other.
- *Exact intersections.*
  - If `ψ_s(h) = ψ_t(h')`, the permutation fixes the labels of `P_s \ P_t` and `P_t \ P_s`. So `h` and `h'` are the
    identity on `X \ ∪(P_s ∩ P_t)`.
  - On a common piece, both are the unique prefix replacement onto the same image piece. So `h = h'`.
- *Conclusion.* A homomorphism from the amalgam, injective on the union with exact intersections, into the finite
  group `Sym(Y)`. Theorem 2.6 applies.

**Example 4.2 (an essential triangle that still dies).**
- *Intersections.* A split region is the only way to write that cylinder as a union of two pieces of the other
  partition, so every intersection element fixes it pointwise. This gives `D_01 = Sym{U_1,U_2,U_3,U_5}`,
  `D_12 = Sym{U_1,U_3,U_4,U_5}` and `D_02 = Sym{U_1,U_3,U_5,U_6}`.
- *Essential.* `(U_1 U_2) ∉ H_2`, because it sends `[0010]` to `[0000]`, which is not a piece. The other two edges are
  symmetric.
- *Infinite order.* `g = (U_3 U_4) ∘ t` sends `010x -> 0110x -> 0100x`.
- *Count.* `|Y| = 6 + 2 + 2 + 2 = 12`.

**Corollary 4.3.** The contrapositive of Proposition 4.1.

## 34. The swap-problem split at the central involution (lead priority check): PASS, route verdict line added

`ternary-leavitt-swap-problem-splits-at-central-involution` had no verdict line on its route. Its earlier review is
Section 23 of `research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md`: parts 1–5 PASS, and part 6 was
corrected forward. The corrected claim is on main. Re-derived independently here:

- **Part 1.** `(2(1 ± z))^2 = 8(1 ± z) = 2(1 ± z)`, the sum is `4 = 1`, and the product is `4(1 - z^2) = 0`. So
  `S_+ ≅ F_3[PG]`.
- **Part 2.**
  - `d^2 = s0t0 + s1t1 = 1`, `dw = s0t1 - s1t0` and `(dw)d = -w = zw`.
  - On `S_-`, `[d] e_- [d] = eps_- - e_-`, with matrix units `e_-`, `eps_- - e_-`, `e_-[d]` and `[d]e_-`.
  - A unital map to a commutative ring would give `e = 1 - e` and `e(1 - e) = 0`. So `e = 2`, and `4 = 2`, which is
    impossible.
- **Part 3.** Fullness through `E_11` of `M_2(T)` is a column times a row, which is a two-pair Cohn family.
- **Part 4.** Evaluation sends `[z]` to `-1` and `eps_+` to 0.
- **Part 5.** Project to `S_+`, and note `ebar ≠ 1`.
- **Part 6, corrected form.**
  - With `b, c ∈ S_-`: `CA = eps_- + eps_+ = 1`, and `AC = e_- b c + eps_+ ≠ 1`, because `e_- b c ∈ e_- S_-` and
    `e_- ≠ eps_-`.
  - `G` embeds in `PG` by `g -> s0 g t0 + s1 t1`, and surjunctivity passes to subgroups.

## 35. Weakly finite representations of the binary corner (w5-wf-binary, 3e90870399): PASS

**Lemma W.1 (corners are weakly finite).**
- `X' = X + (1-p)I` and `Y' = Y + (1-p)I` satisfy `X'Y' = I`, because `X(1-p) = (1-p)Y = 0`.
- Compress `Y'X' = I` by `p`.

**Lemma W.2.**
- *Block unit.* `f(1 - [D(g)]) = (f_(K_3) + f_(K_4)) u`, with `u` a unit of the block algebra: `D(g)` acts by `ω` on the
  `K_3` and `K_4` blocks.
- *One idempotent dies.* If `φ([g]) = 1`, then `q(f_(K_3)) = 0`.
- *The others die.*
  - An `M` fixing `K_1` with `MK_3 = K_2` exists, because `GL_2(F_3)` acts on the four lines as `S_4`.
  - `π_M` commutes with `e`, hence with `f`.
  - `x = π_M f_(K_3)` and `y = f_(K_3) π_M^-1` lie in `T`, with `xy = f_(K_2)` and `x = x f_(K_3)`.
  - So `q(f) = 0`, and `W = 0`.

**Theorem W.**
- *(a) ⇒ (c).*
  - `φ(ce)φ(eb) = 1` gives `φ(ebce) = 1`.
  - `φ(e)` has left inverse `φ(ebc)` and right inverse `φ(bce)`, so `φ(e) = 1`.
  - Then `u + u^2 = 0`, so `u^2 = u`, and `u = 1`.
- *(b) ⇔ (c).* Lemma W.2 in one direction. In the other, `φ(f) = u + u^2 ≠ 0`, with Lemma W.1.
- *(c) ⇔ (d).* Characteristic two, and simplicity of `G`. That input was not re-derived.
- *(b) ⇒ (a).* Theorem C (Section 29.4), then Theorem B (Section 32.3).

**Route `binary-cyclic-corner-from-no-weakly-finite-complement-image`.** PASS as an implication.

**Consequence confirmed, given simplicity.** The binary averaging corner is full iff `L_(F_2)(1,2)^x` has no
nontrivial homomorphism into the unit group of a weakly finite ring of characteristic two.

## 36. Weakly finite representations of the ternary Leavitt units (w5-wf-obstruct; 10be14b3be, ea87417970): PASS

### 36.1 `weakly-finite-reflection-ideal-detects-weakly-finite-images` (Theorem 1, Corollary 1.2): PASS

- **(a)** `AB ≡ I` modulo `J_ω` involves finitely many entries, all in one `J_k`. So `BA - I` has entries in `J_(k+1)`.
- **(b)** By induction: `φ(J_k) = 0` gives `φ(A)φ(B) = I`, hence `φ(B)φ(A) = I`, hence `φ(J_(k+1)) = 0`.
- **(c), (d)** `J_1` is generated by the defects of exact pairs, and `Φ(0) = 0` makes every stage zero.
- **Corollary 1.2.**
  - `J_1(S_-) ≠ 0` is an exact one-sided pair over `S_-`. Padded by `eps_+`, it gives one over `F_3[G]`.
  - `1 ∈ J_ω` together with `S_- ≠ 0` forces `J_1 ≠ 0`, by (d).
- **Literature.** Cohn and Malcolmson not read here either.

### 36.2 `weakly-finite-leavitt-representations-killing-defect-are-trivial` (Theorem 2): steps 4–5 PASS; steps 1–3 cited

- **Inputs, not re-derived.** The reversed-root identity, `[TRI]` Theorem A, and the ring-algebra forms of `[RR]`
  Propositions 6 and 8 and Corollary 9. `w3-vf-linear` passed those in its Section 23.
- **Step 4.**
  - Corners of weakly finite rings are weakly finite: pad by `1 - p_1`.
  - `C(t_0)C(s_0) = p_1` gives `C(s_0)C(t_0) = p_1`, so `C(s_1 t_1) = 0`.
  - Then `p_1 = C(t_1)C(s_1 t_1)C(s_1) = 0`.
- **Step 5.** `u_ij = u_i1 u_1j = 0`, and `x_ij(a) = [x_ik(a), x_kj(1)]` puts every root element in the kernel.

### 36.3 `ternary-weakly-finite-representations-give-anti-central-images` (Theorem 3): PASS, conditional on simplicity of `PG` as recorded

- **Normal subgroups.** If `N ⊄ <z>`, then `N<z> = G`, so `G/N` is abelian, and perfection gives `N = G`.
- **Injectivity.** `ι` is injective with `ι(G) ∩ {±1} = 1`, so `ker(ρ∘ι) = 1`.
- **The cut.**
  - `u = ρ(ι(z))` is an involution different from 1.
  - `f = 2(1 - u)` satisfies `f^2 = 8(1 - u) = f`, and `f` commutes with `ρ(ι(G))`.
  - `[z] -> fu = 2(u - 1) = -f`. So `eps_+ -> 0`, and the image factors through `S_-`.
- **(i) ⟺ (iv).** Through Theorem 2.

## 37. Separated triangular certificates flatten (w5-upg-flatten; d88ccb506a, 04b3f10838): PASS

### 37.1 `separated-triangular-steps-flatten-to-minors` (Lemma S): PASS

- `W𝓡` has rows `[A R_A, C R_B]`, `[0, B R_B]`, `[Z_1 R_1, 0]` and `[0, Z_2 R_2]`.
- So `𝓛W𝓡 = [[f, L_A C R_B], [0, g]]`, and the lower-left block is zero.
- Compress by `diag(f, g)`. Then `[[f, fDg], [0, g]]·[[f, -fDg], [0, g]] = f (+) g`.

### 37.2 `nilpotent-jordan-certificates-flatten-to-minors` (Corollary J): PASS

- **Frobenius matrix.** `[[I, 0], [-U, I]]·[[V, I], [0, U]]·[[I, 0], [-V, I]] = [[0, I], [-UV, 0]]`. So
  `T ~ I_n (+) UV`, up to permutation and sign.
- **Orientation.** Lemma S with `A = u^j`, `Z_1 = I_((j-1)n)`, `B = u` and `C = I_n`. `f^((+)j)` is idempotent.
- **End.** `u^k = 0`. The `K_0` bound comes from the retract in item 1 of Proposition O.
- **Kill test.** `I_9 <~ f^((+)3) <~ I_8`.
- **Sharpness.** On `F_3[C_3]`.

### 37.3 `outer-state-rank-is-rank-function-iff-subadditive` (Proposition O): PASS

- For `f = L e R`: `α = eRf` and `β = fLe` give `βα = f`, and `e' = αβ` is an idempotent with `e' <= e`. So
  `[f] <= [e]`.
- `ρ^s(I_1) = 1`, `ρ^s(X) <= q`, and `f <~ 0` forces `f = 0`.
- Superadditivity holds. The triangular bound comes from Lemma S with empty padding, and minimality from
  Proposition B(2).

### 37.4 `k0-state-extends-to-rank-function-iff-triangular-monotone` (Theorem R): PASS

- **Well defined.** `[e (+) f'] = [e' (+) f]` means mutual domination after adding `K`. Apply the hypothesis both ways.
- **Positive on `H ∩ P`.** `e (+) M (+) K ~ f (+) N (+) K` gives `f (+) K' <=_T e (+) K'`, with `K' = M (+) K`.
- **Extension.** By the one-step lemma (Section 24). Theorem 2.1(a) makes the extension a Sylvester rank function.

## 38. Implication routes of the weakly finite chain (w5-wf-obstruct, w4-upg-kill): PASS

All four routes are implications. None of them makes a claim decision-level, and the required claims keep
their own status.

### 38.1 `no-weakly-finite-representation-from-defect-killing`: PASS

- **Matching.** At `K = F_3`, `weakly-finite-leavitt-representations-killing-defect-are-trivial` has the
  same host class (weakly finite `F_3`-algebras), the same three-leaf frame, and the same defect
  `D_rho = N_23 N_12` with `N_ab = rho(x_ab(1)) - 1`. That is the product that
  `ternary-weakly-finite-representations-kill-two-root-defect` sets to zero.
- **Glue.** For any `rho`, the first claim gives `D_rho = 0` and the second makes `rho` trivial. Both claims
  and the target quantify over the same `rho`.

### 38.2 `no-weakly-finite-representation-from-summand-obstruction`: PASS, inheriting the simplicity condition through Theorem 3

- **Cut.** Take `rho` nontrivial. Then `u = rho(iota(z)) != 1` (Section 36.3). So `f = 2(1 - u)` is a nonzero
  idempotent (`f^2 = 4f = f`, and `2` is invertible) that commutes with `rho(iota(G))`.
- **Image.** `x -> f rho(iota(x))` is a unital map `F_3[G] -> fWf` with `[z] -> -f`, so it factors through
  `S_-`. Its image is a nonzero unital subring of the weakly finite corner `fWf`, hence a nonzero weakly
  finite quotient of `S_-`.
- **Glue.** `ternary-anti-central-summand-has-no-weakly-finite-image` forbids that quotient.

### 38.3 `summand-no-weakly-finite-image-from-no-representation`: PASS

- **Units.** `eps_- = 2(1 - z)` is a central idempotent (`eps_-^2 = 4 eps_- = eps_-`) with
  `eps_- z = 2(z - 1) = -eps_-`. So `g -> eps_- g` is a homomorphism `G -> S_-^x`, and it passes to any
  quotient `W`.
- **Nontrivial.** In a nonzero `W`, `z -> -1 != 1` because `2` is invertible. `W` is then a weakly finite
  `F_3`-algebra carrying a nontrivial representation, which the required claim forbids.
- **No simplicity used.** This is direction 3 ⟹ 1 of Theorem 3. Routes 38.2 and 38.3 are the intended cycle.
  The cycle records an equivalence, not a proof of either claim.

### 38.4 `anti-central-flattening-from-general-state-upgrade`: PASS

- **Contrapositive.**
  - Suppose no `q'` has `I_(q'+1) <~ I_(q')` over `S_-`.
  - By part 2 of `sylvester-rank-functions-iff-no-triangular-certificate`, `S_-` has the rank condition.
  - The general claim gives a Sylvester rank function on `S_-`.
  - Part 1 then rules out every `I_(q+1) <=_T I_q`.
- **Conventions.** `I_(q+1) <~ I_q` means `XY = I_(q+1)`, with `X` of size `(q+1) x q`. That is a split
  epimorphism `S_-^q -> S_-^(q+1)`, which matches the claim's "no epimorphism `A^q -> A^(q+1)`". The unit of
  `S_-` is `eps_-`.

## 39. Sylvester exact globality and kernel compressions (w7-sylv-global): PASS

This section covers `research/artifacts/sylvester-exact-globality-and-kernel-compression-2026-09-12.md` (696ae35bc7,
wired at 0a9c95f793). I re-derived Sections 1–3 and recomputed the displays in the four claim nodes and their four
routes. Neither claim is decision-level. Both hold for every Sylvester rank function, and the kill-D route of
Section 4.1 still needs the OPEN `sylvester-disjoint-cylinder-defects-strictly-submultiplicative`.

### 39.1 Submodularity and the containment calculus (Lemmas 1.1, 1.3): PASS

- **Lemma 1.1.**
  - The row blocks of `diag([A; B], [B; C])` are `[A, 0]`, `[B, 0]`, `[0, B]`, `[0, C]`.
  - The right factor `[[I, 0], [I, I]]` sends a row `[a, b]` to `[a + b, b]`. The blocks become `[A, 0]`, `[B, 0]`,
    `[B, B]`, `[C, C]`, and subtracting the second from the third gives `[0, B]`.
  - After a row permutation the matrix is upper triangular with corners `[A; B; C]` and `B`, and (S4) gives the
    inequality. Every step is an invertible factor or a permutation.
- **Lemma 1.3.**
  - (1) `(Y M) W = (Y (x) I_m) · M W`. (2) `diag(I, U (x) I_m)` is invertible. (3) `(M v) W = M (v W)`.
  - (4) With `(A, B, C) = (M W, M' W, M'' W)`, the hypotheses make the right side `psi(M W) + psi(M' W)`. So the triple
    stack has rank at most `psi(M W)`, and deleting rows squeezes `psi([M W; M'' W])`.
  - (5) With `(A, B, C) = (M_1 W, M W, M_2 W)`, both pairs on the right have rank `psi(M W)` after a row permutation,
    and `[M_1; M_2] W = [M_1 W; M_2 W]`.
  - The node's "unchanged by invertible left factors" also holds in the first argument, since `psi(U M W) = psi(M W)`
    and `[U M W; M' W] = diag(U (x) I, I) [M W; M' W]`.

### 39.2 Exact globality (Lemmas 2.1–2.2, Theorem 2.3, Corollary 2.5): PASS, constant 1

- **Lemma 2.1, forward.**
  - `h s h^-1 - 1 = h (s - 1) h^-1`, so `X_(hSh^-1) = (h I_k) X_S h^-1`.
  - Since each `h s h^-1` lies in `Gamma`, [CA] Lemma 2.1(1) gives `X_(hSh^-1) = Y_h X_S`.
  - So `X_S h^-1 = (h^-1 Y_h) X_S`, and Lemma 1.3(1) gives `X_S ≼ X_S h^-1`.
- **Lemma 2.1, reverse.**
  - Invertible factors give `psi(Y_h X_S) = psi(X_S h^-1) = psi(X_S)`.
  - Apply the Frobenius inequality to `(Y_h (x) I_m, X_S (x) I_m, Z)`, using `psi(X_S (x) I_m) = m psi(X_S)` from (S3).
    It gives `psi(X_S Z) = psi(Y_h X_S Z) = psi(X_S h^-1 Z)`.
  - This uses only `h` in `P_Gamma`, and no fixed-point-freeness. With the forward containment and a row
    permutation, it is `X_S h^-1 ≼ X_S`.
- **Lemma 2.2.**
  - `1` is in `H` by Lemma 1.3(1) with `Y = I`.
  - Lemma 1.3(3) with `v = k` and transitivity, used in both directions, give `hk` in `H`. Taking `v = h^-1` gives
    `h^-1`.
  - So `H` is a subgroup containing `P_Gamma`.
- **Theorem 2.3.**
  - I re-derived [CA] Proposition 3.1(1). The two-sided ideal generated by the `s - 1` contains `n - 1` for every `n`
    in the normal closure. Expanding the right coefficients over group elements gives finitely many translates.
  - Iterated Lemma 1.3(5) gives `X_S ≼ Sigma`, Lemma 1.3(1) gives `Sigma ≼ X`, and transitivity gives `X_S ≼ X`.
  - The displayed chain follows. The hypothesis `psi(X Z) = psi(Z)` enters only at its first equality.
- **Corollary 2.5.**
  - `g Gamma_B g^-1 <= Gamma_B` iff `u^-1 g u` compresses `Gamma_0`, so `P_(Gamma_B) = u P_(Gamma_0) u^-1`.
  - Normal generation passes to conjugates, and `iota_B(X) = X_(S_B)`.
- **Correction forward (Remarks 2.4, calibration).**
  - The example is right. The 4-dimensional sum-zero module is the Steinberg module of `A_5 = SL_2(4)`, which is
    absolutely irreducible. `N(A_4) = A_4`, `Fix(A_4)` is spanned by `(1,1,1,1,0)`, and `psi(X_S) = 3/4`.
  - But "normal generation alone still gives the `1/m` bound" holds only at `Z = 1`, where `psi(Sigma) <= m psi(X_S)`
    needs no translation invariance.
  - For general `Z` the same example breaks it. `F_2[A_5]` maps onto `M_4(F_2)`, so some `Z` maps to the projection
    onto `Fix(A_4)`. Then `psi(Z) = 1/4` and `psi(X_S Z) = 0`.
  - So [CA] Proposition 3.1(3) also needs the compression hypothesis, as its statement says. No node displays the
    wrong sentence.

### 39.3 Kernel compression and the triangular count (Lemmas 3.1, 3.2): PASS

- **Lemma 3.1.**
  - `sigma >= 0`, and (S1) holds: `rho([P_n; 0]) = n rho(P)` and `1 <= rho([P; 1]) <= rho(I_1) = 1`.
  - (S3), (S4). The rows `[P_n, 0]`, `[0, P_q]`, `[A, D]`, `[0, B]` permute to the triangular block with corners
    `[P_n; A]` and `[P_q; B]`.
  - (S2), right factor. `diag(I_p, A) [P_p; B] = [P_p; A B]`. No commutation is needed.
  - (S2), left factor.
    - `B' - P_n [I_n, -B] - B [0, P_p] = [0, P_n B - B P_p]`. This is `0` because the entries of `B` lie in `C`.
    - So `rho([B'; C']) = rho(C') = n + p rho(P)`, after the column factor `[[I, B], [0, I]]`.
    - In the triple stack, `A' - A [I_n, -B] = [0, A B]`. The same column factor leaves the rows `[0, A B]`, `[I_n, 0]`,
      `[0, P_p]`, of rank `n + rho([P_p; A B])`.
    - Lemma 1.1 gives `rho([P_p; A B]) - p rho(P) <= rho([P_n; A]) - n rho(P)`.
  - Regular check. If `eU` is the right annihilator of `P`, then `rho([P_n; A]) - n rho(P)` is the rank of `A` on
    `(eU)^n`, and `A` preserves the annihilators because it commutes with `P`.
- **Lemma 3.2.**
  - `T [P, 0] - P [T, T] = [T P - P T, -P T] = [0, -P T]`.
  - Appending a zero row does not change `rho`, and (S4) with corners `[P; T]` and `-P T` gives the count.
  - In a regular ring it reads `dim(ker P + ker T) <= dim ker PT`. That holds because `ker P` and `ker T` lie in
    `ker PT = ker TP`.

### 39.4 Near-minimal multiplicativity (Setting 3.3, Theorem 3.4, Corollary 3.5): PASS

- **Setting 3.3.**
  - A fixed-point-free `psi` has `psi(X) = 1`, so it is non-augmentation and `psi_omega(A) = psi(X A)/psi(X) = psi(A)`.
  - Conversely every `rho_omega` is fixed-point-free ([CA] Corollary 2.3, with `R^x` perfect).
  - The two sets coincide, so the infima agree.
- **Step 1.** `iota_B(X Z) P_n = iota_B(X) (iota_B(Z) P_n)`, and Corollary 2.5 applies to the matrix `iota_B(Z) P_n`
  over `F_2[R^x]`. So `tau` is fixed-point-free and `tau(E) >= c_*^Syl`.
- **Step 2.**
  - Lemma 3.1 applies with `rho(P) = f(k) <= 1/2`, and pulling back along the unital map `iota_B` keeps (S1)–(S4).
  - The row blocks of `iota_B(X) [P_n; iota_B(Z)]` permute to `[(iota_B(X) (x) I_n) P_n; iota_B(X Z)]`, so
    `sigma(Z) <= sigma(X Z)`. The factor `diag(I_n, iota_B(X) (x) I_m)` gives the reverse.
  - With `n = 1`, `psi([P; T]) >= f(k) + c_*^Syl (1 - f(k))`.
- **Steps 3–4.**
  - `psi(T) = f(1) = delta`, since `B1000` is a proper cylinder. Lemma 3.2 then gives (b).
  - For (c), put `e_k = f(k) - delta^k`, so `e_1 = 0` and `e_(k+1) = (f(k+1) - delta f(k)) + delta e_k`. Hence
    `|e_k| <= eps delta / (1 - delta) <= 2 eps delta`.
- **Corollary 3.5.**
  - Each axiom, and fixed-point-freeness, is a closed condition on finitely many coordinates of `prod_A [0, n_A]`.
  - The set is nonempty because `rho_omega` exists, and evaluation at `E` is a coordinate projection.
  - At `eps = 0`, (a) and (b) give `f(k+1) = c_*^Syl f(k)`. Steps 2–3 squeeze `psi([P; T])`, so `sigma(E) = c_*^Syl`
    and Lemma 3.2 is an equality.

### 39.5 Displays, subsumption and inputs

- **Displays.**
  - The formulas in the four claim nodes and the four routes match the artifact.
  - For the reverse containment, the route cites part 3 of `perfect-group-augmentation-quotient-ranks-are-fixed-point-free`.
    That is valid under the hypotheses of Theorem 2.3, although Lemma 2.1 needs less.
- **Subsumption scan.** I checked every node mentioning globality, near-minimality, multiplicative defects or kernel
  corners, with no truncation.
  - `leavitt-rank-models-kazhdan-fixed-ideals-are-global`, `near-minimal-defect-models-have-multiplicative-cylinder-defects`
    and `leavitt-defect-descent-chain-holds-in-regular-rank-rings` use the same mechanisms for rank-ultraproduct
    models and faithful regular rank rings. There fixed ideals are principal, and `c_*` is an infimum over a smaller
    class.
  - The new claims do not imply the older ones, which cover every tensor degree and near-minimality relative to the
    larger `c_*`. The older ones do not reach general Sylvester rank functions. Nothing is subsumed or refuted.
  - The firewalls `finite-subgroup-data-cannot-force-defect-submultiplicativity` and
    `commuting-subgroup-witnesses-cannot-distort-defect-ranges` realize the independent profile that Section 4.2
    compares against. They contradict nothing here.
- **Section 4.1.** This is an implication from an OPEN claim. Its arithmetic checks: `(1 - theta) delta^2 <= 2 eps delta`
  with `delta >= c_0`. The route is not in my queue, so I add no verdict line.
- **Cited, not re-derived.**
  - [CA] Theorem 4.1: `c_0`, and `0 < f(k) <= 1/2`.
  - [CA] Corollary 2.3 and Proposition 3.1, through `perfect-group-augmentation-quotient-ranks-are-fixed-point-free`
    (verified by `w4-vf-gate`, Section 26).
  - The compression semigroup and normal generation of `Gamma_0` ([CA] Section 3, Application, and
    `binary-leavitt-unit-group-is-simple`).
  - Perfection of `R^x`.
  - [DG] Fact 1.2: `V`-transitivity on tuples with proper union, and commutation on disjoint cylinders.

## 40. Semidihedral and GL_2(F_3) blocks (w6-wf-stage1-b; fb787cf5fe): PASS

Scope:
- the artifact `research/artifacts/semidihedral-and-gl2-f3-blocks-forced-states-2026-09-12.md`;
- the claims `gl2-f3-anti-central-states-are-forced-by-semidihedral-blocks` and
  `semidihedral-anti-central-blocks-are-not-full`;
- the routes `gl2-f3-anti-central-states-forced-proof` and `semidihedral-blocks-not-full-proof`.

I re-derived Lemma 1.1, Theorem 1.2, Remark 1.3, Theorem 2.1, Proposition 2.2, Proposition 3.1 and Remark 4.1 on
paper. Neither claim is decision-level. No trace-lowering relation and no one-sided pair is constructed, and
`anti-central-lifted-trace-is-relatively-positive` stays OPEN.

### 40.1 Lemma 1.1, Theorem 1.2 and Remark 1.3

- **Matrices.** `h = w + d = [[1,1],[1,-1]]` and `wd = -dw`, so `h^2 = 2I = -I` and `h^(-1) = zh`.
  - `hw = [[1,1],[-1,1]]` has trace `2 = -1` and determinant `2 = -1`, so its characteristic polynomial is `p_+`.
  - `(hw)^2 = [[0,-1],[1,0]] = wd`, so `(hw)^4 = (wd)^2 = z`.
  - `wh = [[1,-1],[1,1]]` and `dh = [[1,1],[-1,1]]`, so `I + wh + dh = 3I = 0` and `rho_1(c_2) = 0`.
  - `chi(h) = -1` and `chi(w) = chi(d) = 1`, so `rho_2(c_2) = -(I - wh - dh) = I`. So `c_1` and `c_2` are the unit
    elements of `B_1` and `B_2`.
- **Lemma 1.1.**
  - `p_+ p_- = (x^2 - 1)^2 - x^2 = x^4 + 1`. Since `p_+ - p_- = 2x` and `p_+(0) = -1`, they are coprime.
  - `(hw)^(-1) = w h^(-1) = z wh`, so `w (hw) w = wh = (hw)^3`.
  - Modulo `p_+`, `x^3 = -x - 1` and `x^6 = x - 1`, so `p_+(x^3) = -3 = 0` and `sigma` fixes `k_+`.
  - `rho_2(hw) = -rho_1(hw)` has characteristic polynomial `p_+(-x) = p_-`, which is irreducible over `F_3`. So
    `k_+(rho_1(hw)) = I` and `k_+(rho_2(hw)) = 0`, and `k_+([hw]) eps_- = c_1`.
- **Theorem 1.2.**
  - *Part 1.* `det h = -2 = 1` and `det w = -1`, so `hw` acts on `V'` by `-rho_1(hw)`, which `k_+` kills. `z` acts by
    `det(-I)(-I) = -I`. So `V'|_SD` is the two-dimensional simple module `Q_2` of `B_2 ≅ M_2(F_3)`.
  - *Part 2.*
    - `[GL : SD] = 48/16 = 3`, so `dim Ind Q_1 = 6`, and Frobenius reciprocity gives a nonzero map `Ind Q_1 -> V`.
    - The Sylow 3-subgroup has order three, so `3 | dim P(V)` and `2 <= dim P(V) <= 6`.
    - A three-dimensional cover would leave a one-dimensional kernel with `z -> -1`, but every character has
      `lambda(z) = lambda(wd)^2 = 1`.
    - `V` and `V'` restrict to the non-isomorphic absolutely simple modules `Q_1` and `Q_2`. So
      `2 . 6 + 2 . 6 = 24 = dim eps_- F_3[GL]`, and there is no third simple module.
  - *Part 3.* `trl(P(V)) = 2 . 6/48 = 1/4 = 2 . 2/16 = trl(q_1)`.
  - *Part 4.* `[c_i] = 2[q_i]`, because `B_i ≅ M_2(F_3)`. So `s([q_1]) = t/2` and `s([q_2]) = (1 - t)/2`.
  - *Part 5.* `h`, `w` and `d` are symmetric, with `h^2 = z` and `w^2 = d^2 = 1`, so `alpha(h) = zh`, `alpha(w) = w`
    and `alpha(d) = d`.
    - Hence `alpha_*(c_2) = -eps_-(1 - [wh] - [dh])`, which `rho_1` sends to `I` and `rho_2` to `0`.
    - So `alpha_*` exchanges `c_1` and `c_2`, and an invariant state gives `1/4` to both `[q_i]`.
- **Remark 1.3.**
  - `chi` is trivial on `<w, d>`, and `Q_8 = <wd, h>` has a unique faithful two-dimensional module, so both blocks
    restrict to the natural module there. Inducing it to `SD` gives `Q_1 (+) Q_2`.
  - The correction forward to Remark 3.3 of the forced-states artifact is right. "Its modular blocks carry further
    unforced splits" should read "carry the same split `t`".

### 40.2 Theorem 2.1 and Proposition 2.2

- **Theorem 2.1.**
  - *Forward.* `H_fin(H) <= L_1`.
  - *Reverse.* Positivity on `H_fin(H) ∩ K_0^+` gives a state
    (`anti-central-state-exists-iff-lifted-trace-relatively-positive`), and averaging gives an `alpha_*`-invariant
    state `s` (`anti-central-k0-states-can-be-chosen-transpose-invariant`).
    - `s = trl` on `H_fin(H)`, by part 2 of `anti-central-k0-states-equal-lifted-trace-on-signed-thompson`, and on
      `H_fin(GL)`, by Theorem 1.2(5).
    - Both are additive, so they agree on `L_1`, and `trl = s >= 0` on `L_1 ∩ K_0^+`.
  - *Equivalent form.* A class `x = [P] - [Q] = [X]` with `trl(x) < 0` is a stable isomorphism
    `P (+) S_-^r ≅ Q (+) X (+) S_-^r` with `trl(P) < trl(Q)`. Conjugate subgroups give conjugate idempotents, so
    conjugates of `GL` add nothing.
- **Proposition 2.2.** I recomputed each product.
  - `tau^2 = 1 + 3 s_00 t_00 = 1`, `tau s0 = s0 + s_00 t0` and `t1 tau = t1`. So `tau n tau = 1 + N` with
    `N = s0 t1 + s_00 t_10`.
  - All four products of two terms of `N` contain `t1 s0 = 0`, so `N^2 = 0`. Also `s0 t1 N = 0`, so
    `n (1 - N) = 1 - s_00 t_10`.
  - `v^2 = 1` term by term. `t_10 s_00 = t_01 s_00 = t_11 s_00 = 0`, so `v s_00 = s_00`, and `t_10 v = t_01`.
  - So `v (1 - s_00 t_10) v = 1 - s_00 t_01 = x^(-1)`, and
    `G = <V, x> <= <H, GL>` (`leavitt-prime-field-units-generated-by-v-and-one-transvection`).
- **Remark 2.3.** Positivity on all of `H_fin(G)` implies the OPEN relative-positivity claim and is not a case of it.

### 40.3 Proposition 3.1 and Remark 4.1

- **Part 1.** `w + d = h` in `R`, so `1 + wh + dh = 1 + h^2 = 0`. The values of `pi'` follow from part 5 in 40.1.
- **Part 2.**
  - The four matrices sum to `[[a,b],[c,d]]`. I checked `[[a,1],[-1,0]] [[0,-1],[1,a]] = I` and
    `[[0,1],[-1,d]] [[d,-1],[1,0]] = I` in both orders.
  - So `G` spans `R` through the chart. `alpha` fixes `z`, so `alpha_*` is an automorphism of `S_-`, and
    `(pi, pi')(c_1 a + c_2 b) = (pi(a), pi'(b))`.
- **Part 3.** `pi(eps_-) = 1`, so `ker pi` and `ker pi'` are proper. A split surjection `(c_1 S_-)^m -> eps_- S_-` gives
  `eps_- = sum_k a_k c_1 b_k`, and `pi'` gives `1 = 0`.
- **Part 4.** `alpha` fixes `H` pointwise (part 1 of the transpose-invariant node).
- **Remark 3.2.** `R ≅ R^2`, so `K_0(R) = 0`.
- **Remark 4.1.**
  - `BA = rho iota = I`. `AB = I` would force `iota rho = 1` on `S_-^n (+) (S_- (+) Y)`, which is false.
  - `eps_+` is central and kills the entries, so `(B + eps_+ I)(A + eps_+ I) = eps_- I + eps_+ I = I`.
  - The step from no state to item 3 is cited, as the artifact says.

### 40.4 Displays, scan and inputs

- **Displays.** The formulas in both claim nodes and both routes match the artifact and my recomputation. These
  include `c_2`, `k_+`, the six-dimensional covers, the lifted traces `1/4`, the values of `pi` and `pi'`, and
  `v n (tau n tau)^(-1) v^(-1) = 1 - s_00 t_01`.
- **Inputs.** The four requirements of the forced route, and the one of the not-full route, are ESTABLISHED on
  main. `anti-central-lifted-trace-is-relatively-positive` and `ternary-anti-invariant-swap-corner-is-full` are OPEN,
  and the new nodes claim neither.
- **Subsumption scan.** I checked every node mentioning `GL_2(F_3)`, `SD16`, the semidihedral blocks, `pi'` or `k_+`,
  with no truncation.
  - `anti-central-k0-states-can-be-chosen-transpose-invariant` gives `t = 1/2` for invariant states. The new content
    is `H_fin(GL) = H_fin(SD)`, so that normalization forces `trl` on all of `GL_2(F_3)`. Neither implies the other.
  - `leavitt-semisimple-torsion-units-conjugate-iff-same-support`, Corollary 3, shows that the level-one Singer
    element, hence `SD16`, is not conjugate into `E ⋊ V`. This is consistent, because Theorem 2.1 works through
    states, not conjugation.
  - `leavitt-invisible-half-universal-over-every-finite-field` says no scalar-free subgroup of `GL_2(F_3)` carries a
    nonzero idempotent killed by the natural representation. This is consistent: `pi` kills `c_2`, but `SD` contains
    the scalar `h^2 = z`.
  - `ternary-anti-central-pairs-visible-or-invisible` normalizes through `pi` alone; Proposition 3.1 adds `pi'`.
  - Nothing is subsumed or refuted.
- **Next constants.** `-I` acts trivially on the adjoint module of `GL_3(F_3)`, so the `det` twist lies in the
  anti-central block, and the twist is self-dual since `det^2 = 1`. I did not check the forcing question, which
  belongs to `w7-gl3-f3-states`.
- **Cited, not re-derived.**
  - Corollary 3.2 of the forced-states artifact: invariant states exist.
  - Theorem 2.2(1)–(4) of the extension artifact.
  - `anti-central-k0-states-equal-lifted-trace-on-signed-thompson`, part 2.
  - `leavitt-prime-field-units-generated-by-v-and-one-transvection`.
  - `twisted-leavitt-corner-fullness-equals-absence-of-k0-states`, items 3 and 5, and Theorem E behind them.
  - Krull–Schmidt, Frobenius reciprocity, and freeness of projectives over a Sylow subgroup.

## 41. Two-piece corner criterion and finite-dimensional chart representations (w6-wf-stage1-a; 8e889c4923, 13c4f95756): PASS

Scope:
- the artifact `research/artifacts/ternary-one-transvection-two-piece-lift-2026-09-12.md` (blob `9329b3a18d`);
- the claims `two-piece-left-inverses-are-corner-left-inverses` (Theorem A) and
  `finite-dimensional-chart-reps-kill-one-transvection-lift` (Proposition E);
- the routes `two-piece-left-inverses-are-corner-left-inverses-proof` and
  `finite-dimensional-chart-reps-kill-one-transvection-lift-proof`.

Both claim nodes ask for re-derivation. I re-derived Sections 1–8 of the artifact on paper; the standard inputs I only
cite are listed in 41.4. Neither claim is decision-level. `one-transvection-ternary-s0-lift-is-left-invertible`
stays OPEN: Proposition E restricts where a left inverse can live and refutes nothing.

### 41.1 Section 1, Theorem A and Corollary A.1

- **Honest idempotents.**
  - `eps_-^2 = 4(2 - 2[z]) = 8(1 - [z]) = eps_-`, and `[z] = -1` in `S_-`.
  - For an involution `d`, the same computation gives `P_d^2 = P_d`, and `[d]P_d = P_d[d] = 2([d] - 1) = -P_d`.
  - `d1^2 = 1 + 3 p1 = 1` and `pi(P1) = 2(1 - d1) = -2 p1 = p1`.
  - `d0 = z d1` gives `[d0] = -[d1]`, so `P0 + P1 = 4 = 1` and `P0 P1 = 4(1 - [d1]^2) = 0`.
  - `pi(P0) = 2(2 + p1) = 1 - p1 = p0`.
- **Theorem A(1).** `v = P'vP'` gives `vP = 0`.
  - `c'P = P + vP - PhvP = P`, and `c'hP' = PhP' + vhP' - Ph(vhP') = P'`.
  - So `c'b = 1` with `b = P + hP'`. Since `a = u0 b`, `c = c'u0^(-1)` gives `ca = 1`.
- **Theorem A(2).** Put `C = cu0`. Then `Cb = CP + ChP' = 1`.
  - Multiplying on the right by `P` gives `CP = P`, since `P'P = 0`.
  - Multiplying on the right by `P'` gives `ChP' = P'`.
  - So `P'CP = 0` and `P' = P'ChP' = (P'CP')hP'`.
  - Both directions hold in any unital ring, as the route says.
- **Corollary A.1.**
  - `pi(a) = u0 s0 t0 + u1 s1 t1 = s00 t0 + s01 t1 = s0`. This is not a unit, so `ca = 1` forces `ac != 1`.
  - `pi(Y_h) = s10 t1` corresponds to `s0` under `y -> t1 y s1`, so it is a proper isometry of `p1 R p1`.

### 41.2 Proposition B, Construction C and Section 5

- **Proposition B.**
  - For (2): `P[g]P[k]P = 2P[g](1 - [d])[k]P = 2(Y_(gk) - Y_(gdk))`, and `2 = -1`.
  - For (3), `4 = 1` gives `Y_g = [g] - [dg] - [gd] + [dgd]`. Up to `z`, the only possible coincidence is
    `dg = ±gd`:
    - `dg = gd` gives `2[g] - 2[dg] != 0`;
    - `dg = zgd` gives `[gd] = -[dg]` and `[dgd] = -[g]`, so `Y_g = 0`.
  - Distinct double cosets `DgD` have disjoint supports.
  - (4) is (2) applied to `v = sum lambda_g Y_g`.
  - `pi(Y_g) = s1 g_11 t1` is `p1 g p1 = s1 (t1 g s1) t1`.
- **Construction C.**
  - `t01 s00 = t1 s0 = 0`, so `x^(-1) = 1 - s00 t01` and `x^3 = 1`.
  - `g0` sends `s0, s10, s11` to `s00, s01, s1`.
  - `t01 s00 = 0`, `t01 s01 = 1` and `t01 s1 = 0` give `u0 = s00 t0 + (s01 - s00) t10 + s1 t11`, and `u0 s0 = s00`.
  - The chart entries of `h = s0 t1 - s1 t0 + s10 t1` are `0, 1, -1, s0`.
  - `[[0,1],[-1,s0]]` and `[[s0,-1],[1,0]]` multiply to `I` in both orders.
  - `omega^2 = -I` and `omega [[1,-s0],[0,1]] = h`.
  - `u0 s1 = (s01 - s00) t0 + s1 t1` and `u0 s10 = s01 - s00`.
  - So `u1 = u0 h = s00 t00 + s01 (t1 - t00) - s1 t01`, and `u1 s1 = u0 (s0 + s10) = s01`.
  - `P0 = -(1 + [d1])` and `P1 = -(1 - [d1])` give the four-term `a`.
  - On the visible side, `(s1 t10)(s10 t1) = s1 t0 s0 t1 = p1`.
- **Lemma D.1.** A finite quotient that is injective on `supp(ba - 1)` sends `ab = 1` to the finite-dimensional
  algebra `K[Q]`, and there it forces `ba = 1`.
- **Proposition D.**
  - Theorem A(1) in `S_-(H)`, with `u0 = 1` and `u1 = h`, gives `c'b = 1` for `b = P0 + [h]P1`.
  - Direct finiteness would make `pi(b) = p0 + hp1 = [[1,1],[0,s0]] = diag(1,s0)[[1,1],[0,1]]` a unit.
  - But `diag(1,t0)diag(1,s0) = 1` and `diag(1,s0t0) != 1`, so `diag(1,s0)` is not a unit.
- **The partner k.**
  - `k = [[0,-1],[1,t0]]` and `[[t0,1],[-1,0]]` multiply to `I` in both orders.
  - `kh = [[1,-s0],[-t0,-1]]` and `k d1 h = [[-1,s0],[t0,0]]`, using `t0 s0 = 1`.
  - So `pi(Y_k Y_h) = s1(0 - (-1))t1 = p1`.
- **Claim D.3.**
  - `rho(P1)` is idempotent, so `tr rho(Y_g) = 2(tr rho(g) - tr rho(d1 g))`.
  - This is `2((a+c)^2(a'+c') - (a-c)^2(a'-c')) = 8aca' + 4(a^2+c^2)c' = 2aca' + a^2c' + c^2c'`.
  - The values at `g = 1`, `k d1 h` and `kh` are all `1`.
  - The images `[[-1,s],[s^(-1),0]]` and `[[1,-s],[-s^(-1),-1]]` have the inverses the artifact states. The
    second has determinant `-1 - 1 = 1`.
  - So `tr rho(w) = 1 - 1 - 1 = -1`.
- **The finitary involution.**
  - `hk = [[1,t0],[s0,1 + s0t0]]`, and `1 + s0t0 = -1 - e`.
  - `t0 e = 0`, `e s0 = 0` and `(1 + e)^2 = 1 + 3e = 1` give `(hk)^2 = -diag(1,1+e)`.
  - `n = diag(1,1+e) = 1 + s1 e t1 = 1 + p1 - s10 t10`, and `rho0(n) = I` because `e -> 0`.

### 41.3 Proposition E, its corollaries, and Sections 6–7

- **Ring map.** `rho(z) = (-1)^3 = -1`, so `rho(eps_-) = 2 · 2 = 1`, and `rho` is unital on `eps_- F_3[H]`.
- **Odd part.**
  - `psi0*(d1) f = f ∘ psi0(d1)`, which is `±f` on `V±*`. So `rho(d1)` acts on `W_(abc)` by the sign `abc`.
  - `rho(P1) = 2(1 - rho(d1))` is `0` on the even blocks and `4 = 1` on the odd ones.
- **Compression.** `v = P1 v P1` and `v Y_h = P1` give `rho_O(v) rho_O(h) = 1_O`. So `rho_O(h)` is injective on
  the finite-dimensional space `O`, hence onto.
- **Missing block.**
  - For `f in V-*`, `psi0*(h) f = f ∘ g^(-1)` vanishes on `V-`, because `g^(-1)V- = V+`.
  - Into `W_(++-)`, the blocks from `(++-)` and `(+-+)` have first factor `pi+ g i+ = 0`.
  - The block from `(-++)` has second factor `0`, and the block from `(---)` has third factor `0`.
  - `g` maps `V+` onto `V-` and `V != 0`, so `dim V+ = dim V- >= 1` and `W_(++-) != 0`.
- **Why a tensor cube.** `psi0(P1)` is the projection onto `V-`, and `psi0(Y_h) = pi- g i-`. For `GL_2(phi)`
  this is `phi(s0)`, which can be invertible.
- **Corollary E.1.**
  - `t0 d1 s0 = 1`, `t1 d1 s1 = 2 = -1`, and the off-diagonal entries vanish, so `d1 = diag(1,-1)`.
  - `psi0(h) = [[0,I],[-I,phi(s0)]]` sends `(x,0)` to `(0,-x)`.
- **Instances.**
  - `F_3[s0]` and `F_3<s0,s1>`: distinct words in the `s_i` are distinct normal-form monomials. So these algebras
    are polynomial and free, and `s_i -> 1` is well defined.
  - `T = F_3<s0,t0>`: the monomials `s0^a t0^b` are independent and multiply through `t0 s0 = 1`, so
    `s0, t0 -> 1` is well defined.
  - `F_3<s0,t0,t1>`: the monomials `s0^a t_nu` have no `s1 t1` junction, so they are independent.
  - They are closed under multiplication through `t0 s0 = 1` and `t1 s0 = 0`, so `s0, t0 -> 1`, `t1 -> 0` is well
    defined.
- **Corollary E.2.**
  - `h s0 = -s1` and `h^(-1) s1 = -s0`, so both displayed entries vanish.
  - `t_u d1 s_w = delta_uw + t_u s1 t1 s_w`, which gives sign `-1` exactly on words beginning with `1`.
  - `psi0(h)V+ ⊆ V-` and `psi0(h)^(-1)V- ⊆ V+`, so `psi0(h)V+ = V-`.
- **What escapes.**
  - In a finite-dimensional representation, `t1 s1 = 1` makes `s1` invertible. Then `t0 s1 = 0` gives `t0 = 0`,
    which contradicts `t0 s0 = 1`.
  - `[[s0, s1t0],[0,t1]]` and `[[t0,0],[s0t1,s1]]` multiply to `I` in both orders, using `t0 s1 = t1 s0 = 0` and
    `s0t0 + s1t1 = 1`.
- **Section 6.**
  - Item 2 is Proposition D applied to `H_v`, followed by Elek–Szabó.
  - Item 5 and "What escapes" are Corollary E.1 applied to `A_v`.
  - T1: `rho_O(Y_k Y_h) = rho_O(k) rho_O(h)` is not onto, so `P1 + w` is not invertible in the corner.
  - This subsumes Claim D.3, because a nilpotent `w` would make `P1 + w` invertible.
  - T2: `n` and its `H1`-conjugates lie in `GL_2(T)`.
  - Item 3 is stated conditionally, and I did not re-derive it.
- **Section 7.**
  - `F_3[C_3] = F_3[X]/(X - 1)^3` is local.
  - `M_x = 1 + [x] + [x^2] = N_x^2`, `pi(M_x) = (x - 1)^2 = 0` and `M_x^2 = N_x^4 = 0`.

### 41.4 Displays, scan and inputs

- **Displays.** Both claim nodes and both routes match the artifact and my recomputation:
  - `c = (P + v - Phv) u0^(-1)` and `v = P'cu0P'`;
  - the four-term `a`, `h`, `h^(-1)` and `omega`;
  - `Y_g Y_k = Y_(g d1 k) - Y_(gk)`;
  - the block `V+ ⊗ V+ ⊗ V-*`, the instance maps, and the Thompson unit with its inverse.

  The Attempts entries of the OPEN lift node match Sections 5, 6 and 8.
- **Subsumption scan.** I checked, without truncation, every claim node that mentions:
  - lifts of `s0` or two-piece lifts;
  - `Y_h`, sign-Hecke corners, `psi0` or tensor cubes;
  - `J_1(S_-)` or one-sided units.

  Findings:
  - `two-piece-s0-lifts-telescope-to-a-corner` (over `F_2`) fixes the partner and asks, through `C'C`, when `ba`
    is a unit. It is consistent with Theorem A: a unit `C'C` makes `C` left invertible, but not conversely.
  - Four nodes are over `F_2` with triangular pieces: `finite-support-triangular-two-piece-s0-lifts-do-not-exist`,
    `two-piece-s0-lift-with-triangular-defect-exists`, `finite-support-multi-piece-triangular-s0-lift-exists`
    and `triangular-piece-lifts-need-non-directly-finite-shift-group`. Section 6 item 2 has the shape of the last.
  - `swap-separated-pairs-avoid-finitely-represented-supports` filters a different equation and needs `w in H`.
    Its one-sided-inverse argument gives only bijectivity of `rho_O(h)`.
  - `depth-monotone-configurations-cannot-force-ternary-minus-one`: the remark after Corollary D.2 is consistent
    with it, and Proposition E does not use it.
  - `leavitt-unit-hosts-exclude-matrices-over-commutative-rings` concerns maps of the whole group. Proposition E
    represents proper subgroups such as `GL_2(T)`, so the two are consistent.
  - Three nodes are over `F_2`, and neither claim decides them: `s0-lifts-cannot-be-supported-in-the-all-ones-stabilizer`,
    `left-invertible-lift-of-s0-in-leavitt-group-algebra` and `leavitt-unit-group-algebra-not-directly-finite`.
  - `odd-tensor-closure-kills-projective-zpc-gluing-identities` concerns different identities.
  - Nothing is subsumed or refuted.
- **Cited, not re-derived.**
  - `weakly-finite-reflection-ideal-detects-weakly-finite-images`: `ca = 1 != ac` gives `J_1(S_-) != 0`.
  - Elek–Szabó.
  - Residual finiteness of `GL_2(F_3[s0])` through congruence maps.
  - `SL_fin(F_3) <= GL_2(T)`, which makes `GL_2(T)` not residually finite.
  - The absence statement that no node on main decides soficity of `GL_2(T)`.

## 42. Two-root gate lower bounds and commuting Jordan certificates for matrix states (w6-upg-separate; fdf1237ec2): PASS

Scope:
- the artifact `research/artifacts/two-root-certificates-separate-2026-09-12.md` (blob `0116f471c9`);
- the claims `two-root-gate-lower-bounds-hold-for-matrix-states` (Sections 1–2) and
  `commuting-jordan-certificates-flatten-to-minors` (Section 3);
- the routes `two-root-gate-lower-bounds-matrix-states-proof` and `commuting-jordan-certificates-flatten-proof`.

Both claims landed ESTABLISHED before verification. I re-derived on paper Lemma 2.1, Theorem 2.2, items 2–5 of
Theorem 2.3, and all of Section 3. For items 1 and 6 of Theorem 2.3 the check is a step census of the proofs in
`research/artifacts/char-three-defect-gap-and-descent-2026-09-12.md` ([C3], blob `45397b534e`), not a re-derivation
of [C3]. Neither claim is decision-level, and nothing is refuted.

### 42.1 Matrix states, Lemma 2.1 and Theorem 2.2 (claim items 1–2)

- **Facts from the three axioms.**
  - `d(M) <= min(rows, columns)`, since `M = M I_c = I_r M`.
  - `M + N = [I I] (M (+) N) [I I]^T`, so `d(M + N) <= d(M) + d(N)`.
  - `d(UMV) = d(M)` for invertible `U`, `V`, and `d(M (+) 0) = d(M)`, since each is a minor of the other.
- **Item 1 (Lemma 2.1).**
  - `ker d` is an ideal, since `d(x + y) <= d(x) + d(y)` and `d(axb) <= d(x)`. It is proper, since `d(1) = 1`.
  - `d` descends. A matrix `E` with entries in `ker d` is a sum of one-entry matrices, each a minor of an entry, so
    `d(E) = 0`. Then `d(M + E) <= d(M) + d(E)` and `d(M) <= d(M + E) + d(-E)` give `d(M + E) = d(M)`.
  - The descended state is faithful on elements by construction.
  - Push-through. Row and column operations reduce `[[I_n, X],[Y, I_m]]` to `I_n (+) (I_m - YX)`, and also to
    `(I_n - XY) (+) I_m`. So `n + d(I_m - YX) = d(I_n - XY) + m`, which is the display of Lemma 2.1 at `m = n`.
  - Suppose `XY = I_n` modulo `ker d`. Then `d(I_n - XY) = 0`, so `d(I_n - YX) = 0`. Each entry of `I_n - YX` is a
    minor, so it lies in `ker d`, and `YX = I_n` modulo `ker d`.
- **Item 2 (Theorem 2.2).**
  - `D_rho` lies in `ker d`. So `rho` followed by the quotient map is a representation of `Γ` into the weakly finite
    `K`-algebra `A/ker d`, and it kills the defect.
  - `weakly-finite-leavitt-representations-killing-defect-are-trivial` gives `rho(g) - 1` in `ker d`. Section 36.2
    re-derived steps 4–5 of that node and cited steps 1–3. The artifact's application is the same argument.
  - On `K[Γ]`, with `rho` the inclusion, `ker d` contains the augmentation ideal. That ideal is maximal, so
    `A/ker d = K`. A faithful matrix state on a field is the rank, since `M = U (I_r (+) 0) V` with `U` and `V`
    invertible.

### 42.2 Theorem 2.3 (claim item 3)

- **Scope.** `eps_+ = 2(1 + [z])` and `eps_-` are orthogonal central idempotents with `eps_+ + eps_- = 4 = 1`. Since
  `1 = [1 1] (eps_+ (+) eps_-) [1 1]^T` and `eps_+ (+) eps_- = [eps_+; eps_-] 1 [eps_+ eps_-]`, every matrix state has
  `d(eps_+) + d(eps_-) = 1`. So each `d` in `A_mat` has `d(eps_+) = 0` and factors through `S_-`. Conversely, a matrix
  state on `S_-` pulls back along `F_3[G] -> S_-`.
- **Nonemptiness.** So `A_mat` is nonempty iff `S_-` carries a matrix state. By item 2 of
  `sylvester-rank-functions-iff-no-triangular-certificate`, that holds iff `S_-` has the rank condition. The easy
  direction checks: `XY = I_(n+1)`, with `Y` of size `n x (n+1)`, gives `n + 1 <= d(Y) <= d(I_n) = n`.
- **Compactness and positivity.** Every value lies in `[0, min(rows, columns)]`, and every axiom is a closed
  condition. So `A_mat` is compact, and `c_3^mat` is attained. If `d(D) = 0`, item 2 gives `d(1 - [z]) = 0`, hence
  `d(eps_-) = 0`.
- **Item 2 (Lemma 1.2).** `P` commutes with the entries of `phi(Y)`, so `phi(XMY) P = phi(X) (phi(M) P) phi(Y)`, and
  `d(phi(XMY) P) <= d(phi(M) P)`. Normalization and additivity need `phi` unital and `d(P) > 0`.
- **Items 3–4 (Lemmas 1.3–1.4).**
  - The identities `1 - [gh] = (1 - [g]) + [g](1 - [h])`, `1 - [g^(-1)] = -[g^(-1)](1 - [g])` and
    `1 - [kgk^(-1)] = [k](1 - [g])[k^(-1)]` make `K_d` a normal subgroup.
  - If `d(D_A) = 0`, then `d o F_3[iota_A]` is a matrix state killing `D`, so `iota_A(G) <= K_d` by Theorem 2.2.
  - `K_d <z> / <z>` is a nontrivial normal subgroup of the simple group `G/<z>`, so `K_d <z> = G`.
  - `G` is perfect and `z` is central, so `G = [G, G] <= K_d`. Then `z` lies in `K_d`, and `d(eps_-) = 0`.
- **Item 5.**
  - When `d(eps_-) > 0`, compressing along the central idempotent `eps_-` gives `d(D eps_-) >= c_3^mat d(eps_-)`.
  - `iota_A(-1) = 1 - 2 p_A = tau_A`, so `F_3[iota_A](eps_-) = Q_A`, and `Q_A` commutes with the image of
    `F_3[iota_A]`. Compressing along `iota_A` with `P = Q_A` gives an element of `A_mat`, so
    `d(D_A Q_A) >= c_3^mat d(Q_A)`.
  - `d(Q_A) = 1/2` is [C3]'s argument: `N(Q_A) = N(u Q_A u^-1) = N(1 - Q_A)` by Lemma 1.1.5 (conjugation), then
    Lemma 1.1.3 (additivity). Both steps are valid for matrix states. So `d(D_A) >= d(D_A Q_A) >= c_3^mat/2`.
- **Items 1 and 6 (census).**
  - I re-read the proofs of [C3] Lemmas 1.1.1, 1.1.3 and 1.1.5 and Theorems 3.1.2–3.1.4.
  - Each step is a minor, additivity, subadditivity, a commuting idempotent split, conjugation by a unit, or
    compactness. Fact 1.5 is a statement about conjugation in `G`.
  - The Frobenius inequality (Lemma 1.1.2) enters only through Lemma 1.1.4. That lemma gives `c_3 <= 2/3` and
    Theorem 3.1.1, and the claim excludes both.

### 42.3 Theorem 3.1, Corollary 3.2 and Example 3.3 (second claim)

- **Base.** At `j = 1` the display is the hypothesis `f <~ xP`.
- **Induction step.** Apply `separated-triangular-steps-flatten-to-minors` (re-derived in Section 37) to
  `f^((+)j) <~ x^j P (+) P^((+)(j-1))` and `f <~ xP`, with corner `P`, up to a permutation of blocks. This gives
  `f^((+)(j+1)) <~ [[x^j P, P],[0, xP]] (+) P^((+)(j-1))`.
- **Frobenius matrix.** Using `P x^j = x^j P`, so that `x P x^j = x^(j+1) P`:
  - `[[x^j P, P],[0, xP]] [[I, 0],[-x^j, I]] = [[0, P],[-x^(j+1) P, xP]]`;
  - `[[I, 0],[-x, I]] [[0, P],[-x^(j+1) P, xP]] = [[0, P],[-x^(j+1) P, 0]]`.
  A column swap and a sign give `P (+) x^(j+1) P`. So `f^((+)(j+1)) <~ P^((+)j) (+) x^(j+1) P`.
- **End.** At `j = m`, `x^m P = 0`, and a zero block drops out of a minor bound.
- **Corollary 3.2.**
  - Take an idempotent `f <~ xP` and an idempotent `e` with `P <~ e`. Then `f' = f^((+)m)` is a minor `X e' Y` of
    `e' = e^((+)(m-1))`.
  - Put `a = f' X e'` and `b = e' Y f'`. Then `ab = f' (X e' Y) f' = f'`, `aba = a` and `bab = b`. So `ba` is an
    idempotent equivalent to `f'`, with `e' (ba) e' = ba`.
  - So `[e'] = [ba] + [e' - ba] >= [f']`, and `m s[f] <= (m - 1) s[e]`. Taking the supremum over `f` and the infimum
    over `e` gives the display.
- **Example 3.3.** Take `R = F_3[u]/(u^3)` and `d(M) = dim_(F_3) soc(Im M)`.
  - `d(I_1) = dim soc R = 1`, and `d` is additive on block sums.
  - `Im(MY) ⊆ Im M`, and a submodule has a smaller socle.
  - `Im(XM)` is a quotient of `Im M`. A finitely generated `R`-module is a sum of cyclic modules `R/(u^i)`, and its
    socle dimension is the number of summands, `dim N/uN`, which does not grow under quotients. So `d(XMY) <= d(M)`.
  - `d(u) = dim (u^2 R) = 1`. With `x = u`, `P = 1` and `m = 3`, the value form would give `d(u) <= 2/3`.

### 42.4 Displays, scan and notes

- **Displays recomputed.**
  - The claim displays: `f^((+)j) <~ P^((+)(j-1)) (+) x^j P` and `rho^s(xP) <= (1 - 1/m) rho_s(P)`.
  - The route displays: `[[x^j P, P],[0, xP]] ~ P (+) x^(j+1) P` and `n + d(I - YX) = d(I - XY) + n`.
  - The item 3 values `d(Q_A) = 1/2` and `d(D_A Q_A) >= c_3^mat/2`.
  - `N_12^3 = [x_12(1)]^3 - 1 = 0` in characteristic three, the instance with `m = 3`.
- **Cited, not re-derived.** The Section 1 census of [TRI] Theorem A and D.2 and of [RR] Propositions 6, 8 and
  Corollary 9. Neither claim depends on it.
- **Subsumption scan** (ESTABLISHED nodes on matrix states, weakly finite images, minors and Jordan certificates).
  - `rank-condition-rings-have-weakly-finite-images` (Theorem C) is consistent with item 1 and is its global form: it
    builds a weakly finite image from the rank condition alone.
  - `k0-state-extends-to-rank-function-iff-triangular-monotone` is consistent with the "Not included" paragraph.
  - `separated-triangular-steps-flatten-to-minors` and `nilpotent-jordan-certificates-flatten-to-minors` are inputs
    and special cases (Section 37).
  - Nothing is subsumed or refuted. The Consequence paragraph is the route checked in Section 43.
- **Notes.**
  - The compression bullet of claim item 3 omits the hypotheses `d(P) > 0` and `phi` unital. Artifact Theorem 2.3.2
    has `d(P) > 0`.
  - The sentence `c_3^mat <= c_3` after artifact Theorem 2.3 needs anti-central Sylvester rank functions to exist.
    The node has the proviso.
  - The lane's Attempts entries on `anti-central-weakly-finite-images-carry-rank-functions` and
    `ternary-anti-central-disjoint-defects-have-a-strict-deficit` were not checked.
- **Status.** Not decision-level. No claim changes status.

## 43. The strict deficit over matrix states restates emptiness (w7-matrix-state-deficit; f3545c8591): PASS on routes, claim stays OPEN

**Scope.**
- Artifact `research/artifacts/matrix-state-deficit-item-two-2026-09-12.md`, Sections 1–5. Section 6 (literature)
  was not checked.
- Claim `ternary-anti-central-matrix-state-defects-have-a-strict-deficit` (OPEN).
- Routes:
  - `matrix-state-deficit-gives-nonpositive-unit-class`;
  - `nonpositive-unit-class-makes-matrix-state-deficit-vacuous`;
  - `rank-kill-makes-ternary-strict-deficit-vacuous`;
  - `matrix-state-strict-deficit-restricts-to-rank-functions`.

**Verdict.** PASS on all four routes and on Theorem 2.2. The claim is a restatement: in each scope the target
holds iff the state space is empty. The claim stays OPEN. This is decision-relevant: the deficit target that
`w3-strategist-gate` relies on is emptiness itself, not a reduction of it.

### 43.1 Facts (F1)–(F5)

- **(F1).** For `A_mat` this is item 3, bullet 2, of `two-root-gate-lower-bounds-hold-for-matrix-states`, which was
  re-derived in Section 42.2. For `A_S` it is [C3] Theorems 2.1 and 3.1, cited.
- **(F2), re-derived.** Put `phi = F_3[iota_B]`, which is unital, and `P = Q_B D_A`.
  - `D_A` lies in `F_3[iota_A(G)]`, and this commutes with `iota_B(G)` because the cylinders are disjoint.
  - `Q_B = 2(1 - [tau_B])` is central in `F_3[iota_B(G)]`, since `tau_B = iota_B(z)` is central in `iota_B(G)`.
  - So `P` commutes with every entry of `phi(X)`, and `d'(X) = d(phi(X) P)/d(P)` is a matrix state, by the
    compression step of Section 42.2.
  - In scope `A_S`, the triangular axiom also passes to `d'`, because
    `[[phi(A) P, phi(C) P], [0, phi(B) P]] = [[phi(A), phi(C)], [0, phi(B)]] (P (+) P)`.
  - Normalization: `tau_B^2 = 1` gives `Q_B^2 = 4(2 - 2 tau_B) = 8(1 - tau_B) = 2(1 - tau_B) = Q_B` over `F_3`. So
    `d'(eps_-) = d(Q_B Q_B D_A)/h = 1`.
- **(F3), (F4).** These are [C3] 3.1.2 and 3.1.4 at `k = 1`, carried to `A_mat` by item 3, bullet 4, of the same
  node. They are cited. Their census check is in Section 42.2.
- **(F5).** This is item 2 of `sylvester-rank-functions-iff-no-triangular-certificate` ("carries a matrix state ...
  iff `A` has the rank condition, iff `(K_0(A), [A])` admits a state"), together with item 3, bullet 1, of the
  matrix-state node. Checked against both nodes on main.

### 43.2 Lemma 2.1, Theorem 2.2, Corollary 2.3 and Remark 2.4

**Lemma 2.1, re-derived.**
- Suppose item 1 holds at `d_0`. By the contrapositive of (F4), `h(d_0) > 0`, so (F2) puts `d_0'` in `S`.
- By minimality, `d_0'(D) >= c = d_0(D)`.
- By (F1), `d_0(D) > 0`, so `d_0'(D) > theta d_0(D)` for every `theta < 1`.
- The artifact adds "and this inequality is (F3)". That is true, because `F_3[iota_B](D) = D_B` gives
  `d_0'(D) = d_0(D_B Q_B D_A)/h`, but minimality alone already gives the inequality.

**Theorem 2.2, re-derived.**
- **Both parts.** Vacuity gives one direction and Lemma 2.1 the other.
- **Part 1.** `A_S = ∅` is the kill claim, because `N(eps_-) = N(2(1 - [z])) = N(1 - [z])` (2 is a unit in `F_3`).
- **Part 2, first equivalence.** This is (F5).
- **Part 2, second equivalence.**
  - *No state gives a nonpositive class.* This is part 2 of `anti-central-state-obstruction-equals-stable-finiteness`.
  - *A nonpositive class leaves no state.* `k[eps_-] + [Q] = 0` with `k >= 1` would give `k + s[Q] = 0` with
    `s[Q] >= 0`, which is impossible.
  - *A matrix state gives a state.*
    - `d(0) = 0`, because `0_2` and `0_1` are mutual minors and `d(0_1 (+) 0_1) = 2 d(0_1)`.
    - `d(eps_+) = 0`: with `U = [[eps_+, eps_-], [-eps_-, eps_+]]` and `U^(-1) = [[eps_+, -eps_-], [eps_-, eps_+]]`,
      we get `U (1 (+) 0) U^(-1) = eps_+ (+) eps_-`, so `d(eps_+) + d(eps_-) = 1`.
    - So `d` is a matrix state on `S_-` (node item 1).
    - `d` is additive on idempotent matrices.
    - Murray–von Neumann equivalent idempotents are mutual minors: from `e = ab`, `f = ba`, `a = eaf` and
      `b = fbe`, we get `a f b = a (ba) b = (ab)^2 = e` and `b e a = (ba)^2 = f`.
    - `s[eps_-] = d(eps_-) = 1`.
- **Theorem C sentence.** "By Theorem C this is also `ternary-anti-central-summand-has-no-weakly-finite-image`"
  agrees with `rank-condition-rings-have-weakly-finite-images`.

**Corollary 2.3.**
- **Restriction, re-derived.** `N(XMY) <= N(MY) <= N(M)`, so `A_S ⊆ A_mat`, and `d'` has the same formula in both
  scopes.
- **Converse.**
  - If `A_mat` is nonempty, then `(K_0(S_-), [eps_-])` has a state.
  - (U1), as stated on `ternary-anti-central-states-give-sylvester-rank-functions`, then gives `N` on `S_-` with
    `N(eps_-) = 1`, and its pullback lies in `A_S`.
  - So `A_S = ∅` forces `A_mat = ∅`, which is the direction claimed.
- **Not opened.** The node `ternary-counterexample-from-rank-kill-and-state-realization`.

**Remark 2.4, re-derived.**
- Suppose `h(d_0) > 0` at some configuration. Then minimality contradicts item 2.
- So `h(d_0) = 0` at every configuration, and (F4) gives `d_0(D_A D_B) = 0`.

### 43.3 Proposition 3.1 and Remark 3.2

**Proposition 3.1, re-derived.**
1. **`W` is the largest weakly finite image.**
   - `S_-/J` embeds in the product of the `S_-/I`.
   - `XY = I` holds componentwise, so `YX = I` componentwise: products are weakly finite, and so are unital
     subrings.
   - Every weakly finite image factors through `W`.
   - `W` maps onto the nonzero image of Theorem C, so `W != 0`.
2. **A minimizer descends.** `d_0(eps_+) = 0`, so `d_0` is a matrix state on `S_-`. By node item 1,
   `S_-/ker d_0` is weakly finite, so `J ⊆ ker d_0` and `d_0` descends.
3. **Violators on `W`.**
   - A matrix state on `W` pulls back into `A_mat`, since `eps_- -> 1`.
   - `W = 0` carries no state.
   - `W != 0` gives the rank condition. A failure `XY = I_n` with `X` of size `n x m`, `m < n`, pads to
     `X' = [X 0]` and `Y' = [Y; 0]`. Weak finiteness then gives `Y'X' = I_n`, but `Y'X'` has a zero last row.
   - The rank condition passes up from `W` to `S_-`, and (F5) gives a minimizer.

**Other paragraphs.**
- **"Smaller images."** The last sentence holds: `S_-/ker d_0` is nonzero and weakly finite, so it has the rank
  condition. A maximal `J'` with `J' ⊆ ker d_0` must then equal `ker d_0`.
- **"Which relations it uses."** This list was compared with (F1)–(F4). It was not re-audited step by step against
  the proofs of [SEP] Theorem 2.2 and [C3] 3.1.4.

**Remark 3.2, re-derived.** It is not load-bearing.
- `H -> (F_3[u]/(u^3))^x` factors through `H^ab`, and `1 + u` has order 3.
- `N_12, N_23 -> u` and `D -> u^2`.
- `dim soc(u^2 F_3[u]/(u^3)) = 1 = dim soc(F_3[u]/(u^3))`.

### 43.4 Proposition 4.1 and Section 5

**Proposition 4.1, re-derived.**
- The display is `n = d(I_n) = d(X I_(n-1) Y) <= d(I_(n-1)) = n - 1`.
- Padding a failure of size `n x m` to `n x (n-1)` adds zero columns and rows.
- Theorem 2.2.2 then finishes.

**Lemma 5.1, re-derived.**
- **1 ⟹ 2.** Put `e = x D y` and `g = (yx) D`.
  - `g^2 = y e x D` and `g^3 = y e^2 x D = g^2`.
  - `x (D g^2) y = (xDy)^3 = e`, so `g^2 != 0`.
- **1 ⟹ 3.** Put `g = D (yx)`.
  - `g^2 = D y e x = g^3`.
  - `x g^2 D y = e^3 = e`.
- **2 ⟹ 1 and 3 ⟹ 1.** These are the minors `a D 1` and `1 D a`.

**Lemma 5.2, re-derived.**
- **First case.** `1 = [a_1 ... a_k] (D (+) ... (+) D) [b_1 ... b_k]^T`.
- **Second case.** A nonzero `W/WDW` with the rank condition carries a matrix state. It pulls back into `A_mat` and
  kills `D`, which contradicts node item 3, bullet 2 (positivity of `c_3^mat`).

**Facts, re-derived.**
- **The evaluation `pi`.**
  - `pi(D) = e_23 e_12 = 0`.
  - `pi(eps_-) = 2(1 - (-1)) = 4 = 1`.
  - `pi(Q_C) = 2(1 - (1 - 2p_C)) = 4 p_C = p_C`.
  - So `S_- D S_- ⊆ ker pi` misses `eps_-`.
- **`D = D y D`.** Then `(yD)^2 = yD`, and `yD != 0`.
- **The matrix example.** `e_22 = e_21 e_12`.
- **Nilpotent entries.** An idempotent with entries in `(u)` is `e = e^3`, with entries in `(u)^3 = 0`.
- **Status of (c).** The open status of (c) is as the artifact says.

### 43.5 Routes, displays and scan

**Routes, all PASS.**
- **`matrix-state-deficit-gives-nonpositive-unit-class`.** Steps 1–4 re-derived.
  - "Item 3 of the second requirement" matches item 3, bullets 2 and 4, of the node on main.
  - Item 2 of the Sylvester node and part 2 of the obstruction node match.
  - The target form `k[eps_-] <= 0` matches `ternary-anti-central-unit-class-is-nonpositive`.
- **`nonpositive-unit-class-makes-matrix-state-deficit-vacuous`.** Steps 1–3 re-derived.
  - `S_-^r ~= S_-^r (+) S_-^k (+) Q` gives `k[eps_-] + [Q] = 0`.
  - The mutual-minor display is checked.
- **`rank-kill-makes-ternary-strict-deficit-vacuous`.** Steps 1–2 re-derived.
  - Its Equivalence paragraph describes the gate route `ternary-rank-kill-via-anti-central-defect-deficit` as the
    minimizer contradiction. That contradiction is Lemma 2.1 in scope `A_S`.
- **`matrix-state-strict-deficit-restricts-to-rank-functions`.** Steps 1–2 re-derived.
  - Its Scope bullets agree with Theorem 2.2 and with the statement of (U1).

**Claim node.**
- The Restatement bullets agree with Theorem 2.2 and Corollary 2.3.
- In the Violators bullets, the "largest weakly finite image `W`" is the `W` of Proposition 3.1.

**Scan (main `a49eed5622`).** I grepped the claim nodes for `matrix state|A_mat|strict deficit|rank condition` and
got 81 files. The 22 ESTABLISHED claims among them were read for implication, subsumption and refutation.
- **Same ideal.** `weakly-finite-reflection-ideal-detects-weakly-finite-images`: its `J_omega` is the smallest ideal
  with weakly finite quotient, so it equals the `J` of Proposition 3.1. Proposition 3.1 item 1 is a second proof of
  that node's first two bullets. Consistent.
- **Different `W`.** In `rank-condition-rings-have-weakly-finite-images` and
  `anti-central-rank-condition-gives-weakly-finite-image`, `W` is a maximal rank-condition quotient. The artifact
  keeps it apart from the `W` of Proposition 3.1. Consistent.
- **Second route to Theorem 2.2.2.** `twisted-leavitt-corner-fullness-equals-absence-of-k0-states`, items 3–5 at
  `(3, 2, 2)`, give the second equivalence of Theorem 2.2.2 by another route. Consistent.
- **Sylvester form.** `sylvester-rank-function-quotients-are-weakly-finite` is the Sylvester form of node item 1.
  Consistent.
- **Flattening nodes.** `nilpotent-jordan-certificates-flatten-to-minors` and
  `split-identity-minors-survive-triangular-moves` bound states on idempotent minors. The socle state of Remark 3.2
  is not such a bound, and the Fact that every idempotent minor of `u` vanishes agrees with them.
- **Firewall and near-minimal nodes.**
  - The nodes are `anti-central-sofic-data-cannot-force-defect-submultiplicativity`,
    `finite-subgroup-data-cannot-force-defect-submultiplicativity`, `sofic-subgroups-carry-independent-cylinder-defects`
    and the two near-minimal nodes.
  - They build rank models on subgroups, or in characteristic two. None gives an element of `A_mat`, and none
    proves emptiness.
  - This is consistent with the claim being a restatement.
- **Matched on wording only.** The remaining hits either use "rank condition" in another sense or treat the binary
  corner.

Nothing subsumes the claim, and nothing refutes it or any route.

**Notes.** No claim changes status.
1. Lemma 2.1 cites (F3) for an inequality that minimality already gives. This is harmless.
2. Proposition 3.1 and Theorem C both use the letter `W`, for different quotients: the smallest weakly finite
   reflection and a maximal rank-condition quotient.
3. Not checked:
   - Section 6 (literature);
   - the node `ternary-counterexample-from-rank-kill-and-state-realization`;
   - a step-by-step audit of the "Which relations it uses" list.
