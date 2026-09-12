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
