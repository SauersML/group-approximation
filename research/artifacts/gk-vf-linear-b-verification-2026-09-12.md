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
  is not on main at 74c21d92f7. That remark has not been checked.
