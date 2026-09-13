# Two-piece involution lifts live on a dihedral support: the one-transvection lift of s0 has no left inverse

Date: 2026-09-12. Lane: `w7-yh-rank-firewall`.

**Nodes.**
- Claim `one-transvection-s0-lift-has-no-left-inverse`, with route `one-transvection-s0-lift-has-no-left-inverse-proof`
  (Sections 1–2).
- **Status: held OPEN pending verification by `w4-vf-linear-b`.** Once verified, it refutes
  `one-transvection-ternary-s0-lift-is-left-invertible` and invalidates route
  `one-transvection-s0-lift-refutes-ternary-surjunctivity`.

**Notation.** As in `research/artifacts/ternary-one-transvection-two-piece-lift-2026-09-12.md`, cited as TP:
- `R = L_(F_3)(1,2)`, `G = R^x`, `z = -1`, `eps_- = 2(1 - [z])` and `S_- = eps_- F_3[G]`;
- `d1 = 1 + s1 t1`, with `P1 = P_(d1) = 2(1 - [d1])` and `P0 = P_(d0) = 2(1 + [d1])` in `S_-`;
- `Y_g = P1[g]P1` and `h = [[0,1],[-1,s0]]`.

## 0. Summary

1. **Theorem 1 (dihedral support).** Let `d in G \ <z>` be an involution and `h in G`. If `P_d[h]P_d` has a left
   inverse in `P_d S_- P_d`, then it is invertible there.
   - Any left inverse projects onto `k[W]`, where `W = <z, d, h^(-1) d h>` is virtually cyclic.
   - A dimension count in a finite quotient of `W` then finishes the proof.
2. **Corollary 2.** If a two-piece element `a = [u0]P0 + [u1]P1` has a left inverse in `S_-`, then it is
   invertible. Lifts of `s0` are never invertible, so no two-piece lift of `s0` over the involution partition of
   `d1` has a left inverse.
3. **Refutation.** In particular `Y_h` has no left inverse, so `one-transvection-ternary-s0-lift-is-left-invertible`
   is false. Section 2 gives a second, direct proof: the representation `s0 -> 0` sends `Y_h` to 0 and `P1` to
   `diag(0,1)`.
4. **Rank version of Proposition E** (Section 4). It names the axioms and states the eigenspace condition in rank
   form.
5. **Models** (Section 5). It records which weakly finite models reach which supports. After Theorem 1 only `W`
   matters.

## 1. Theorem 1 and Corollary 2

**Setting.**
- `k` is a field of characteristic not 2, `G` a group, and `z in G` central of order 2.
- `eps_- = (1 - [z])/2` and `S_- = eps_- k[G]`.
- For an involution `g in G \ <z>`, `P_g = eps_-(1 - [g])/2` is an idempotent of `S_-`. Over `F_3` we have
  `1/2 = 2`, so these are the `P_g` of TP Section 1.
- For a subgroup `H` containing `z`, write `S_-(H) = eps_- k[H]`.

**Theorem 1.** Let `d in G \ <z>` be an involution, `P = P_d`, `h in G` and `Y = P[h]P`. If `vY = P` for some
`v in P S_- P`, then `Y` is invertible in `P S_- P`.

*Proof.*

*Step 1 (conjugated form).* Put `c = h^(-1) d h` and `Q = P_c = [h^(-1)]P[h]`. Then `P[h] = [h]Q`, so
`vY = vP[h]P = v[h]QP`. With `x = v[h]` and `Pv = v`, this reads `P = P x Q P`.
Conversely, if `P = P x Q P`, then `P x [h^(-1)] P` is a left inverse of `Y`.

*Step 2 (projection to W).* Let `W = <z, d, c>`, and let `E : k[G] -> k[W]` keep the coefficients of elements of
`W`.
- For `g in G` and `w in W`, `gw in W` iff `g in W`. So `E(fy) = E(f)y` and `E(yf) = yE(f)` for `y in k[W]`.
- `P`, `Q` and `eps_-` lie in `k[W]`. Applying `E` gives `P = P x' Q P` with `x' = eps_- E(x) in S_-(W)`.

This is the projection step of `subgroup-supported-one-sided-inverse-rigidity`.

*Step 3 (an equivalent idempotent).* Put `alpha = P x' Q` and `beta = QP`, both in `S_-(W)`.
- `alpha beta = P`, so `e = beta alpha` is idempotent.
- `alpha e = P alpha = alpha` and `e beta = beta P = beta`, so `P` and `e` are Murray–von Neumann equivalent in
  `S_-(W)`.
- `Qe = eQ = e`, so `f = Q - e` is an idempotent orthogonal to `e`.

*Step 4 (W is residually finite).* `z` is central and `d^2 = c^2 = 1`, so `W` is a quotient of
`C_2 x (C_2 * C_2)`. There `<dc>` has index at most 4. So `W` is finitely generated and virtually cyclic, hence
residually finite.

*Step 5 (counting in a finite quotient).* Choose a finite quotient `q : W -> K` that is injective on the finite
set `supp(f) ∪ {1, z, d, zd, c, zc}`. Extend `q` to `k[W] -> k[K]`, and put `r(y) = dim_k(y k[K])` for `y in k[K]`.
- **Properties of r.** Equivalent idempotents have equal `r`, `r` is additive on orthogonal idempotents, and
  `r(p) = 0` forces `p = 0`.
- **The two involutions.** Let `g in {d, c}` and `A = <q(z), q(g)>`, which has order 4.
  - As a left `k[A]`-module, `k[K]` is free on a set of right coset representatives. Left multiplication by
    `q(P_g) in k[A]` preserves each summand.
  - `q(P_g)` is a primitive idempotent of the split semisimple algebra `k[A] ≅ k^4`, so `r(q(P_g)) = |K|/4`.
- **Conclusion.** `r(q(e)) = r(q(P)) = |K|/4 = r(q(Q)) = r(q(e)) + r(q(f))`. So `r(q(f)) = 0` and `q(f) = 0`.
  Since `q` is injective on `supp(f)`, `f = 0`, that is `e = Q`.

*Step 6 (the inverse).* Put `v' = P x' [h^(-1)] P`. By Step 1, `v'Y = P`. Using `[h^(-1)]P = Q[h^(-1)]`,

```text
Y v' = P[h]P x' [h^(-1)] P = [h] Q P x' Q [h^(-1)] = [h] beta alpha [h^(-1)] = [h] Q [h^(-1)] = P.   ∎
```

**Corollary 2 (two-piece involution lifts).** Let `d1 in G \ <z>` be an involution, `P1 = P_(d1)`,
`P0 = eps_- - P1`, `u0, u1 in G` and `a = [u0]P0 + [u1]P1`. If `a` has a left inverse in `S_-`, then `a` is
invertible.

*Proof.* Put `h = u0^(-1) u1` and `b = [u0^(-1)] a = P0 + [h]P1`.
- By TP Theorem A(2) (`two-piece-left-inverses-are-corner-left-inverses`), `Y_h` has a left inverse. By
  Theorem 1 it has an inverse `v in P1 S_- P1`.
- Put `b' = P0 - P0[h]P1 v + v`.
  - `b b' = eps_-`, since `b P0 = P0`, `b P0[h]P1 v = P0[h]P1 v` and `b v = P0[h]P1 v + Y_h v = P0[h]P1 v + P1`.
  - `b' b = eps_-`, since `P0 b = P0 + P0[h]P1`, `P0[h]P1 v b = P0[h]P1` and `v b = v Y_h = P1`.
- So `a^(-1) = b'[u0^(-1)]`. ∎

**Lifts of s0.** Let `pi : S_- -> R` be the evaluation map.
- If `u0 s0 = s00` and `u1 s1 = s01`, then `pi(a) = s0` (TP Corollary A.1). `s0` is not a unit, so `a` is not
  invertible, and by Corollary 2 it has no left inverse.
- For the data of TP Construction C, this is the negation of `one-transvection-ternary-s0-lift-is-left-invertible`.
  `a = -[u0] - [u0 d1] - [u1] + [u1 d1]` has no left inverse, and `Y_h` has none in `P1 S_- P1`.

**Remark 1.1 (why the earlier firewalls did not decide it).**
- TP Proposition D and `finite-dimensional-chart-reps-kill-one-transvection-lift` restrict where a left inverse
  can be supported. Step 2 shows that the support can always be moved into `W`.
- `pi(Y_h) = s10 t1` does have a left inverse in `p1 R p1`, but `E` has no analogue in `R`. The obstruction is
  that the corner relation must be witnessed inside `S_-(W)`.

**Remark 1.2 (idempotents of finite subgroups).** Let `A <= G` be a finite subgroup containing `z`, `P in S_-(A)`
an idempotent, `h in G`, `Q = [h^(-1)]P[h]` and `W = <A, h^(-1) A h>`.
- Steps 1–3 and 6 use only `P[h] = [h]Q`.
- Step 5 needs `r(q(P)) = r(q(Q))`. This holds for any `q` injective on `A ∪ h^(-1) A h`, since conjugation by
  `h` is an isomorphism `k[A] -> k[h^(-1) A h]` carrying `P` to `Q`.
- So Theorem 1 and Corollary 2 hold whenever `W` is residually finite.
- If `|A/<z>| = 2`, then `W/<z>` is generated by two involutions and `W` is virtually cyclic.

## 2. A direct check for h = [[0,1],[-1,s0]]

1. **The dihedral group.**
   - In the chart, `c = h^(-1) d1 h = [[s0,-1],[1,0]] · diag(1,-1) · [[0,1],[-1,s0]] = [[-1,-s0],[0,1]]`, and `c^2 = 1`.
   - `d1 c = z u` with `u = [[1,s0],[0,1]]` and `u^3 = 1`. So `d1 c` has order 6 and `(d1 c)^3 = z`.
   - Hence `W = <d1, c>` is dihedral of order 12 and contains `z`. Theorem 1 decides the question inside the
     12-dimensional algebra `F_3[W]`.
2. **The representation `s0 -> 0`.**
   - The chart entries of `z, d1, h, h^(-1), c` lie in `F_3[s0]`. This is a polynomial ring, since the powers
     `s0^n` are distinct normal-form monomials.
   - So `s0 -> 0` defines `psi0 : H0 = <z, d1, h> -> GL_2(F_3)`, with `psi0(z) = -I`, `psi0(d1) = diag(1,-1)`,
     `psi0(h) = [[0,1],[-1,0]]` and `psi0(c) = diag(-1,1)`.
   - Its linear extension is a unital algebra map `S_-(H0) -> M_2(F_3)`, with `psi0(eps_-) = I`,
     `psi0(P1) = diag(0,1)`, `psi0(P_c) = diag(1,0)` and `psi0(Y_h) = diag(0,1) [[0,1],[-1,0]] diag(0,1) = 0`.
3. **Contradiction.**
   - Suppose `vY_h = P1` over `G`. Step 2, with `H0` in place of `W`, gives `v' in S_-(H0)` with `v'Y_h = P1`.
     Applying `psi0` gives `0 = diag(0,1)`.
   - Equivalently, `psi0(P0 + [h]P1) = [[1,1],[0,0]]` is singular.
   - On `W`, `psi0(P_c P1) = 0`, so `P1 in P1 S_-(W) P_c P1` fails directly.

This is TP Corollary E.1 for `A = F_3[s0]` together with the projection. It uses neither residual finiteness nor
Theorem 1.

## 3. Consequences for the graph (once verified)

- **Refuted.** `one-transvection-ternary-s0-lift-is-left-invertible`.
- **Invalidated.** Route `one-transvection-s0-lift-refutes-ternary-surjunctivity`. It stays on main, but its only
  open input would be false.
- **Still true.** `two-piece-left-inverses-are-corner-left-inverses`, since Theorem A holds in any ring, and TP
  Proposition D and `finite-dimensional-chart-reps-kill-one-transvection-lift`. For this lift they are now weaker
  than Theorem 1.
- **Superseded.** TP Section 6 items 2–3 and "The region", and the "Cost" paragraph of the open claim. A left
  inverse does not need a non-sofic subgroup, because none exists.
- **What a repaired two-piece route needs** (Remark 1.2). The idempotent must come from a finite subgroup `A` with
  `|A/<z>| >= 3`, and `h` must make `<A, h^(-1) A h>` not residually finite. Alternatively, the lift must use more
  pieces than Theorem A handles.

## 4. Rank version of Proposition E

Let `H` be a subgroup containing `z, d1, h`, `Phi : S_-(H) -> U` a unital ring map (`Phi(eps_-) = 1`), and `rk` a
Sylvester matrix rank function or matrix state on `U`. Three axioms are used:
- **(R1) Monotone.** `rk(X M Y) <= rk(M)` for matrices over `U`.
- **(R2) Additive on orthogonal idempotents.** `rk(e + f) = rk(e) + rk(f)` when `ef = fe = 0`. This follows from
  additivity on block diagonals, because `e + f` and `diag(e,f)` are related by `X · M · Y` moves in both
  directions.
- **(R3) Faithful**, meaning `rk(y) = 0` implies `y = 0`. It is used only in Lemma 4.2.

**Lemma 4.1 (a deficit is a firewall).** If `vY_h = P1` with `v in S_-(H)`, then `rk Phi(P1) <= rk Phi(Y_h)`.
Only (R1) is used. So a deficit `rk Phi(Y_h) < rk Phi(P1)` excludes left inverses supported in `H`. By the
projection of Step 2 onto `H`, it excludes them over `G` as well.

**Proposition E′ (the eigenspace condition in rank form).**
- *Data.* `T` is an `F_3`-algebra and `psi0 : H -> T^x` a homomorphism with `psi0(z) = -1`. Put
  `p_(±) = 2(1 ± psi0(d1))`.
- *Hypotheses.* `p_+ psi0(h) p_+ = 0` and `p_- psi0(h^(-1)) p_- = 0`.
- *Construction.* `rho = psi0 ⊗ psi0 ⊗ psi0*` maps into `U = T ⊗ T ⊗ T^op`, where `psi0*(x) = psi0(x^(-1))^op`.
  Put `E = p_+ ⊗ p_+ ⊗ p_-^op`.
- *Conclusion.* `rk rho(Y_h) <= rk rho(P1) - rk E` for every rank function on `U` satisfying (R1) and (R2).

*Proof.*
- `rho(z) = -1`, so `rho` is unital on `S_-(H)`. `rho(d1)` acts on `p_a ⊗ p_b ⊗ p_c^op` by the sign `abc`. So
  `rho(P1) = sum_(abc = -1) p_a ⊗ p_b ⊗ p_c^op`, and `E <= rho(P1)`.
- `E rho(h) rho(P1)` is the sum over odd `(a,b,c)` of `p_+ psi0(h) p_a ⊗ p_+ psi0(h) p_b ⊗ (p_c psi0(h^(-1)) p_-)^op`.
  If `a = +` or `b = +`, the first hypothesis kills the term. Otherwise `a = b = -` forces `c = -`, and the second
  hypothesis kills it.
- So `E rho(Y_h) = 0` and `rho(Y_h) = (rho(P1) - E) rho(Y_h)`. Then (R1) and (R2) give the bound. ∎

**Instances.**
- `T = M_n(K)`, with `V_(±) = p_(±) K^n`, recovers TP Proposition E. There
  `rk E = (dim V_+)^2 (dim V_-) / n^3 > 0`.
- A rank ultraproduct of such algebras also works, since tensor products are taken stagewise and
  `rk E = rk(p_+)^2 rk(p_-)`.

**Lemma 4.2 (deficit versus invertibility).**
- `Phi(b)`, with `b = P0 + [h]P1`, is invertible iff `Phi(Y_h)` is invertible in `Phi(P1) U Phi(P1)`. This is because
  `b` is upper triangular for `(P0, P1)` with diagonal `(P0, Y_h)`.
- Assume (R2) and (R3), and let `Phi(v)Phi(Y_h) = Phi(P1)` in the corner. Then `e = Phi(Y_h)Phi(v)` is an
  idempotent under `Phi(P1)` and equivalent to it. So `rk(Phi(P1) - e) = rk Phi(P1) - rk e = 0`, which forces
  `e = Phi(P1)`, and the left inverse is an inverse.

**Lemma 4.3 (states on idempotents see nothing).** If `vY_h = P1`, then `e = Y_h v` is an idempotent equivalent to
`P1`, so `[e] = [P1]`. A `K_0`-state, or any state defined only on idempotents, therefore gives no deficit. A
deficit needs (R1) on the non-idempotent `Y_h`.

## 5. Weakly finite models and the supports they reach

Three supports are relevant:
- `W = <d1, c> ≅ D_12` (Section 2);
- `H0 = <z, d1, h> <= GL_2(F_3[s0])`;
- supports containing the Thompson unit `g0 = [[s0, s1 t0],[0, t1]]`, where TP Section 6 placed a left inverse.

By Theorem 1 only `W` matters.

1. **V rank models and torsion spectra.** Nodes: `v-rank-functions-are-trivial-plus-regular-on-cylinder-groups`,
   `v-rank-torsion-constant-equals-global-fixed-rank`, `thompson-v-rank-models-displace-every-element-uniformly`,
   `signed-thompson-z-moving-rank-functions-match-v-rank-functions`.
   - These models reach `g0`, and `d1` through signed V.
   - They miss `c`, and so miss `W` and `H0`. In the Cantor representation `c 1_([1w]) = 1_([1w]) - 1_([00w])`,
     which is not a signed indicator, so `c` is not a signed prefix bijection.
   - They say nothing about `Y_h`.
2. **Depth-monotone parts** (`depth-monotone-configurations-cannot-force-ternary-minus-one`).
   - `z, d1, h, h^(-1), c` are combinations of `s_mu t_nu` with `|mu| >= |nu|`. So `H0` and `W` lie in the units of
     the depth-monotone part.
   - On `H0` the chart representation `s0 -> 0` is a deficit: `rk psi0(Y_h) = 0 < 1/2 = rk psi0(P1)`.
3. **Graphs of locally finite groups, level HNN extensions and Fock letters.** Nodes:
   `graphs-of-locally-finite-groups-carry-regular-rank-models`, `level-unit-hnn-extensions-have-anti-central-rank-models`,
   `fock-local-letters-extend-level-models-with-disjoint-commutation`,
   `existential-fock-library-has-zero-carrier-or-regular-firewall`.
   - These are rank models of abstract groups built from routed letters. They constrain routed certificates, not
     one element of a fixed group algebra, and there the letter choice for `h` is free.
   - After Theorem 1 no letter choice is needed. The question lives on the finite group `W`, where the normalized
     dimension rank is faithful.
4. **UT4 countermodels and commuting witnesses.** Nodes: `one-shared-root-plus-dyadic-depth-has-ut4-countermodels`,
   `dyadic-perturbation-group-has-three-point-commuting-witness`.
   - These concern different groups, neither of which carries `d1` with `z -> -1`. They do not apply.
5. **Anti-central rank models, matrix states and K_0-states.** Nodes:
   `anti-central-rank-models-kill-ternary-corner-witnesses`, `anti-central-rank-functions-give-weakly-finite-leavitt-images`,
   `matrix-state-strict-deficit-restricts-to-rank-functions`, `ternary-anti-central-matrix-state-defects-have-a-strict-deficit`,
   `gl2-f3-anti-central-states-are-forced-by-semidihedral-blocks`.
   - A rank function or matrix state with `z -> -1` firewalls `Y_h` on its support exactly when Lemma 4.1 gives a
     deficit.
   - States on idempotents alone never do (Lemma 4.3).
   - Theorem 1 is the case `Phi = q` with the dimension rank. It uses faithfulness on `S_-(W)`, not a deficit.
6. **Finite-dimensional chart representations** (`finite-dimensional-chart-reps-kill-one-transvection-lift`).
   - They reach `GL_2(A)` for chart subalgebras `A` with a finite-dimensional representation. This includes `H0`
     and `W`.
   - They miss `g0`, because the chart entries of `g0` and `g0^(-1)` generate `R`.
   - The deficit is TP Proposition E, whose rank form is Proposition E′.

## 6. Outcome

- **Firewalled on every support.**
  - By Step 2 every left inverse of `Y_h` can be moved into `S_-(W)`.
  - So no model has to reach supports containing `g0`, and no unreached support is left to attack with
    Proposition B.
- **Proposition B read on W.**
  - Left invertibility means `P1 in P1 S_- P_c P1` (Step 1). In TP Proposition B(4), with `y = gh`, this is
    `Y_1 in span{Y_(yc) - Y_y}`.
  - Theorem 1 shows it fails whenever `p0 + h p1` is not a unit of `R`.
- **No counterexample here.** If the proof holds, this lift gives no counterexample. The claim stays OPEN until
  `w4-vf-linear-b` re-derives Sections 1–2.
- **Where it stops.** Theorem 1 covers idempotents of involutions and, more generally, finite-subgroup idempotents
  with `<A, h^(-1) A h>` residually finite (Remark 1.2). Two-piece lifts over finite subgroups with
  `|A/<z>| >= 3`, where that group can fail to be residually finite, are not decided here.
