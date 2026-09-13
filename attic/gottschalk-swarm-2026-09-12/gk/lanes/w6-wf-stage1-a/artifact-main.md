# One-transvection two-piece lifts of s0 in the ternary anti-central summand

Lane `w6-wf-stage1-a`, 2026-09-12. Mathematics on paper; nothing was computed.

## 0. Setting and summary

`R = L_(F_3)(1,2)`, `G = R^x`, `z = -1`, `eps_- = 2(1 - [z])`, `S_- = eps_- F_3[G]`, and `pi : S_- -> R` is the
evaluation `[g] -> g`.

**Target.** Find a one-sided invertible element of `S_-` that is not invertible. That gives `J_1(S_-) != 0` in
`weakly-finite-reflection-ideal-detects-weakly-finite-images` (artifact Corollary 1.2 of
`weakly-finite-representations-of-ternary-leavitt-units-2026-09-12.md`). It is also a Kaplansky
direct-finiteness counterexample.

**Results.**
- **Theorem A** (any ring, Section 2). A two-piece combination `a = u0 P + u1 (1-P)` of units has a left
  inverse iff the one-term corner element `(1-P) u0^(-1) u1 (1-P)` has a left inverse in `(1-P)S(1-P)`.
  Both directions come with explicit formulas.
- **Proposition B** (Section 3). The corner at an honest involution idempotent `P_d = 2(1 - [d])` is
  spanned by `Y_g = P_d[g]P_d`, with `Y_g Y_k = Y_(gdk) - Y_(gk)`. So left invertibility of `Y_h` is one
  linear equation in the `Y_g`.
- **Construction C** (Section 4). The transvection `x = 1 + s00 t01` and a Thompson unit give a four-term
  lift `a` of `s0`. Its corner transition is `h = omega (1 - s00 t1)`, where `omega = s0 t1 - s1 t0` and
  `omega^2 = z`; in the `{0,1}` chart, `h = [[0,1],[-1,s0]]`.
- **Proposition D** (Section 5). No left inverse of `Y_h` has all its group elements in a subgroup
  `H` containing `z, d1, h` with `F_3[H]` directly finite: for instance `GL_2(F_3[s0])`, or any locally
  residually finite `H`.
- **Near miss** (Section 5). The partner `k = [[0,-1],[1,t0]]` gives `pi(Y_k Y_h) = pi(P_(d1))`. But
  `Y_k Y_h - P_(d1)` is not nilpotent: a finite-dimensional representation gives it trace `-1`.
- **Open** (Section 6). Is `Y_h` left invertible in `P_(d1) S_- P_(d1)`? Any left inverse needs Toeplitz
  entries of both depth directions: `h` lowers depth, `k` raises it. The group `<h, k, d1, z>` already
  contains the finitary involution `diag(1, 1 + e)` with `e = 1 - s0 t0`.

**Chart.** `a in R` corresponds to the matrix `(t_i a s_j)_(i,j in {0,1})`, and `a = sum s_i a_ij t_j`. This is a
unital ring isomorphism `R ≅ M_2(R)`, because `sum_k s_k t_k = 1`. Words: `s_(ij) = s_i s_j`, and
`t_(ij) = (s_(ij))^* = t_j t_i`.

## 1. Honest idempotents

- `eps_-^2 = 4(2 - 2[z]) = eps_-`, and `1 - eps_- = 2(1 + [z])`. So `S_- ≅ F_3[G]/(1 + [z])`, and `[z] = -1` in
  `S_-`. `pi` is well defined, since `pi([z]) = -1`.
- **Involution idempotents.** For an involution `d in G`, put `P_d = 2(1 - [d])`. Then
  `P_d^2 = 4(2 - 2[d]) = P_d` and `[d] P_d = P_d [d] = -P_d`.
- **The partition.** `d1 = 1 + p1` with `p1 = s1 t1` satisfies `d1^2 = 1 + 3 p1 = 1`, and `pi(P_(d1)) = -2 p1 = p1`.
  With `d0 = z d1` we get `[d0] = -[d1]` and `P_(d0) = 2(1 + [d1])`. So `P_(d0) + P_(d1) = 4 = 1`,
  `P_(d0) P_(d1) = 4(1 - [d1]^2) = 0` and `pi(P_(d0)) = p0 = s0 t0`.
- **Notation.** Write `P0 = P_(d0)` and `P1 = P_(d1)`. In the chart, `d1 = diag(1,-1)`, `z = -I` and `p1 = e_11`.

## 2. Theorem A: the two-piece corner criterion

**Theorem A.** Let `S` be a unital ring, `P` an idempotent, `P' = 1 - P`, `u0, u1` units of `S`, `h = u0^(-1) u1`,
and `a = u0 P + u1 P'`. Then `a` has a left inverse in `S` iff there is `v in P'SP'` with `v · P'hP' = P'`.
Explicitly:
1. if `v in P'SP'` and `v h P' = P'`, then `c = (P + v - P h v) u0^(-1)` satisfies `c a = 1`;
2. if `c a = 1`, then `v = P' c u0 P'` lies in `P'SP'` and satisfies `v h P' = P'`.

*Proof.* `a = u0 b` with `b = P + hP'`. So `c a = 1` iff `(c u0) b = 1`, and it suffices to treat `b`.

(1) Put `c' = P + v - P h v`. From `v = P' v P'` we get `vP = 0` and `v = vP'`.
- `c'P = P + vP - P h vP = P`.
- `c' h P' = P h P' + v h P' - P h (v h P') = P h P' + P' - P h P' = P'`.
- So `c' b = c'P + c'hP' = 1`, and `c = c' u0^(-1)` satisfies `c a = 1`.

(2) Put `C = c u0`, so that `C b = CP + ChP' = 1`.
- Multiplying on the right by `P` gives `CP = P`; multiplying by `P'` gives `ChP' = P'`.
- Then `P'CP = P'P = 0`, so `P' = P'ChP' = P'CP·hP' + P'CP'·hP' = (P'CP') hP'`.
- Put `v = P'CP'`. ∎

**Remarks.**
- **A four-term element becomes a one-term corner element.** `a` involves four group elements once
  `P = P_(d0)`. The corner element `P'hP' = P1[h]P1` is a single compressed group element.
- **Not the binary telescoping criterion.** `two-piece-s0-lifts-telescope-to-a-corner` fixes the partner
  `b = E^[g1^(-1)] + E1^[g2^(-1)]` and asks when `ba` is a unit, through `C'C`. Theorem A asks for any left
  inverse and involves only `C = P'hP'`. It holds in any ring and in any characteristic.

**Corollary A.1 (lifts of s0).** In `S = S_-` with `P = P0`, suppose `u0 s0 = s00` and `u1 s1 = s01`. Then
- `pi(a) = u0 s0 t0 + u1 s1 t1 = s00 t0 + s01 t1 = s0`, which is not invertible in `R`;
- so `a` is not invertible, and any left inverse `c` gives `c a = 1 != a c`;
- then `1 - ac` is a nonzero element of `J_1(S_-)`.

So stage one follows from a left inverse of `Y_h := P1[h]P1` in `P1 S_- P1`. Moreover `pi(Y_h) = p1 h p1` is
a proper isometry of `p1 R p1`, so the corner problem is again a lift problem, one corner down.

## 3. Proposition B: the sign-Hecke corner

**Proposition B.** Let `d in G` be an involution, `P = P_d`, `D = {1, d, z, zd}`, and put `Y_g = P[g]P`.
1. `Y_(dg) = Y_(gd) = Y_(zg) = -Y_g`, `Y_1 = P`, and `P S_- P` is spanned by the `Y_g`.
2. `Y_g Y_k = Y_(gdk) - Y_(gk)`.
3. `Y_g = 0` iff `d g = z g d`. Otherwise `Y_g` is supported on exactly four classes of `DgD / <z>`. Nonzero
   `Y_g` for distinct double cosets `DgD` are linearly independent.
4. `Y_h` is left invertible in `P S_- P` iff `sum_g lambda_g (Y_(gdh) - Y_(gh)) = Y_1` for some finitely
   supported `lambda : G -> F_3`.

*Proof.*
1. `[d]P = 2([d] - 1) = -P` and `P[d] = -P`, and `[z] = -1`. The `P[g]P` span `P S_- P`.
2. `P[g]P[k]P = 2 P[g](1 - [d])[k]P = 2(Y_(gk) - Y_(gdk))`, and `2 = -1`.
3. As `4 = 1`, `Y_g = (1 - [d])[g](1 - [d]) = [g] - [dg] - [gd] + [dgd]`. The classes of `G/<z>` form a basis of
   `S_-` up to sign, so cancellation needs two of `g, dg, gd, dgd` to agree up to `z`.
   - `g = ±dg` and `g = ±gd` are impossible, since `d != ±1`.
   - The remaining coincidences are all `dg = ±gd`.
   - If `dg = gd`, then `Y_g = 2[g] - 2[dg] != 0`.
   - If `dg = zgd`, then `[gd] = -[dg]` and `[dgd] = -[g]`, so `Y_g = 0`.
   - Otherwise the four classes are distinct. Distinct double cosets have disjoint supports.
4. Write `v = sum lambda_g Y_g` and apply (2). ∎

**Consequence.** Take `d = d1`. A left inverse is a finite `F_3`-combination of double cosets `D g D` such
that the products `g d1 h` and `g h` cancel down to the single double coset `D`. Under `pi` every `Y_g` goes
to `s1 g_11 t1`, where `g_11` is the `(1,1)` chart entry. So the equation always reduces to
`sum lambda_g ((g d1 h)_11 - (g h)_11) = 1` in `R`, and that reduced equation is solvable. The difficulty
lies entirely in `ker pi`.

## 4. Construction C: the one-transvection lift

**Data.**
- **The transvection.** `x = 1 + s00 t01`. Since `t01 s00 = t1 t0 s0 s0 = t1 s0 = 0`, `(s00 t01)^2 = 0`, so
  `x^(-1) = 1 - s00 t01` and `x^3 = 1`.
- **The Thompson unit.** `g0 = s00 t0 + s01 t10 + s1 t11` carries the prefix code `{0, 10, 11}` onto
  `{00, 01, 1}`, and `g0 s0 = s00`.
- **First piece.** `u0 = x^(-1) g0 = s00 t0 + (s01 - s00) t10 + s1 t11`. This uses `t01 s00 = 0`, `t01 s01 = 1`
  and `t01 s1 = 0`, and it gives `u0 s0 = x^(-1) s00 = s00`.
- **Transition.** `h = s0 t1 - s1 t0 + s10 t1 = [[0,1],[-1,s0]]`, with `h^(-1) = s00 t0 - s0 t1 + s1 t0 = [[s0,-1],[1,0]]`.
- **Sign element.** `omega = s0 t1 - s1 t0 = [[0,1],[-1,0]]` satisfies `omega^2 = z`, and
  `omega^(-1) h = [[1,-s0],[0,1]] = 1 - s00 t1`. So `h` is a signed Thompson unit times one transvection
  `T_(00,1)(-1)`, of depth pattern `(2,1)`.
- **Second piece.** `u1 = u0 h = s00 t00 + s01 (t1 - t00) - s1 t01`.
  - Check `u1 s1 = s01`: `h s1 = s0 + s10`, and `u0 s10 = s01 - s00`, using `t10 s10 = 1` and
    `t0 s10 = t11 s10 = 0`. So `u1 s1 = s00 + s01 - s00 = s01`.
  - Expansion: `u0 s1 = (s01 - s00) t0 + s1 t1`, so
    `u1 = s00 t1 - (s01 - s00) t00 - s1 t01 + (s01 - s00) t1`, which is the formula above.

**The lift.** `P0 = -(1 + [d1])` and `P1 = -(1 - [d1])`, so

```text
a = u0 P0 + u1 P1 = -[u0] - [u0 d1] - [u1] + [u1 d1],        pi(a) = s0.
```

By Theorem A and Corollary A.1, `a` has a left inverse in `S_-` iff `Y_h = P1[h]P1` has one in `P1 S_- P1`.
Then `J_1(S_-) != 0`.

**Visible side.** `pi(Y_h) = p1 h p1 = s10 t1`. Under `p1 R p1 ≅ R`, `y -> t1 y s1`, this is `s0`, with corner
left inverse `s1 t10`: `(s1 t10)(s10 t1) = s1 t0 s0 t1 = p1`. Nothing is visible; the whole question is in
`ker pi`.

## 5. Proposition D: firewall, and the partner near miss

**Lemma D.1.** Let `K` be a field and `H` a group whose finitely generated subgroups are residually finite.
Then `K[H]` is directly finite.

*Proof.*
- Let `ab = 1` in `K[H]`, and let `H0` be generated by `supp a ∪ supp b`. Put `F = supp(ba - 1)`.
- Choose a finite quotient `q : H0 -> Q` that is injective on `F`.
- `q(a) q(b) = 1` in the finite-dimensional algebra `K[Q]`, so `q(b) q(a) = 1`.
- As `q` is injective on `F`, `q(ba - 1) = 0` forces `ba - 1 = 0`. ∎

**Proposition D.** Let `H <= G` contain `z`, `d1` and `h`, and put `S_-(H) = eps_- F_3[H] ⊆ S_-`. If `S_-(H)` is
directly finite, then no `v in P1 S_-(H) P1` satisfies `v Y_h = P1`.

This applies whenever `F_3[H]` is directly finite, because `S_-(H)` is a direct factor of it. For example,
`H` locally residually finite (Lemma D.1), or `H` sofic (Elek–Szabó).

*Proof.*
- Apply Theorem A(1) inside `S_-(H)`, with `P = P0`, `u0 = 1` and `u1 = h`. It gives `c' in S_-(H)` with
  `c' b = 1`, where `b = P0 + [h] P1`.
- Direct finiteness gives `b c' = 1`, so `pi(b) = p0 + h p1` is a unit of `R`.
- In the chart, `p0 + h p1 = [[1,1],[0,s0]] = diag(1,s0) · [[1,1],[0,1]]`.
- The unit `diag(1,t0)` is a left inverse of `diag(1,s0)`, and `diag(1, s0 t0) != 1`, so `diag(1,s0)` is not a
  unit. Contradiction. ∎

**Corollary D.2 (polynomial and free charts are dead).**
- **Polynomial chart.** Through the chart, `H = GL_2(F_3[s0])` contains `z = -I`, `d1 = diag(1,-1)` and `h`.
  `F_3[s0] ⊆ R` is a polynomial ring, since the powers `s0^n` are distinct normal-form monomials. The
  congruence maps to `GL_2(F_3[s0]/(s0^N))` separate points, so `H` is residually finite.
- **Other charts.** The same holds for `GL_m(A)`, whenever `A ⊆ R` is residually finite-dimensional and
  `z, d1, h in GL_2(A)`. For example `A = F_3<s0,s1>`, a free algebra, using the ideals of long words.
- **Consequence.** No left inverse of `Y_h` has all its group elements in such a subgroup.
- **Relation to w6-mismatch-c3.** Both cases lie in the units of `span{s_mu t_nu : |mu| >= |nu|}`. They are
  special cases of the depth-monotone firewall that lane `w6-mismatch-c3` is preparing
  (`depth-monotone-configurations-cannot-force-ternary-minus-one`, not yet on main).

**The partner k.**
- **Data.** `k = [[0,-1],[1,t0]] = -s0 t1 + s1 t0 + s1 t10`, with `k^(-1) = [[t0,1],[-1,0]]`. Then
  `kh = [[1,-s0],[-t0,-1]]` and `k d1 h = [[-1,s0],[t0,0]]`, using `t0 s0 = 1`.
- **Visible agreement.** By Proposition B(2), `Y_k Y_h = Y_(k d1 h) - Y_(kh)`, and
  `pi(Y_k Y_h) = s1 (0 - (-1)) t1 = p1 = pi(P1)`.
- **The kernel element.** `w := Y_k Y_h - P1` lies in `ker pi ∩ P1 S_- P1`, and `w != 0`: by Proposition B(3),
  `kh` and `k d1 h` lie outside `D`.
- **What would suffice.** If `P1 + w` were invertible in the corner, `(P1 + w)^(-1) Y_k` would be a left
  inverse of `Y_h`.

**Claim D.3.** `w` is not nilpotent, so the Neumann series gives nothing.

*Proof.*
- **Setup.** `T = F_3<s0,t0> ⊆ R` is the Jacobson algebra `F_3<s,t | ts = 1>`. Every nonzero ideal of that algebra
  contains `e = 1 - st`, and `s0 t0 != 1` in `R`. So `T` has the ring map `s0 -> s`, `t0 -> s^(-1)` onto
  `F_3[s^(±1)]`.
- **The representation.** Let `rho0 : GL_2(T) -> GL_2(F)`, with `F = F_3(s)`, and put
  `rho = rho0 ⊗ rho0 ⊗ rho0^*`, where `rho0^*(g) = rho0(g)^(-T)`. Then `rho(z) = -1`, so `rho` extends to a ring
  map `eps_- F_3[GL_2(T)] -> M_8(F)`. `w` lives there.
- **Traces.** `rho(d1) = diag(1,-1)^(⊗3)`, so `rho(P1) = 2(1 - rho(d1))` projects onto the span of the `e_ijk`
  with `i + j + k` odd. For `g` with diagonal entries `a, c` and `g^(-1)` diagonal entries `a', c'`,

  ```text
  tr rho(Y_g) = tr(rho(P1) rho(g)) = 2 a c a' + a^2 c' + c^2 c'.
  ```

  - `g = 1` gives `1`.
  - `g = k d1 h -> [[-1,s],[s^(-1),0]]`, with inverse `[[0,s],[s^(-1),1]]`, gives `1`.
  - `g = kh -> [[1,-s],[-s^(-1),-1]]` (determinant `1`), with inverse `[[-1,s],[s^(-1),1]]`, gives
    `2 + 1 + 1 = 1`.
- **Conclusion.** `tr rho(w) = 1 - 1 - 1 = -1 != 0`, so `rho(w)` is not nilpotent, and neither is `w`. ∎

**The finitary involution.** Put `H1 = <h, k, d1, z>`. A direct computation, using `t0 e = 0`, `e s0 = 0` and
`(1 + e)^2 = 1`, gives

```text
hk = [[1,t0],[s0,-1-e]],        (hk)^2 = -diag(1, 1+e).
```

So `n = z (hk)^2 = diag(1, 1 + e) = 1 + p1 - s10 t10` is an involution of `H1` in the kernel of `rho0`.
- `H1` meets the finitary part `1 + M_2(span{s0^a e t0^b})`, which is locally finite.
- Neither Lemma D.1 nor the representation `rho` separates that part, so Proposition D is not
  available for `H1`.

## 6. The open question and where a left inverse must live

**Open question.** Is `Y_h = P1[h]P1` left invertible in `P1 S_- P1`? By Theorem A, this is the same as asking
whether the four-term lift `a = -[u0] - [u0 d1] - [u1] + [u1 d1]` of `s0` is left invertible in `S_-`.

**What a left inverse must contain.**
1. **One linear equation.** By Proposition B(4), a finitely supported `lambda` with
   `sum lambda_g (Y_(g d1 h) - Y_(gh)) = Y_1`.
2. **A non-sofic subgroup.** Let `H_v = <z, d1, h, supp lambda>`. By Proposition D, `eps_- F_3[H_v]` is not
   directly finite, and neither is `F_3[H_v]`. So `H_v` is a finitely generated subgroup of `G` that is not
   sofic by Elek–Szabó, and in particular not residually finite. A success therefore also decides a
   harder problem. That matches the shape of the sharpening in
   `triangular-piece-lifts-need-non-directly-finite-shift-group`.
3. **Both depth directions.** By Corollary D.2, `H_v` lies neither in `GL_2(F_3[s0])` nor in `GL_m(F_3<s0,s1>)`.
   - Assuming the `w6-mismatch-c3` firewall, `H_v` is also not conjugate into the units of a weighted
     depth-monotone part.
   - `h` has the terms `s0 t1` and `s1 t0`, which force equal letter weights, and `s10 t1`, which lowers
     depth. So `supp lambda` must contain depth-raising elements such as `k`.
4. **Not the Neumann series.** By Claim D.3, the partner `k` alone does not give a left inverse through a
   Neumann series.

**The region.**
- **Where the configuration lives.** `H1 = <h, k, d1, z> <= GL_2(T)`, where `T = F_3<s0,t0>` is the Jacobson
  algebra, `I = span{s0^a e t0^b} ≅ M_∞(F_3)` is its finitary ideal, and `T/I ≅ F_3[s^(±1)]`.
- **Structure.** `GL_2(T)` is an extension. The kernel `GL_2(T) ∩ (1 + M_2(I))` contains `GL_fin(F_3)` and is
  locally finite. The quotient lies in the linear group `GL_2(F_3[s^(±1)])`.
- **Why the firewalls fail here.** `GL_2(T)` is not residually finite, since it contains the infinite simple
  group `SL_fin(F_3)`. Rank truncations send finitary elements to normalized rank `o(1)`. So neither
  Lemma D.1 nor naive rank models apply.
- **Status on main.** No node decides soficity, or direct finiteness of the group algebra, for `GL_2(T)` or
  its finitely generated subgroups.
- **Consistency.** `toeplitz-defect-dies-in-every-finite-quotient-of-el3` says finite images of `EL_3` over
  `T` kill the defect. A certificate living in this region is consistent with that.

**Next tests (not done).**
- **(T1) Corner invertibility.** Decide whether `P1 + w` is invertible in `P1 eps_- F_3[H1] P1`. A necessary
  condition is invertibility of `rho(P1 + w)` on the four-dimensional odd part, for representations `rho`
  of `GL_2(F_3[s^(±1)])` with `z -> -1`. That rules out only inverses supported in `H1`.
- **(T2) Enlarge the partner set.** Add the finitary involution `n = diag(1, 1 + e)` and its
  `H1`-conjugates. The corner idempotent `P_n = 2(1 - [n])` lifts the rank-one defect `s1 e t1`. Test
  whether the peeling identity `Y_g Y_k = Y_(g d1 k) - Y_(gk)` can cancel the off-`D` terms `Y_(kh)`,
  `Y_(k d1 h)` against terms involving `n`.

## 7. Dead variants recorded on paper

- **Idempotents from x alone.** `F_3[<x>] = F_3[C_3] = F_3[X]/(X - 1)^3` is local, so `x` gives no nontrivial
  idempotents. `N_x = [x] - 1` satisfies `N_x^3 = 0`, and `M_x = 1 + [x] + [x^2] = N_x^2` lies in `ker pi`
  with `M_x^2 = 0`. The pieces have to come from involutions such as `d1`, as in Section 1.
- **Residually finite charts.** Corollary D.2.
- **One partner through the Neumann series.** Claim D.3.
