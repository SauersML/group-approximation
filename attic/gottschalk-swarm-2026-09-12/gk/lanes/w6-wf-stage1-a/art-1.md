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
- **Proposition E** (Section 8). Suppose `H ∋ z, d1, h` has a finite-dimensional representation over a
  field of characteristic 3 with `z -> -1`, in which `h` carries the `+1`-eigenspace of `d1` onto the
  `-1`-eigenspace. Then no left inverse of `Y_h` is supported in `H`. The proof compresses `h` on
  `V ⊗ V ⊗ V*`. This applies to `GL_2(A)` for every chart subalgebra `A ∋ s0` with a nonzero
  finite-dimensional representation, the Jacobson algebra `F_3<s0,t0>` (which carries `k`) included. It
  subsumes Claim D.3 and the chart cases of Corollary D.2.
- **Open** (Sections 6 and 8). Is `Y_h` left invertible in `P_(d1) S_- P_(d1)`? The chart entries of any
  left inverse must generate an algebra with no nonzero finite-dimensional representation, for example
  one containing `s0, t0, s1, t1`, as the Thompson unit `g0 = [[s0, s1 t0],[0, t1]]` does.

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
