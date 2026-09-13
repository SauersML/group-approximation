---
rg: 2
id: toms-twisted-swap-pairs-forcing-proof
kind: route
title: The top power of the twist class starts the forcing, Toms's Lemma 1 propagates it, and point traces turn a zero into maximal 2-norm defect
target: toms-twisted-swap-pairs-are-totally-degeneracy-forcing
requires: []
---

Imports from arXiv:2606.12188v2, read on 2026-09-12:
- Section 2: for equal rank `n`, `Delta_n(c(F - E)) = c_(n^2)(F tensor E^*)`, and
  `Delta_n != 0` implies that every bundle map `E -> F` vanishes somewhere.
- The proof of Lemma 1: splitting principle, the rectangular resultant, Künneth
  over torsion-free cohomology.
- Lemma 2: point traces with stage-`i` measure `delta_x`.
- Proposition 4 (3)–(5) and the proofs of Theorems 2 and 5.

**Step 1: forcing at stage `r + 1`.** Let `alpha_1..alpha_w` and
`beta_1..beta_w` be Chern roots of `pi_1^* E` and `pi_2^* E`, and put
`u = c_1(gamma_(r,1)) - c_1(gamma_(r,2))`, pulled back from
`c_1(O(-1)) != 0` on `CP^(j_r)`. The roots of `E_2 tensor E_1^*` are
`beta_j - alpha_i - u`, so

```text
Delta_w(c(E_2 - E_1)) = prod_(i,j) (beta_j - alpha_i - u).
```

- As a polynomial in `u` with coefficients from `X_r x X_r`, the term of degree
  `w^2` is `(-1)^(w^2) u^(w^2)`, with coefficient `1`.
- Every other term has lower degree on the `CP^(j_r)` factor, so it lies in a
  different Künneth summand.
- `u^(w^2) != 0` because `w^2 <= 2 d_r^2 = j_r`.

So `Delta_w != 0`, and every bundle map `E_1 -> E_2` vanishes somewhere.

**Step 2: propagation.**
- Toms's proof of Lemma 1 uses only three inputs for a pair of rank `n` at stage
  `i`: `Delta_n != 0`, torsion-free Künneth, and `y_i^(2 n^2) != 0` on
  `CP^(j_i)`, which holds when `2 n^2 <= j_i = 2 d_i^2`, that is `n <= d_i`.
- It shows that `Delta_(2n)` of the pushforward pair `(phi_i(E_1), phi_i(E_2))` is
  nonzero. The pushforwards have rank `2n` at stage `i + 1`.
- Start with `n = w <= sqrt(2) d_r <= d_(r+1)`. Ranks and `d_i` both double, so
  `n <= d_i` at every later stage.
- By induction `Delta != 0` at every stage `n >= r + 1`, which is part 1.

**Step 3: traces.** `phi_(r+1,n)(E_1)` has fibre rank `w 2^(n-r-1)` inside
`M_k(A_n)`, whose unit has fibre rank `k d_n = k d_r 2^(n-r)`. So its normalized
fibre trace is `w/(2 k d_r)` at every point, hence for every trace. The same
holds for `E_2`. This is part 2.

**Step 4: transport (part 3).**
- Let `y in E_2 M_k(A) E_1` be a contraction and `nu > 0`. Choose a contraction
  `x` at some stage `n` with `||x - y|| < nu`, and put
  `y_n = phi(E_2) x phi(E_1)`, a bundle map between the pushforwards. Since
  `y = E_2 y E_1`, `||y_n - y|| < nu`.
- By Step 2 there is `x_0` with `y_n(x_0) = 0`. Lemma 2 gives `tau_(x_0)` with
  stage-`n` measure `delta_(x_0)`, so
  `tau_(x_0)((E_1 - y_n* y_n)^2) = tr_(x_0)(E_1(x_0)) = w/(2 k d_r)`.
- The map `z -> tau((E_1 - z*z)^2)` is `4`-Lipschitz on contractions in norm.
  Letting `nu -> 0` gives `||E_1 - y*y||_(2,u)^2 >= w/(2 k d_r)`.
- If `V in M_k(A^u)` had `V*V = E_1` and `VV* = E_2`, compressing Kaplansky
  approximants of `V` would give contractions `y` in the corner with
  `||E_1 - y*y||_(2,u) <= 2 ||V - y||_(2,u) -> 0`, which is a contradiction.

**Step 5: part 4 in `B`.** Run Step 4 with Toms's Proposition 4 data, as in
Toms's Theorem 5 and in Step 3 of the artifact of
`toms-schubert-algebra-fails-o6-plus`.
- Put `F_i = psi_(m,n)(E_i)` and `G_i = E_(n,m) F_i E_(n,m)`, the top-branch
  pushforwards, and `y_n = F_2 x F_1`.
- Compress **on the left** by the top-branch projection `E_(n,m)`:
  `c = E_(n,m) y_n = G_2 x F_1`, as in Step 3 of the o6-plus artifact.
- Then `y_n* y_n - c* c = F_1 x* (F_2 - G_2) x F_1`. Its uniform 2-norm is at
  most `sqrt(eta_m)`, because `F_2 - G_2` is a projection of trace at most
  `eta_m` (Proposition 4(5)).
- A two-sided compression `G_2 x G_1` would cost up to `5 sqrt(eta_m)`, which
  only changes the constant.
- `G_2 x G_1` is a bundle map between the old topological pushforwards. By Step 2
  it vanishes at some `x_0 in X_n`. There the compression of `F_1 - c*c` to
  `G_1(x_0)` is the identity, so `Tr(A^2) >= Tr((P A P)^2)` gives
  `tr((F_1 - c*c)(x_0)^2) >= tr(G_1(x_0))`.
- The trace `tau_(x_0)` has `mu({x_0}) >= delta`, and the fibre fraction of
  `G_1` is at least `delta w/(2 k d_r)`, since `rank q_n / rank s_n >= delta`.
- So `tau((F_1 - c*c)^2) >= delta^2 w/(2 k d_r)`, and the triangle inequality
  gives the bound. Square.
- Reviewed by ex-verify2-analysis (PASS;
  `research/artifacts/ex-review2-analysis-2026-09-13-part2.md` §2.9), with this
  left-compression wording fix.
