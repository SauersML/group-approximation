---
rg: 2
id: fpbs-l2-gap-transfers-to-kesten-normal-gap-proof
kind: route
title: Følner compression on amenable kernels of the tower Gamma/N_j, window agreement with Gamma, and lower semicontinuity of p_c carry a fixed l2 bound to the relative susceptibility along N
target: fpbs-l2-gap-transfers-to-kesten-normal-gap
requires: [fpbs-high-girth-uniform-l2-patch, fpbs-l2-gap-class-closed-under-local-limits]
artifacts:
  - experiments/fpbs-kesten-transfer-2026-09-17/tree_calibration.py
  - experiments/fpbs-kesten-transfer-2026-09-17/output.txt
---

Complete proof. Written 2026-09-19 by `swarm-0917-w19-w19-bs-follow`
(reframing).

**What is used from the prerequisites.**
- `fpbs-l2-gap-class-closed-under-local-limits` (ESTABLISHED), part 2: `p_c` is
  lower semicontinuous under local convergence of infinite transitive graphs.
  The input there is the Duminil-Copin–Tassion finite-set criterion. The
  fuller continuity statement `fpbs-easo-hutchcroft-pc-locality` would also
  do, but only this direction is needed.
- `fpbs-high-girth-uniform-l2-patch` (ESTABLISHED), used only for Corollary A,
  exactly as stated there: girth hypothesis, spectral radius at most
  `1 - eta`, and the conclusion `||T_(p_c+delta(k,eta))|| <= M(eta)`.

Everything else is proved below. Notation is as in the target. All Cayley
graphs are for right multiplication, `x ~ xs`, so left multiplication acts by
label-preserving automorphisms, and `tau_q(gx,gy) = tau_q(x,y)`.

## Step 0. Elementary facts

**(F1) Monotonicity.** For nonnegative kernels, `0 <= K <= K'` entrywise
implies `||K||_(2->2) <= ||K'||_(2->2)`. The reason is that
`|<Kf,g>| <= <K|f|,|g|> <= <K'|f|,|g|>`. Since `tau_q` is nondecreasing in
`q`, so is `||T_q||`.

**(F2) Left continuity.** For `q_0 in (0,1]`, `chi^N_(q_0) <= liminf_(q ↑ q_0) chi^N_q`.
- `{e <-> x}` is the increasing union over `r` of the events
  `{e <-> x inside B_r(e)}`.
- Each of these events has a probability that is a polynomial in `q`.
- So `tau_q(e,x)` is a supremum of continuous functions, hence lower
  semicontinuous in `q`.
- A sum of nonnegative lower semicontinuous functions is lower
  semicontinuous.

**(F3) Quotients raise the spectral radius.** Let `H -> Q` be a surjection of
marked groups, and let `mu_H`, `mu_Q = pi_* mu_H` be symmetric and finitely
supported. The walk on `H` returns to `e` at time `n` only if its image
returns. So `mu_H^(*n)(e) <= mu_Q^(*n)(e)`. For symmetric `mu` on a group, the
norm satisfies `||lambda(mu)|| = limsup_n mu^(*2n)(e)^(1/(2n))` (Kesten).
Hence `||lambda_H(mu_H)|| <= ||lambda_Q(mu_Q)||`.

## Step 1. Følner compression on an amenable subgroup

**Lemma 1.** Let `H` be a finitely generated group with a Cayley graph `G_H`,
let `A <= H` be an amenable subgroup, and let `q` satisfy
`||T^(G_H)_q|| < infinity`. Then

```text
chi^A_q = sum_(a in A) tau_q(e,a) <= ||T^(G_H)_q||.
```

*Proof.* Put `phi(c) = tau_q(e,c) >= 0` for `c in A`. For `a, b in A`,
`tau_q(a,b) = tau_q(e, a^(-1) b) = phi(a^(-1) b)`, by left invariance.

The amenable group `A`, countable because `H` is, has a Følner sequence
`F_n` for right translation: for every `c in A`,
`|F_n c^(-1) ∩ F_n| / |F_n| -> 1`. (Inverting a left Følner sequence gives
one.)

For finite `C ⊂ A`, `f_n = 1_(F_n)` gives

```text
||T_q|| |F_n|  >=  <T_q f_n, f_n>  =  sum_(a,b in F_n) phi(a^(-1) b)
              =  sum_(c in A) phi(c) #{a in F_n : a c in F_n}
              >= sum_(c in C) phi(c) |F_n ∩ F_n c^(-1)|.
```

Divide by `|F_n|` and let `n -> infinity` to get
`sum_(c in C) phi(c) <= ||T_q||`. Taking the supremum over finite `C` gives
the claim. ∎

(Lemma 1 is the relative form of the amenable obstruction, part 4 of
`fpbs-l2-gap-class-closed-under-local-limits`. Here `H` itself is
nonamenable. Only the subgroup being summed over needs to be amenable.)

## Step 2. The tower

Let `N ◁ Gamma` be residually amenable in `Gamma`, with tower
`N_1 >= N_2 >= ...`. Put `H_j = Gamma/N_j`, marked by the images of the
`s_i`, with Cayley graph `G_j`, and `A_j = N/N_j ◁ H_j`, which is amenable.
Let `pi_j : Gamma -> H_j` be the quotient map.

**(T1) Membership of the kernel.** For every `j` and every `x in Gamma`,
`pi_j(x) in A_j` iff `x in N`. Indeed `pi_j(x) in N/N_j` iff
`x in N N_j = N`.

**(T2) Local convergence.** Fix `R`. The set `W_R` of elements of `Gamma` of
word length at most `2R + 2` is finite. Since `∩_j N_j = {e}` and the `N_j`
decrease, `W_R ∩ N_j = {e}` for all `j >= j_0(R)`.

For such `j`:
- `pi_j` is injective on the ball `B_(R+1)(e)` of `G`;
- a word of length at most `2R + 2` is trivial in `H_j` iff it is trivial in
  `Gamma`;
- so `pi_j` restricts to a label-preserving isomorphism
  `B_(R+1)^G(e) -> B_(R+1)^(G_j)(e)`, which includes the edges between
  vertices of the ball.

With `R = 1`, the generator images are nontrivial and distinct exactly when
they are in `Gamma`. So for `j >= j_0(1)` the simple Cayley graph of `H_j` has
the same edge labels as `G`. Its uniform label measure `mu_j` is `(pi_j)_* mu`,
and it pushes forward to `pi_* mu` on `Q`.

**(T3) Spectral control.** `H_j / A_j = Gamma/N = Q`. By (F3) applied to
`H_j -> Q`, for `j >= j_0(1)`,

```text
rho(G_j) = ||lambda_(H_j)(mu_j)|| <= ||lambda_Q(pi_* mu)|| = rho_Q.
```

So if `rho_Q <= 1 - eta`, every `G_j` with `j >= j_0(1)` has spectral radius
at most `1 - eta`. This is item 2 of the target.

**(T4) Relations pass down.** If `w = e` in `Gamma`, then `w = e` in every
`H_j`, since `H_j` is a quotient of `Gamma`.

## Step 3. Proof of the transfer lemma (item 1)

Assume `||T^(G_j)_(p_c(G_j)+delta)|| <= M` for all `j` in an infinite set `J`.

**(a) Pushing `q` under the threshold.** Let `q < p_c(G) + delta`.
- By (T2), `G_j -> G` locally, and all these graphs are transitive.
- Assume `N` has infinite index, so that `Q`, and hence every `G_j`, is
  infinite. If `N` has finite index, `N` is co-amenable and the statement is
  not needed; in any case the proof below uses only that the `G_j` are
  infinite.
- By lower semicontinuity of `p_c` (prerequisite),
  `liminf_j p_c(G_j) >= p_c(G) > q - delta`.
- So `q <= p_c(G_j) + delta` for all large `j`.
- By (F1), `||T^(G_j)_q|| <= M` for all large `j in J`.

**(b) Compression.** Lemma 1 with `H = H_j` and `A = A_j` gives
`chi^(A_j)_q(G_j) <= M` for all large `j in J`.

**(c) Windows.** For `R, R' >= 1` put

```text
chi^(N; R, R')_q(G) = sum_(x in N, |x| <= R) P_q(e <-> x inside B_(R')(e)),
```

where "inside `B_(R')(e)`" means through an open path that uses only edges
with both endpoints in `B_(R')^G(e)`. Define `chi^(A_j; R, R')_q(G_j)` in the
same way.

This quantity is determined by:
- the labelled ball `B_(max(R,R')+1)(e)`;
- which of its vertices lie in `N` (respectively `A_j`).

By (T2) and (T1), once `j >= j_0(max(R,R'))`, the ball isomorphism `pi_j`
carries one set of data to the other. So

```text
chi^(N; R, R')_q(G) = chi^(A_j; R, R')_q(G_j) <= chi^(A_j)_q(G_j) <= M
```

for all large `j in J`.

**(d) Limits.**
- Let `R' -> infinity`. The events `{e <-> x inside B_(R')}` increase to
  `{e <-> x}`, so by monotone convergence
  `sum_(x in N, |x| <= R) tau_q(e,x) <= M`.
- Let `R -> infinity` to get `chi^N_q(G) <= M`.

This holds for every `q < p_c(G) + delta`, and by (F2) also at
`q = p_c(G) + delta`. Hence `chi^N` is finite on `[0, p_c(G) + delta]`, and
`p_c(N;G) >= p_c(G) + delta`. ∎

(Throughout, `q` ranges over `[0,1]`. If `p_c(G) + delta > 1`, read the
right-hand endpoint as `1`.)

## Step 4. Corollary A

Let `Gamma` have no nontrivial reduced word of length less than `L = L(eta)`
equal to `e`, and let `rho_Q <= 1 - eta`.

Take `R` with `2R + 2 >= L`, and let `j >= max(j_0(R), j_0(1))`. By (T2), a
reduced word of length less than `L` is trivial in `H_j` iff it is trivial in
`Gamma`, so it is never trivial. By (T3), the simple Cayley graph `G_j` has
spectral radius at most `1 - eta`.

So `H_j` satisfies both hypotheses of `fpbs-high-girth-uniform-l2-patch`,
which gives `||T^(G_j)_(p_c(G_j)+delta(k,eta))|| <= M(eta)` for all large `j`.
Step 3 with `delta = eta/(4(2k-1))` and `M = 1 + 3/eta^2` then gives
Corollary A. ∎

## Step 5. Corollaries B and C

**Corollary B.** Assume the stated uniform bound, either on `X_(k,eta)` or on
one cylinder `Z_(k,eta,w)`.
- By (T3), `G_j` lies in `X_(k,eta)` for `j >= j_0(1)`.
- If `w = e` in `Gamma`, then by (T4) `G_j` also lies in `Z_(k,eta,w)`.
- The hypothesis therefore holds for all large `j`, and Step 3 applies.

**Corollary C** is the contrapositive of B:
- A pair with `p_c(N;G) = p_c(G)` violates the conclusion of B for every
  `delta > 0`.
- A family with margins tending to `0` violates it for every fixed `delta`.
- A family with `chi^N` unbounded at `p_c + delta` for every `delta` violates
  it for every fixed `(M, delta)`.

## Step 6. The examples of residually amenable subgroups

**(a) `N` residually solvable.** The derived subgroups `N^(j)` are
characteristic in `N`, and `N` is normal in `Gamma`, so each `N^(j)` is normal
in `Gamma`. Each `N/N^(j)` is solvable, hence amenable. Residual solvability
means that every `x != e` survives in some solvable quotient `N/K`. If that
quotient has derived length `l`, then `N^(l) <= K`, so `x` is not in
`N^(l)`. Hence `∩_j N^(j) = {e}`.

A subgroup of a residually solvable group is residually solvable, since
`N^(j) <= Gamma^(j)`. Free groups and surface groups are residually
nilpotent (Magnus; Baumslag, since surface groups are residually free),
hence residually solvable.

**(b) `N` finitely generated and residually finite.** A finitely generated
group has finitely many subgroups of each finite index. So
`N_j = ∩{K <= N : [N:K] <= j}` has finite index and is characteristic in `N`,
hence normal in `Gamma`. `N/N_j` is finite, hence amenable. Residual
finiteness gives `∩_j N_j = {e}`.

The surface-group illustration in the target uses only (a). It also uses the
standard fact that the Cayley graph of the standard presentation of
`pi_1(Sigma_g)` (`g >= 2`) is the 1-skeleton of the regular `{4g,4g}`
tessellation of the hyperbolic plane, whose shortest cycles are face
boundaries, of length `4g`. That illustration is not used anywhere else.

## Numerical calibration

`experiments/fpbs-kesten-transfer-2026-09-17/tree_calibration.py` checks
Corollary A on `F_k` independently of the proof. On the tree,
`tau_s(e,x) = s^|x|`, so `chi^N_s` is the cogrowth series. Grigorchuk's
formula and `p_n(e) <= rho_Q^n` then give

```text
chi^N_s <= (1-s^2)/(1+q s^2) / (1 - rho_Q (q+1) s/(1+q s^2)),
```

uniformly over all `Q` with `rho_Q <= 1 - eta`. This bound is below
`1 + 3/eta^2` at `s = 1/q + eta/(4q)`, with the worst ratio `0.23`. The exact
threshold `s_q(rho_Q)` exceeds `1/q + eta/(4q)` for every `k` and `eta` on the
grid. See `output.txt`.
