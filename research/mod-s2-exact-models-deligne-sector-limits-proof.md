---
rg: 2
id: mod-s2-exact-models-deligne-sector-limits-proof
kind: route
title: Pass Torelli almost-scalarity to the limit trace, descend it to the omega fibre, and round flexible models back to exact ones
target: mod-s2-exact-models-are-fd-character-limits-of-deligne-sectors
requires:
  - deligne-torelli-character-counts-separating-twists
  - deligne-triple-cover-is-a-torelli-scalar-quotient-of-mod-s2
  - deligne-maslov-sector-traces-are-central-regular
artifacts:
  - research/artifacts/hl-nh-deligne-extension-2026-09-14.md
---

Notation as in the target. Inputs:
- **[TSQ]** `deligne-triple-cover-is-a-torelli-scalar-quotient-of-mod-s2`, items (TS1), (TS2);
- **[ST]** `deligne-torelli-character-counts-separating-twists`, items (ST1), (ST2), (ST4);
- **[CR]** `deligne-maslov-sector-traces-are-central-regular`: every tracial state of `A_omega` is a
  convex combination of `tau_(eta_+)` and `tau_(eta_-)`.

Standard facts used, not re-pinned:
- (F1) for unitaries `X, Y` and a matrix `A`, `||XAY||_2 = ||A||_2` and `|tr_d(A)| <= ||A||_2`;
- (F2) pointwise convergence on `M` of states of `C*(M)` is weak*-convergence, and the pointwise limit of
  normalized characters is a tracial state;
- (F3) in the GNS representation of a tracial state, the trace vector is separating for the generated von
  Neumann algebra.

## Step 0: word length of Torelli elements

By (ST1), every `k in K` has expressions `k = prod_j g_j t_s^(e_j) g_j^(-1)`. Let `l_T(k)` be the least
`sum_j |e_j|`, and `c(k) = epsilon sum_j e_j` by (ST2). Replacing factors one at a time, and using (F1)
together with `||t^(-1) - omega^(-epsilon)||_2 = ||t - omega^epsilon||_2` for a unitary `t`, gives for
every representation `rho`

```text
|| rho(k) - omega^(c(k)) I ||_2  <=  l_T(k) delta(rho).                  (W)
```

## Step 1: (E1), forward direction

Let `delta(rho_n) -> 0` and let `tau` be a pointwise cluster point of `chi_n = tr o rho_n`. For `k in K`
and `m in M`, by (F1) and (W):

```text
| chi_n(k m) - omega^(c(k)) chi_n(m) | <= ||rho_n(k) - omega^(c(k))||_2 <= l_T(k) delta(rho_n) -> 0.
```

So `tau(k m) = omega^(c(k)) tau(m)`. In particular `tau((k - omega^(c(k)))*(k - omega^(c(k)))) =
2 - 2 Re(omega^(-c(k)) tau(k)) = 0`, so `pi_tau(k) xi_tau = omega^(c(k)) xi_tau`. By (F3),
`pi_tau(k) = omega^(c(k))`. Then `(m, j) -> omega^j pi_tau(m)` is trivial on
`L_c = {(k, -c(k))}`, so by (TS1) it defines a representation of `E_3` with `z -> omega`. Its vector
state is a tracial state `tau~` of `A_omega` with `tau = tau~ o q`. Hence `tau in T_omega(M)`.

## Step 2: (E1), converse, and the two sector traces

Let `tau = tau~ o q in T_omega(M)` be a pointwise limit of `chi_n = tr o rho_n`. Since `q(t_s) = z^epsilon`,
`tau(t_s) = omega^epsilon`, so

```text
delta(rho_n)^2 = 2 - 2 Re( omega^(-epsilon) chi_n(t_s) )  ->  2 - 2 Re(omega^(-epsilon) omega^epsilon) = 0.
```

So `inf delta = 0` iff `T_omega(M)` meets `cl Char_fd(M)`, by compactness of the state space.

**The two sector traces.** By [CR], `tau = t tau'_+ + (1-t) tau'_-`. Let `iota` be the hyperelliptic
involution. It is central in `M`, `iota^2 = 1`, and it maps to `-I`. So `q(iota)` is the central element of
order two in `Z(E_3)`, with `eta_(+-)(q(iota)) = +-1` for the labelling of [CR].

`rho_n(iota)` is a central involution. Cut `rho_n` by `P_(+-) = (1 +- rho_n(iota))/2` into subrepresentations
`rho_n^(+-)` of dimension fractions `(1 +- chi_n(iota))/2 -> t` and `1 - t`. If `t > 0`, then
`delta(rho_n^+)^2 <= delta(rho_n)^2 d_n / d_n^+ -> 0`, by the orthogonal splitting of the Frobenius norm.
So by Step 1 every cluster point of `tr o rho_n^+` lies in `T_omega(M)` and takes the value `+1` on
`iota`. By [CR] it is `tau'_+`. If `t = 0`, argue with `rho_n^-`. The reverse implication is trivial.
This proves (E1).

## Step 3: (E2)

Exact representations have zero relator defect. If `delta(rho_n) -> 0`, then (ST4), with the primitive
cube root `zeta = omega^epsilon`, says that `E_3` is hyperlinear. The remark on
`deligne-central-mark-hs-collapse` is its definition, and the genus statement is the direction of
`deligne-cover-hyperlinearity-is-monotone-in-genus`.

## Step 4: (E3)

**Definition used** (flexible HS stability, as used on main; not re-pinned here). Let `M = <S | R>` be finitely
presented. For every `e > 0` there is `d_0 > 0` with the following property. Every tuple `phi : S -> U(d)`
with `max_r ||phi(r) - I||_2 <= d_0` admits a representation `rho : M -> U(D)` with
`d <= D <= (1+e) d` and `max_s ||phi(s) - P rho(s) P||_(2,d) <= e`. Here `P` is the compression to the
first `d` coordinates, and `||.||_(2,d)` is normalized by `d`.

**Leaks.** Normalize by `d`. Because `phi(s)` is unitary, `||P rho(s) P||_(2,d) >= 1 - e`. The identities
`tr_d(P rho(s)* rho(s) P) = 1 = tr_d(P rho(s) rho(s)* P)` give
`||(1-P) rho(s) P||_(2,d)^2 <= 2e` and `||P rho(s) (1-P)||_(2,d)^2 <= 2e`. Use
`||X Y||_2 <= ||X||_2 ||Y||_op` and `||X Y||_2 <= ||X||_op ||Y||_2`, with `||P rho P||_op <= 1`.
- **Leaks.** From `(1-P) rho(uv) P = (1-P) rho(u) P rho(v) P + (1-P) rho(u) (1-P) rho(v) P`, the leak of a
  word of length `L` is at most `L sqrt(2e)`, on either side.
- **Errors.** From `phi(uv) - P rho(uv) P = (phi(u) - P rho(u) P) phi(v) + P rho(u) P (phi(v) - P rho(v) P)
  - P rho(u) (1-P) rho(v) P`, the error `err(uv)` is at most `err(u) + err(v) + leak(v)`. So a word `w`
  of length `L` satisfies

```text
|| phi(w) - P rho(w) P ||_(2,d)  <=  L e + L^2 sqrt(2e).
```

**Rounding.** Let `E_3` be hyperlinear. By (ST4) there are tuples `phi_n` with relator defects `-> 0` and
`||phi_n(t_s) - zeta I||_2 -> 0` for a primitive cube root `zeta`. If `zeta = omega^(-epsilon)`, replace
`phi_n` by its entrywise conjugate, which changes no defect. Apply the definition with `e_n -> 0` to get
`rho_n` on `C^(D_n)`. Let `w` be a word of length `L` for `t_s`. Split the Frobenius norm of
`X = rho_n(t_s) - omega^epsilon I_D` into its four blocks:

```text
D delta(rho_n)^2  <=  d ||P X P||_(2,d)^2 + 2 d (L sqrt(2 e_n))^2 + 4 (D - d).
```

Dividing by `D` and using `||P X P||_(2,d) <= L e_n + L^2 sqrt(2 e_n) + ||phi_n(t_s) - omega^epsilon||_2`
gives `delta(rho_n) -> 0`.

## Step 5: (E4)

Let `rho` factor through `M/N`, and take `k = prod_j g_j t_s^(e_j) g_j^(-1) in N` with
`sum_j |e_j| = l(N)` and `sum_j e_j != 0 mod 3`. Such `k` exist:
- (TS2) gives `k in K cap N` with `c(k) != 0`;
- (ST2) writes `k` in this form with `c(k) = epsilon sum_j e_j`.

Then `rho(k) = I`, while (W) gives `||rho(k) - omega^(c(k)) I||_2 <= l(N) delta(rho)`. The left side is
`|1 - omega^(+-1)| = sqrt(3)`.
