---
rg: 2
id: qudit-weyl-rounding-constant-linear-upper-bound-proof
kind: route
title: A commutator pair bound makes the good set commute below sigma_d/2, and the averaging proof then gives 2/sin(pi/d)+3
target: qudit-weyl-rounding-constant-linear-upper-bound
requires: []
artifacts:
  - research/artifacts/qudit-stabilizer-rounding-2026-09-12.md
  - experiments/qudit-stabilizer-rounding-constant-2026-09-17/README.md
---

Ordinary proof, unreviewed, not Lean-verified. Lane sw-078b, 2026-09-17. Steps (Q2)–(Q5)
are copied from `research/artifacts/qudit-stabilizer-rounding-2026-09-12.md` §2. Only
(Q1) and the threshold change.

## Setting

`d` is prime and `omega = e^(2 pi i/d)`. `K = sum_j |c_j| u_j` with `u_j = (c_j/|c_j|) g_j`,
where the `g_j` are Weyl operators. Any two `u_j` commute up to a power of `omega`.
`psi` is a top eigenvector of `K`, `delta_j = 1 - Re<psi|u_j|psi> in [0,2]`, and
`F = sum_j |c_j| delta_j = W - lambda_max(K)`.

## (P) Pair bound

**Lemma.** If `u, v` are unitaries with `uv = omega^t vu` and `t != 0 mod d`, then for
every unit `psi`, `delta_u + delta_v >= sigma_d := sin(pi/d)/(1 + 2 sin(pi/d))`.

*Proof.* For a unitary `u`, `||(u - I) psi||^2 = 2 delta_u`, and
`||(u^* - I) psi|| = ||u^*(I - u) psi|| = ||(u - I) psi||`.

(i) `uv - vu = (u-I)(v-I) - (v-I)(u-I)`, so
`<psi|[u,v]|psi> = <(u^*-I)psi|(v-I)psi> - <(v^*-I)psi|(u-I)psi>`. By Cauchy–Schwarz,
`|<[u,v]>| <= 2 sqrt(2delta_u) sqrt(2delta_v) = 4 sqrt(delta_u delta_v)`.

(ii) `vu = omega^(-t) uv`, so `[u,v] = (1 - omega^(-t)) uv` and
`|<[u,v]>| = |1 - omega^(-t)| |<uv>| >= 2 sin(pi/d) |<uv>|`.

(iii) `||(uv - I)psi|| <= ||u(v - I)psi|| + ||(u - I)psi|| = sqrt(2delta_v) + sqrt(2delta_u)`, so
`|<uv>| >= Re<uv> = 1 - ||(uv-I)psi||^2/2 >= 1 - (sqrt delta_u + sqrt delta_v)^2`.

Put `s = delta_u + delta_v`. Then `sqrt(delta_u delta_v) <= s/2` and
`(sqrt delta_u + sqrt delta_v)^2 <= 2s`. So (i)–(iii) give `2 sin(pi/d) (1 - 2s) <= 2s`, i.e.
`s >= sigma_d`. (If `1 - 2s < 0` then `s > 1/2 > sigma_d` anyway.) QED.

## (Q1') The good set commutes

Put `tau = sigma_d/2` and `G = {j : delta_j < tau}`. For `j, k in G`,
`delta_j + delta_k < sigma_d`, so by (P) `u_j` and `u_k` commute.

## (Q2)–(Q4), unchanged

- (Q2) Measure the commuting family `{u_k : k in G}` on `psi`, which gives a
  distribution `mu` on eigenvalue tuples `x`. Let `G*` be the indices `j` with `u_j` in
  `C^* <u_k : k in G>`. Each such `u_j` has a determined outcome `x_j`, with
  `E_mu x_j = <psi|u_j|psi>`. So some `x` of positive probability has
  `sum_(G*) |c_j| (1 - Re x_j) <= sum_(G*) |c_j| delta_j`.
- (Q3) The joint eigenspace `E_x` is nonzero. So `A_x = <x_k^(-1) u_k : k in G>` is abelian
  with no nontrivial scalar, and for prime `d` it extends to maximal stabilizer groups.
  Their states form a finite set `S_x` inside `E_x`, and each has `<u_j> = x_j` for
  `j in G*`. Let `nu` be uniform on `S_x`.
- (Q4) For `j not in G*`, `E_nu <phi|u_j|phi> = 0`. Either `u_j` fails to commute with
  some `h in A_x`, which forces `<phi|u_j|phi> = 0` on `S_x`, or `u_j` lies in
  `C(A_x) \ C^* A_x`. In the second case nondegeneracy of the symplectic form on
  `C(A_x)/A_x` gives a Weyl `R in C(A_x)` with `R u_j = omega^m u_j R`, `m != 0`. `R` permutes
  `S_x`, so the average is multiplied by `omega^(-m)` and must vanish.

## (Q5') Accounting

`E_nu <phi|K|phi> = sum_(G*) |c_j| Re x_j >= sum_(G*) |c_j| (1 - delta_j)`, hence

```text
lambda_max - E_nu <phi|K|phi>  <=  sum_(j not in G*) |c_j| max{0, 1 - delta_j}.
```

Since `G` is contained in `G*`, every `j not in G*` has `delta_j >= tau`, and then
`max{0, 1 - delta_j} <= ((1 - tau)/tau) delta_j`. So the loss is at most
`(1/tau - 1) F = (2/sigma_d - 1) F = (2/sin(pi/d) + 3) F`. Some member of `S_x` attains
at least the average. QED.

## Gaps and what is not claimed

- Not sharp. Numerically the exact pair gap `eps_d = min (delta_u + delta_v)` is
  `0.634, 0.517, 0.398, 0.266, 0.227` for `d = 3, 5, 7, 11, 13`, against `sigma_d = 0.464,
  0.370, 0.281, 0.182, 0.156` (`pair_gap.py`). With `eps_d` in place of `sigma_d` the same
  argument would give `2.15, 2.87, 4.02, 6.53, 7.80`. This is not proved, and it is
  still not sharp.
- `sigma_d ~ pi/d` and numerically `eps_d ~ 3/d`. So any argument that thresholds on a
  pair gap gives a leading term of about `2d/pi` or `2d/3`, while the Harper lower bound is
  `d/pi`. Closing that factor of 2 needs post-selection rather than a hard threshold; see
  `qudit-weyl-rounding-sharp-constant`.
- For `d = 2` this gives `5`. The sharp qubit constant `1/sqrt2` is
  `stabilizer-rounding-constant-is-one-over-sqrt2`.
