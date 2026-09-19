---
rg: 2
id: bs12-sharp-pair-twist-holonomy-proof
kind: route
title: A twist u with C u C^* = u^2 commutes with C^L, so C^L must have the same diagonal entry at f_0 and at u f_0, while A_s^L has e^(2isL) and hol_p(s) there
target: bs12-sharp-pair-twist-coherent-corrections-are-bounded-below
requires: []
---

This is a lane proof (swarm-0917-w15, 2026-09-19), not reviewed. It is self-contained. The notation
is that of the target. The numerical checks are in
`experiments/bs12-twist-holonomy-2026-09-17/twist_holonomy.py`, with output in `output.txt`.

**Step 0 (Fourier facts).** Take `f_m = N^(-1/2) sum_j w^(-jm) e_j`.
- `V f_m = sum_j w^(-jm) e_(j+1) / sqrt N = w^m f_m`.
- `D f_m = f_(m-1)`.
- `W f_m = sum_j w^(-jm) e_(j/2) / sqrt N = sum_k w^(-2km) e_k / sqrt N = f_(2m)`.
- `exp(is(V+V^*)) f_m = phi(m) f_m`.

So `A_s f_m = phi(m) f_(2m)`, and hence

```text
A_s^L f_0 = phi(0)^L f_0 = e^(2isL) f_0,
A_s^L f_(-N/p) = prod_(k<L) phi(-2^k N/p) f_(-N/p) = hol_p(s) f_(-N/p),
```

because `2^L = 1 mod p` and `cos` is even.

**Step 1 (the twist commutes with `C^L`).** From `C u C^* = u^2` we get
`C^k u C^(-k) = u^(2^k)` by induction. Since `u^p = 1` and `2^L = 1 mod p`, this gives
`C^L u C^(-L) = u`.

**Step 2 (equal diagonal entries).** Put `xi = f_0`, `eta = f_(-N/p)`, and `xi' = e^(-i theta) u xi`,
where `theta` attains `kappa = kappa(u) = ||xi' - eta||`. By Step 1,
`<xi', C^L xi'> = <u xi, C^L u xi> = <xi, u^* C^L u xi> = <xi, C^L xi>`.
Since `||C^L|| = 1`, we have `|<xi', C^L xi'> - <eta, C^L eta>| <= 2 ||xi' - eta|| = 2 kappa`.

**Step 3 (compare with `A_s`).** Put `eps = ||C - A_s||`. Telescoping gives
`||C^L - A_s^L|| <= L eps`. By Step 0,
`|<xi, C^L xi> - e^(2isL)| <= L eps` and `|<eta, C^L eta> - hol_p(s)| <= L eps`. With Step 2,

```text
|e^(2isL) - hol_p(s)| <= 2 L eps + 2 kappa.
```

For `p = 3`: `L = 2` and `hol_3 = e^(-2is)`, so the left side is `|e^(6is) - 1| = 2|sin 3s|`.
For `p = 7`: `L = 3` and `hol_7 = e^(-is)`, so the left side is `2|sin(7s/2)|`. This proves (A) and (D).

**Step 4 (sources of twists; proves (B)).**
- If `C Z C^* = Z^2`, then `C Z^n C^* = Z^(2n)`. So `u = Z^(N/p)` satisfies `C u C^* = u^2`, and
  if `Z^N = 1` it also satisfies `u^p = 1`.
- Now let `Z = G D G^*` with `G = R M`, where `M = h(V)` is diagonal in the basis `f_m`. Then
  `Z^N = G D^N G^* = 1` and `u = G D^(N/p) G^*`.
- Write `r = ||R - 1||`. We have `M^* f_0 = conj(h(0)) f_0`, `D^(N/p) f_0 = f_(-N/p)` and
  `M f_(-N/p) = h(-N/p) f_(-N/p)`.
- Hence `u f_0 = conj(h(0)) h(-N/p) R f_(-N/p) + R M D^(N/p) M^* (R^* - 1) f_0`, which is within
  `r + r` of a unimodular multiple of `f_(-N/p)`. So `kappa(u) <= 2r`.
- For `R = 1`, `kappa = 0` and (A) gives `||C - A_s|| >= |sin 3s|/2`. For general `R` it gives
  `4 eps + 4 r >= 2|sin 3s|`.

None of this uses a bound on `||Z - D||` or any structure of `C` beyond `C Z C^* = Z^2`.

**Step 5 (sharpness, computed; proves (C)).** Take `C = c M W M^*` and `Z = M D M^*` with
`M = h(V)`, `h = e^(i alpha)`, `c = e^(ia)`. Then:

- `C f_m = c h(2m) conj(h(m)) f_(2m)`, so `||C - A_s|| = max_m |e^(i(a + alpha(2m) - alpha(m))) - phi(m)|`.
- `Z f_m = conj(h(m)) h(m-1) f_(m-1)`, so `||Z - D|| = max_m |e^(i(alpha(m-1) - alpha(m))) - 1|`.

The phase LP (no `2 pi` jumps) returns the value `1.5 s` for all `N <= 729` tested. The matrices
built from it are exact pairs, which the script checks. Their distances are `2 sin(0.75 s)`
for both generators.

Since `2 sin(0.75 s) = 1.5 s + O(s^3)` and `|sin 3s|/2 = 1.5 s + O(s^3)`, the small-`s` constant
`3/2` of the Fourier-gauge class is attained. This part is a computation, not a proof, for `N`
outside the tested range.
