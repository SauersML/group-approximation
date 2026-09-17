---
rg: 2
id: hs-commutative-microstate-amplification-proof
kind: route
title: Rotate a swapped block microstate by the amplification commutant and pack the operator-norm ball
target: hs-commutative-microstate-bernoulli-entropy-is-base-blind
requires: []
artifacts:
  - research/artifacts/stability-approximation-transplant-to-bernoulli-rokhlin-2026-09-17.md
---

Notation as in the target. Write `d=d_j`, `m=m_j=2M`, `M_(dm)=M_d (x) M_2 (x) M_M`,
`sigma~ = sigma_j (x) 1_2 (x) 1_M`, and use normalized traces throughout. Fix `(F,delta)` with
`delta<1/(2q)`, a large `j`, and `p in Mic(sigma_j,F,delta)`.

## Step 1: swapped block microstate

Let `pi` swap two letters `a0 != a1`. The uniform product measure is invariant under
`w -> pi o w`, so `p^pi=(p_(pi a))_a` is again in `Mic(sigma_j,F,delta)`. Put

```text
P_a = p_a (x) e11 (x) 1_M + p_(pi a) (x) e22 (x) 1_M.
```

These are commuting projections summing to `1`. Their `sigma~`-translates commute blockwise,
and every moment is the average of the moments of `p` and `p^pi`. Hence
`P in Mic(sigma~,F,delta)`.

## Step 2: commutant rotations preserve microstates

For `X in M_M` set `H(X) = 1_d (x) (e12 (x) X + e21 (x) X^*)` and `W(X)=exp(iH(X))`.
`H(X)` is self-adjoint and commutes with `sigma~(G)`. So `Ad W(X)` fixes `sigma~(g)`,
preserves commutation, and preserves every moment. Therefore
`W(X)PW(X)^* in Mic(sigma~,F,delta)`.

## Step 3: exact linear term

With `p0=p_(a0)` and `p1=p_(a1)`,

```text
[H(X),P_(a0)] = (p1-p0) (x) e12 (x) X + (p0-p1) (x) e21 (x) X^*.
```

Because `(p1-p0)^2=p0+p1`,

```text
||[H(X),P_(a0)]||_2 = s ||X||_(2,M),    s^2 = tau_d(p0+p1).
```

The `F={e}` moments give `s^2 >= 2/q-2delta >= 1/q`, and `s<=1`.

## Step 4: remainder is Lipschitz-small

Write `e^(iH)Pe^(-iH) = P+i[H,P]+R(H)` with `R(H) = sum_(k>=2) i^k ad_H^k(P)/k!`.
Suppose `||H||_inf, ||H'||_inf <= r` and put `Delta=H-H'`. Telescoping gives `k` terms. Using
`||ad_(H')^i(P)||_inf <= (2r)^i`, `||[Delta,Y]||_2 <= 2||Y||_inf||Delta||_2` and
`||[H,Y]||_2 <= 2r||Y||_2`,

```text
||R(H)-R(H')||_2 <= sum_(k>=2) 2k(2r)^(k-1)/k! ||Delta||_2 = 2(e^(2r)-1)||Delta||_2.
```

With `r=s/10` this is `< 0.49 s ||Delta||_2`, and `||Delta||_2 = ||X-X'||_(2,M)`. Therefore

```text
||W(X)P_(a0)W(X)^* - W(X')P_(a0)W(X')^*||_2 >= (s/2)||X-X'||_(2,M)
    for ||X||_inf, ||X'||_inf <= s/10.
```

## Step 5: packing

Let `Z` be complex Ginibre in `M_M` with entry variance `1/M`.

**Norm bound.** Take a `1/4`-net `N` of the unit sphere of `C^M` with `|N| <= 81^M`. Then
`||Z||_inf <= 2max_(u,v in N)|<Zu,v>|`, and each `<Zu,v>` is complex Gaussian of variance
`1/M`. The union bound gives `P(||Z||_inf>12) <= 81^(2M)e^(-36M) <= 1/2`.

**Small balls.** The Ginibre density is at most `(M/pi)^(M^2)`. A normalized-HS ball of radius
`eta` is a Euclidean ball of radius `sqrt(M)eta` in real dimension `2M^2`. So its mass is at most

```text
(M^2 eta^2)^(M^2)/(M^2)! <= (e eta^2)^(M^2).
```

**Packing.** A maximal `1/4`-separated set `S` inside `{||Z||_inf<=12}` covers that set with
`1/4`-balls, so `|S| >= (1/2)(16/e)^(M^2)`. Rescaling by `r/12` gives `|S|` matrices `X` with
`||X||_inf <= r` and pairwise distances `||X-X'||_2 >= r/48`.

## Step 6: count

By Steps 2 and 4, the microstates `W(X)PW(X)^*` are pairwise `rho`-separated by at least
`(s/2)(r/48) = s^2/960 >= 1/(960q)`. For `eps<1/(2000q)` each `eps`-ball contains at most one
of them. Hence

```text
N_eps(Mic(sigma~,F,delta),rho) >= (1/2)(16/e)^(M^2),
(dm)^(-beta) log N_eps >= (m^(2-beta)/(4d^beta)) log(16/e) - (dm)^(-beta) log 2.
```

The right side tends to `+infinity` by the choice of `m_j`. This holds for every
`(F,delta)` with `delta<1/(2q)`, so the infimum over `(F,delta)` of the limsup is
`+infinity` for every small `eps`. This proves `(HSB1)` and `(HSB2)`.

## Step 7: sofic amplification and the multinomial bound

If `sigma_j` are permutation matrices, `sigma_j (x) 1_(m_j)` are permutation matrices with
the same multiplicativity defects and normalized traces, so they form a sofic
approximation. Along it, for `G=Z` with `h^Rok(A^Z)=log q`, the count is `+infinity`.
Hence the transplanted count does not satisfy `h <= H(P)` for generating partitions.

The proof used only three properties of `Mic`, so the conclusion holds for every
microstate space defined by joint `*`-moment conditions on `(sigma,p)`:

- conjugation by the commutant preserves membership;
- block averaging preserves membership;
- swap invariance of the uniform base.
