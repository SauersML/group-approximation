---
rg: 2
id: fpbs-stationary-half-tilt-lamplighter-proof
kind: route
title: Proof that the limiting-lamp law of a drifted lamplighter walk is a stationary boundary with linear mutual information and positive Radon-Nikodym growth on an amenable Cayley graph, where item 6 of the tilt claim pins the half tilt at p_c, and that the half tilt never exceeds exp(-h/2)
target: fpbs-stationary-boundary-half-tilt-dies-on-amenable-lamplighter
requires:
  - fpbs-boundary-tilted-susceptibility-kernel
  - fpbs-worst-pair-collapse-realized-on-amenable-growth
---

Notation is that of the target. Logarithms are natural. `H(.)` is Shannon
entropy and `I(.;.)` mutual information. `Lambda` is countable, so every
identity below that holds `nu`-a.e. for each fixed tuple of group elements
holds simultaneously for all tuples on one conull set.

## Step 0: the walk and its limiting lamps

Write the `k`-th increment as `Y_k = a^(b_k) t^(e_k) a^(b'_k)`. Then
`z_k = z_(k-1) + e_k`, and `f_k = f_(k-1) + b_k 1_(z_(k-1)) + b'_k 1_(z_k)`.
So step `k` changes only the lamps at `z_(k-1)` and `z_k`.

The base walk `z_k` is a nearest-neighbour walk on `Z` with drift `1/2`, so
`z_k -> +infinity` a.s. and every site is visited finitely often. Hence every
lamp changes finitely often, and `Phi = lim f_k` exists a.s. in the product
topology.

**Shift structure.** For fixed `n`, put `W_k = X_n^(-1) X_(n+k)`. Then
`(W_k)` is a `mu`-walk independent of `X_n`. Its limiting lamps `Phi^(n)` have
law `nu` and are independent of `X_n`. Since
`X_(n+k) = X_n W_k`, the lamps of `X_(n+k)` are `f_n + tau_(z_n)(lamps of W_k)`,
so

```text
Phi = X_n · Phi^(n).                                                   (0.1)
```

## Step 1: stationarity, quasi-invariance, the conditional law

By (0.1), for `g` in `Lambda` and Borel `A`,

```text
P(X_n = g, Phi in A) = mu^(*n)(g) P(g·Phi^(n) in A) = mu^(*n)(g) (g_* nu)(A).   (1.1)
```

Summing over `g` gives `nu = sum_g mu^(*n)(g) g_* nu`. At `n = 1` this is
stationarity.

**Quasi-invariance.** Stationarity gives `nu >= mu^(*n)(g) g_* nu`, so
`g_* nu << nu` whenever `mu^(*n)(g) > 0` for some `n`.
- `mu(t) = (1/4)(3/4) = 3/16` and `mu(t^(-1)) = 1/16`.
- `mu^(*2)(a) >= 1/256`, since `a = (a^0 t a^0)(a^0 t^(-1) a^1)` has
  probability `(3/16)(1/16)`.

So `s_* nu << nu` for `s in {a, t, t^(-1)}`, and trivially for `u^(±1)`.
Composition gives `g_* nu << nu` for all `g`. Applied to `g^(-1)` this gives
`nu << g_* nu`, since `(g^(-1))_* nu << nu` is equivalent to it.

**Conditional law.** By (1.1) and `(g_* nu)(A) = int_A Delta_zeta(o,g) d nu(zeta)`,
`P(X_n = g | Phi = zeta) = mu^(*n)(g) Delta_zeta(o,g)` for `nu`-a.e. `zeta`.
This is item 1.

**Upper bound.** From `nu >= mu^(*k)(s) s_* nu`:
`Delta_eta(o,s) <= C := 256` for `nu`-a.e. `eta` and each `s in S`
(`Delta ≡ 1` for `u^(±1)`). The cocycle identities of item 1 of the tilt claim
give, for a word `g = s_1 ... s_m`,

```text
Delta_zeta(o,g) = prod_(i=1)^m Delta_((s_1...s_(i-1))^(-1) zeta)(o, s_i).
```

The exceptional sets are null, and so are their translates by quasi-invariance.
So `Delta_zeta(o,g) <= C^(|g|)` for all `g`, `nu`-a.e.       (1.2)

## Step 2: linear mutual information

`X_n` takes finitely many values, so `I(X_n;Phi) = H(X_n) - H(X_n|Phi)`.

**Lower bound on `H(X_n)`.** Let `P` be the base path `(z_k)_(k>=0)`, which
is independent of all the bits. Conditioning cannot increase entropy, so
`H(X_n) >= H(X_n | P) = H(f_n | P)`, since `z_n` is a function of `P`. Given
`P`, each bit `b_k, b'_k` with `k <= n` is applied at exactly one site, and
every site of `R_n = {z_0, ..., z_n}` receives at least one of them (`n >= 1`).
So given `P`, `f_n` is uniform on the configurations supported on `R_n`, and
`H(f_n | P) = (log 2) E|R_n|`. Since `|R_n| >= z_n - z_0 + 1` and
`E z_n = n/2`,

```text
H(X_n) >= (log 2)(n/2 + 1).                                           (2.1)
```

**Upper bound on `H(X_n | Phi)`.** Put `m_n = min_(k>=n) z_k`,
`M_n = max_(k<=n) z_k`, `A = z_n - m_n >= 0` and `B = M_n - z_n >= 0`.

- A lamp at `y < m_n` is not changed after time `n`, by Step 0, so
  `f_n(y) = Phi(y)`.
- A lamp at `y > M_n` has never been changed, so `f_n(y) = 0`.

Hence `X_n` is a function of `(Phi, z_n, A, B, f_n restricted to [m_n, M_n])`,
and the last block has at most `A + B + 1` bits. So

```text
H(X_n | Phi) <= H(z_n) + H(A) + H(B) + (log 2) E(A + B + 1).           (2.2)
```

- `H(z_n) <= log(2n+1)`, because `|z_n| <= n`.
- `A` has the law of `-min_(k>=0) S_k` for a walk `S` with the same steps
  started at `0` (Markov property at time `n`). Gambler's ruin with
  `p = 3/4`, `q = 1/4` gives `P(A >= j) = (q/p)^j = 3^(-j)`, so `E A = 1/2`.
- `B = max_(0<=i<=n) (-(z_n - z_(n-i)))`, and `z_n - z_(n-i)` is a sum of `i`
  i.i.d. steps. So `B` has the law of `max_(i<=n)(-S_i)`, which is
  stochastically dominated by `A`. So `E B <= 1/2`.
- An `N`-valued variable with mean at most `m` has entropy at most
  `(m+1) log(m+1) - m log m`, the geometric maximum, which is increasing in
  `m`. At `m = 1/2` this is `(3/2) log(3/2) + (1/2) log 2 < 0.9548`. So
  `H(A), H(B) < 0.9548`.

Therefore `H(X_n | Phi) <= log(2n+1) + 1.9096 + 2 log 2 < log(2n+1) + 3.3`.
Together with (2.1) this is item 2.

## Step 3: positive Radon–Nikodym growth

Let `q_zeta(g) = mu^(*n)(g) Delta_zeta(o,g)`, the conditional law of Step 1.
Then, for `nu`-a.e. `zeta`, `q_zeta` is a probability on `supp mu^(*n)`, and

```text
I(X_n;Phi) = int sum_g q_zeta(g) log( q_zeta(g) / mu^(*n)(g) ) d nu(zeta)
           = int sum_g q_zeta(g) log Delta_zeta(o,g) d nu(zeta)
          <= int log max_(g in supp mu^(*n)) Delta_zeta(o,g) d nu(zeta).
```

Each increment has word length at most `3`, so `supp mu^(*n) ⊆ B_(3n)`. Put

```text
V_n(zeta) = (1/(3n)) log max_(g in B_(3n)) Delta_zeta(o,g).
```

Then `V_n >= 0` (take `g = o`) and `V_n <= log C` by (1.2). By item 2,
`int V_n d nu >= I(X_n;Phi)/(3n) -> (log 2)/6`. Reverse Fatou, valid since
`V_n <= log C`, gives `int limsup_n V_n d nu >= (log 2)/6`. As
`0 <= limsup V_n <= log C`,

```text
nu(limsup_n V_n >= (log 2)/12) >= ((log 2)/12) / log C > 0.
```

Finally `h_nu(zeta) >= limsup_n V_n(zeta)`, because `h_nu` is a `limsup` over
all radii and `V_n` looks at the radii `3n`. This is item 3.

## Step 4: the kill

- **Amenable.** `L` is metabelian and `Lambda = L x Z`.
- **Growth.** The `2^n` words `a^(c_0) t a^(c_1) t ... a^(c_(n-1)) t`, with
  `c_i in {0,1}`, have length at most `2n` and pairwise different lamps, so
  `|B_(2n)| >= 2^n` and `gr >= sqrt 2`.
- **`p_c < 1`.** `<t,u> ≅ Z^2`, and its Cayley graph on `{t,u}` is a subgraph
  of `H`, so `p_c(H) <= 1/2`.

So `H` satisfies the hypotheses of `fpbs-worst-pair-collapse-realized-on-amenable-growth`,
and by item 3 `nu(h_nu > 0) > 0`. The general amenable statement proved under
item 6 of `fpbs-boundary-tilted-susceptibility-kernel` (its proof, "General
amenable statement") gives `p^nu_t(H) = p_c(H)`. Explicitly: for `p > p_c(H)`,
`kappa_p(n) >= theta(p)^2` by item 1 of the collapse claim, while finiteness
of `chi^nu_(1/2)(p)` would force `kappa_p(n) <= S e^(-(h - epsilon) n/2)` for
infinitely many `n` (the display in item 3 of the tilt claim, which uses no
nonamenability). This is item 4.

**Why the class dies.** Every input listed in (c) of the target holds for
`(H,Z,nu)`, by Steps 1–3. Inputs (a) and (b) hold as in the tilt claim's
class kill, except the pointwise uniform growth bound, which is not claimed
here and is not in the killed class. Those inputs use only amenability of
the acting group and quasi-invariance. The conclusion `chi^nu_(1/2)(p) < infinity` for some
`p > p_c` fails. So no argument using only (a), (b) and (c) is valid.

## Step 5: the universal ceiling

Let `G = Cay(Gamma,S)` be any Cayley graph, and `nu` any quasi-invariant
probability with `nu(h_nu >= h) > 0`. Let `p < p^nu_t`, so
`chi^nu_(1/2)(p) < infinity`. The display in item 3 of the proof of
`fpbs-boundary-tilted-susceptibility-kernel` uses no nonamenability. For every
`epsilon in (0,h)` it gives infinitely many `n` with

```text
kappa_p(n) <= S(zeta) e^(-(h - epsilon) n/2),     S(zeta) < infinity.
```

Every `v in B_n` is joined to `o` by a path of at most `n` edges. That path
is open with probability at least `p^n`, so `kappa_p(n) >= p^n`. Hence
`n log p <= log S(zeta) - (h - epsilon) n/2` for infinitely many `n`, and
`log p <= -(h - epsilon)/2`. Letting `epsilon -> 0` and `p -> p^nu_t` gives
`p^nu_t <= exp(-h/2)`.

**Sharpness on trees.** For `T_d` with the visual measure, item 5 of the tilt
claim gives `h_nu = log(d-1)` everywhere and `p^nu_t = (d-1)^(-1/2)`, which is
`exp(-h/2)`. This is item 5.

## Step 6: consequences

- *[BT] needs small growth.* For every `h < h^*(nu)`, Step 5 gives
  `p^nu_t <= exp(-h/2)`, so `p^nu_t <= exp(-h^*(nu)/2)`. If `nu` witnesses
  [BT], then `p_c < p^nu_t`, so `h^*(nu) < 2 log(1/p_c)`.
- *l2 threshold.* If `pi_nu ≺ lambda_Gamma`, item 4 of the tilt claim gives
  `p_(2->2) <= p^nu_t`. Combine with the previous bullet.
- *Stationary boundaries.* Suppose `nu` is `mu`-stationary with
  `supp mu ⊆ B_L` generating `Gamma` as a semigroup, and the conditional law
  `P(X_n = g | Phi = zeta) = mu^(*n)(g) Delta_zeta(o,g)` holds. Steps 1 and 3
  apply verbatim, with `3` replaced by `L`, and with `C` replaced by
  `max_s 1/mu^(*k_s)(s)`, where `k_s` is some `k` with `mu^(*k)(s) > 0`.
  - They give `0 <= V_n <= log C`, `int V_n d nu >= I(X_n;Phi)/(L n)`, and
    `h_nu >= limsup V_n`.
  - Reverse Fatou gives `E_nu h_nu >= limsup_n I(X_n;Phi)/(L n) =: i`.
  - `h_nu <= log C` a.e. by (1.2). So `E_nu h_nu >= i` forces
    `nu(h_nu >= i) > 0`, that is `h^*(nu) >= i`.
  - Step 5 then gives `p^nu_t <= exp(-i/2)`.

This is item 6.
