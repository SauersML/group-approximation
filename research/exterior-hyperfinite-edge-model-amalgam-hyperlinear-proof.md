---
rg: 2
id: exterior-hyperfinite-edge-model-amalgam-hyperlinear-proof
kind: route
title: Brown--Dykema--Jung supplies the ambient, the top alternation component supplies injectivity, Radulescu supplies hyperlinearity
target: exterior-hyperfinite-edge-model-amalgam-hyperlinear
requires:
  - abstract-unitary-embedding-upgrades-to-hyperlinear
---

**The ambient algebra.**  `L(K)` is Connes embeddable (`K` hyperlinear), so
`A_2 = P (x)-bar L(K)` is Connes embeddable, contains `P = P (x) 1`, and the
canonical conditional expectation `E_P(p (x) u_k) = p tau(u_k) = p delta_(k,e)`
is trace preserving.  Form the tracial amalgamated free product

```text
N = N_1 *_P A_2.
```

Both factors are Connes embeddable and the base `P` is hyperfinite (amenable,
Connes), so `N` is Connes embeddable by Brown--Dykema--Jung,
arXiv:math/0609080, Corollary 4.5 (the statement already used by
`amenable-edge-hnn-hyperlinear-permanence-proof`).

**The homomorphism.**  Define `Phi` on the amalgam `E = G *_Gamma (Gamma x K)`
by `Phi(g) = pi(g)` for `g in G` and `Phi(k) = 1 (x) u_k` for `k in K`.  The
two assignments agree on `Gamma`, and `Phi(K)` commutes with `Phi(Gamma) <= P`,
so `Phi` is a well-defined homomorphism into `U(N)`.

**Injectivity.**  Write `x^o = x - E_P(x)`.  For `k != e`, `Phi(k)^o = Phi(k)`
lies in `A_2 (-) P = P (x) (L(K) (-) C)`.  Let `L^2(N) = L^2(P) (+) (+)_w H_w`
be the free-product decomposition into alternating patterns `w` of the
`P`-centered pieces `N_1^o` and `A_2^o`, with `H_w` the relative tensor product
over `P` along `w` (Voiculescu's construction; the map from the relative
tensor product onto `H_w` is isometric).

Every nontrivial element of `E` has a reduced form
`g_0 k_1 g_1 k_2 ... k_m g_m` with `m >= 0`, `k_i in K - {e}`,
`g_1, ..., g_(m-1) in G - Gamma`, `g_0, g_m in G` (Britton).  If `m = 0` the
image is `pi(g_0) != 1` by injectivity of `pi`.  Suppose `m >= 1` and
`Phi(g_0 k_1 ... k_m g_m) = 1`; then

```text
Phi(k_1) pi(g_1) Phi(k_2) ... pi(g_(m-1)) Phi(k_m) = pi(g_0)^(-1) pi(g_m)^(-1) =: c in N_1.
```

Expand each interior `pi(g_i) = E_P(pi(g_i)) + pi(g_i)^o`.  The term with all
interior letters centered,

```text
Phi(k_1) pi(g_1)^o Phi(k_2) ... pi(g_(m-1))^o Phi(k_m),
```

is an alternating word of `2m - 1 >= 1` centered letters and lies in `H_w` for
the pattern `w = (A_2^o, N_1^o, ..., A_2^o)`.  Every other term replaces some
`pi(g_i)^o` by `E_P(pi(g_i)) in P`, which commutes with `Phi(k_i)` and
`Phi(k_(i+1))` and merges `Phi(k_i) Phi(k_(i+1))` into one element of `A_2`
(equal to `1 (x) u_(k_i k_(i+1))`, centered or in `P`), so after re-centering
it lies in patterns of strictly smaller alternation length.  The right-hand
side `c in N_1` lies in `L^2(P) (+) H_((N_1^o))`.  For `m >= 2` the top pattern
has length `>= 3`, and for `m = 1` it is `(A_2^o)`, orthogonal to
`L^2(P) (+) H_((N_1^o))`.  In all cases the top component must vanish, i.e.

```text
Phi(k_1) (x)_P pi(g_1)^o (x)_P ... (x)_P pi(g_(m-1))^o (x)_P Phi(k_m) = 0
```

in the relative tensor product.  Since `1 (x) u_k`, `k != e`, generates a copy
of `L^2(P)` as a `P`-bimodule inside `A_2^o` (`p (x) u_k <-> p`), this forces
`pi(g_1)^o (x)_P ... (x)_P pi(g_(m-1))^o = 0` (for `m = 1` it forces
`Phi(k_1) = 0`, absurd).

**The chain condition.**  The squared norm of `x_1 (x)_P ... (x)_P x_r` is
`tau(D_r)` where `D_1 = E_P(x_1^* x_1)` and `D_(j+1) = E_P(x_(j+1)^* D_j x_(j+1))`.
For `x = pi(g)^o` with `b = E_P(pi(g))`, `E_P(x^* x) = 1 - b^* b` (Kadison--
Schwarz terms cancel: `E_P(pi(g)^* b) = b^* b`).  Under (E2),
`1 - b^* b >= (1 - ||b||^2) 1 > 0`, so `D_1` is invertible and inductively
`D_(j+1) >= c_j E_P(x_(j+1)^* x_(j+1)) >= c_j (1 - ||b_(j+1)||^2) > 0`.  Hence
the relative tensor never vanishes, `Phi` is injective, and `E` embeds
abstractly in `U(N)` with `N` Connes embeddable.

**Hyperlinearity.**  `abstract-unitary-embedding-upgrades-to-hyperlinear`,
direction `(3) => (1)`, gives that `E` is hyperlinear; subgroups of hyperlinear
groups are hyperlinear, which covers the double (index two in the `K = C_2`
case).
