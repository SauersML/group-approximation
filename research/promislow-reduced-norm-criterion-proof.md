---
rg: 2
id: promislow-reduced-norm-criterion-proof
kind: route
title: Right-multiplication matrices, semilinear conjugation and Cayley-Hamilton give the reduced-norm unit criterion on P
target: promislow-group-ring-units-are-constant-reduced-norm
requires: []
---

Notation as in the target.

**Model.** Use Gardam's faithful affine model (arXiv:2312.05240, proof of
Theorem A):

- `a: v -> diag(1,-1,-1) v + (1,1,0)`;
- `b: v -> diag(-1,1,-1) v + (0,1,1)`.

In this model:
- both relators hold;
- `x`, `y`, `z` are the translations by `(2,0,0)`, `(0,2,0)`, `(0,0,-2)`;
- conjugation by `a`, `b`, `ab` changes the signs of translation vectors by
  `diag(1,-1,-1)`, `diag(-1,1,-1)`, `diag(-1,-1,1)`, which gives the `K4`-action
  of the target;
- `L = <x, y, z>` is free abelian of rank 3 and index 4, with coset
  representatives `1, a, b, ab`.

All of this is checked by assertions at the top of the script.

**Step 1: matrices.** For representatives `c, d`, write `c d = m(c,d) [cd]`,
with `m(c,d) in L` and `[cd]` the representative of the coset of `cd`. The
nontrivial values are:

| product  | value           |
|----------|-----------------|
| `a a`    | `x`             |
| `a ab`   | `x b`           |
| `b a`    | `x^-1 y z^-1 ab`|
| `b b`    | `y`             |
| `b ab`   | `x^-1 z^-1 a`   |
| `ab a`   | `y^-1 z b`      |
| `ab b`   | `y^-1 a`        |
| `ab ab`  | `z`             |

These are the script's "cocycle" lines, read with doubled exponents. Let
`u = sum_d F_d d`. Since `c F = F^c c`, we get `c u = sum_d F_d^c m(c,d) [cd]`.
So the matrix `M_u` of `w -> w u` in the left basis `e_c = c` has entry
`F_d^c m(c,d)` in row `c`, column `[cd]`.

- **Homomorphism.** `w -> w u` is left `R[L]`-linear and `e_c (uv) = (e_c u) v`,
  so `M_(uv) = M_u M_v`. Certificate: log line `C2`, with independent symbols
  for `u` and `v`.
- **Injective.** The row of `e_1` lists `p, q, r, s`.
- **Formula.** Expanding `det M_u` by the Leibniz formula gives the 24 terms of
  the target. The script computes this with the twisted coefficients as
  independent symbols (log line `G1`).
- **Validation on known units.**
  - `V1`: Tabei's orbit-1 unit and its displayed inverse (arXiv:2608.00103,
    Table 1) multiply to 1 mod 2, and `Nrd = 1 mod 2`.
  - `V2`: Gardam's 2021 unit (arXiv:2102.11818, Theorem A, built from his
    Lemma 1) is a unit mod 2.

**Step 2: invariance.** Fix `h in {a, b, ab}` with class `H in K4`, and put
`phi(w) = h w h^-1`.

- `phi` is a ring automorphism with `phi(l w) = l^H phi(w)` for `l in R[L]`.
- Because `P/L` is abelian, `phi(e_c) = n_c e_c` with `n_c in L`.
- Applying `phi` to `e_c u = sum_d M_u(c,d) e_d` gives
  `n_c e_c phi(u) = sum_d M_u(c,d)^H n_d e_d`. So
  `M_(phi(u)) = D^-1 (M_u)^H D` with `D = diag(n_c)`, and
  `det M_(phi(u)) = (det M_u)^H`.
- On the other hand `M_(phi(u)) = M_h M_u M_(h^-1)`, and
  `det M_h det M_(h^-1) = det M_1 = 1`. So `det M_(phi(u)) = det M_u`.

Hence `Nrd(u)^H = Nrd(u)`. The script confirms the invariance of the symbolic
formula (`G1`).

**Step 2': values on group elements.** `M_g` is a monomial matrix, so
`Nrd(g)` is plus or minus a monomial. By the formula:

- `Nrd(a) = 1`: `q = 1`, all other coefficients 0;
- `Nrd(b) = 1` and `Nrd(ab) = 1` in the same way;
- `Nrd(x^m) = x^m (x^m)^A (x^m)^B (x^m)^C = 1`.

Multiplicativity gives `Nrd(g) = 1` for every `g in P`, so
`Nrd(lambda g) = lambda^4`.

**Step 3: criterion.**

- **Only if.** Suppose `u v = 1`. Then `Nrd(u) Nrd(v) = 1` in `R[L]`. Over a
  domain, the units of a Laurent polynomial ring are `R^x` times monomials, so
  `Nrd(u) = c x^i y^j z^k` with `c in R^x`. Invariance under `A` and `B`
  forces `j = k = 0` and `i = 0`. So `Nrd(u) = c in R^x`.
- **If.** Apply Step 2 over the domain `R[T]` to the element `T - u`. Then
  `chi(T) = det M_(T - u) = T^4 - c_1 T^3 + c_2 T^2 - c_3 T + Nrd(u)` is
  `K4`-invariant, so every `c_i` lies in `R[L]^(K4)`.
  - For invariant `l` we have `e_c l = l^c e_c = l e_c`. So `M_l = l I`, and
    `l` is central in `R[P]`.
  - Cayley-Hamilton over the commutative ring `R[L]` gives `chi(M_u) = 0`,
    hence `M_(chi(u)) = 0`, and by injectivity `chi(u) = 0`.
  - So `u (u^3 - c_1 u^2 + c_2 u - c_3) = -Nrd(u)`, and the second factor
    commutes with `u`. If `Nrd(u) in R^x`, the displayed element is a
    two-sided inverse.

QED
