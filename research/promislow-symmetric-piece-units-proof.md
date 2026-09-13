---
rg: 2
id: promislow-symmetric-piece-units-proof
kind: route
title: The reduced norm of a symmetric-piece element is N^2 - xyz M^2, and exponent parity splits it
target: promislow-symmetric-piece-units-satisfy-gardam-equations
requires:
  - promislow-group-ring-units-are-constant-reduced-norm
---

Notation as in the target.

**Source (Gardam 2021).** Lemma 1 of arXiv:2102.11818 (p. 6), from the PDF
text extracted on MSI. The extraction drops sub- and superscripts, so they are
reconstructed here. It reads: "Let K be a field ... Let p,q,r,s ∈
K[x^±1,y^±1,z^±1] ... Adjoin square roots of x and y and suppose that
p0,q0,r0,s0 ... defined by p0 = x^-1/2 y^-1/2 p, q0 = y^1/2 q, r0 = x^-1/2 r,
s0 = s are all invariant under the action of ab (i.e. under x ↦ x^-1,
y ↦ y^-1, z ↦ z). If the equations (1) p0^a s0 − q0 r0^a +
z^-1(p0^a s0 − q0 r0^a)^a = 0, (2) p0 p0^a − q0 q0^a − r0 r0^a + s0 s0^a = 1
hold, then p + qa + rb + sab is a unit in K[P]." The proof's table gives
`p' = x^-1 p^a`, `q' = −x^-1 q`, `r' = −y^-1 r`, `s' = z^-1 s^a`.

**Step 1: (1) and (2).** The script `research/artifacts/promislow-reduced-norm-cp.py`
computes exactly with symbols `P0, Q0, R0, S0`:

- the invariance is imposed as `f^C = f`, `f^B = f^A`;
- half-integral exponents are stored doubled.

It prints (log lines `L1`, `C1`):
- `(alpha' alpha)` has coset-`a` and coset-`b` components 0, coset-1 component
  `N`, and coset-`ab` component `M`;
- `(alpha alpha')` has coset-1 component `N` and coset-`ab` component `x y M`;
- `det M_alpha = N^2 - x y z M^2` identically, as a 16-term polynomial.

(1) is Gardam's own computation in the proof of Lemma 1. For (2) by hand, put
`mu = x^(1/2) y^(1/2) z^(1/2) M = z^(1/2) xi + z^(-1/2) xi^A`. Expanding
`N^2 - mu^2` reproduces the 24-term formula of the requires, evaluated on
symmetric pieces. The cross terms `2 p0 p0^A s0 s0^A` and
`2 q0 q0^A r0 r0^A` of `N^2` cancel against `-2 xi xi^A`. The rest match term
by term: `-z (p0^A)^2 s0^2`, `2 z p0^A s0 q0 r0^A`, `-z q0^2 (r0^A)^2`, their
`A`-images with `z^-1`, and the four fourth powers.

**Step 2: parity.**
- Exponents of `p0` lie in `(Z+1/2) x (Z+1/2) x Z`.
- Exponents of `q0` lie in `Z x (Z+1/2) x Z`.
- Exponents of `r0` lie in `(Z+1/2) x Z x Z`.
- Exponents of `s0` lie in `Z^3`.

The `K4`-action changes signs only, so it preserves these classes. Hence every
exponent of `N` lies in `Z^3` and every exponent of `mu` in `(Z+1/2)^3`
(certificate: log line `C1 exponent parity classes`).

**Step 3: (3).**
- **Only if.** If `alpha` is a unit, the requires gives `Nrd(alpha) = c` with
  `c in R^x`. In `A = R[x^(+-1/2), y^(+-1/2), z^(+-1/2)]`, a Laurent
  polynomial ring over a domain, `(N - mu)(N + mu) = c` is a unit. So both
  factors are units: `N - mu = c_1 m_1` with `c_1 in R^x` and `m_1` a
  monomial.
  - By Step 2 the exponent supports of `N` and `mu` are disjoint, so `N = 0`
    or `mu = 0`.
  - If `N = 0`, then `mu^2 = -c`, so `mu = c' m` with `m^2 = 1`. That forces
    `m = 1`, which is impossible for exponents in `(Z+1/2)^3`.
  - So `mu = 0`, i.e. `M = 0`, and `N^2 = c`. Then `N = c'' m` with `m^2 = 1`,
    so `m = 1`, `N in R` and `N^2 in R^x`. Thus `N in R^x`.
- **If.** If `M = 0` and `N in R^x`, then (1) gives
  `(N^-1 alpha') alpha = 1 = alpha (N^-1 alpha')`.

**Step 4: (4).** Let `alpha = lambda x^i y^j z^k c`.
- `c = 1`: `p0 = lambda x^(i-1/2) y^(j-1/2) z^k` is invariant only if
  `i = j = 1/2`. Impossible.
- `c = a`: `q0 = lambda x^i y^(j+1/2) z^k` needs `j = -1/2`. Impossible.
- `c = b`: `r0` needs `i = 1/2`. Impossible.
- `c = ab`: `s0 = lambda x^i y^j z^k` is invariant iff `i = j = 0`, giving
  `lambda z^k ab`. Its inverse is `lambda^-1 z^-k (ab)^-1`, so it is a unit
  exactly when `lambda in R^x`. Consistently, `N = lambda^2` and `M = 0`.

QED
