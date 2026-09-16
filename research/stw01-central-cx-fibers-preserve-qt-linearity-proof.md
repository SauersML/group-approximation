---
rg: 2
id: stw01-central-cx-fibers-preserve-qt-linearity-proof
kind: route
title: Central cuts make extreme quasitraces characters on C(X), so they descend to one fiber
target: stw01-central-cx-fibers-preserve-qt-linearity
requires: []
artifacts:
  - research/artifacts/stw01-central-fiber-qt-linearity-2026-09-16.md
---

Quasitraces are in Haagerup's sense (Definition 3.1 of *Quasitraces on exact
C\*-algebras are traces*, C. R. Math. Rep. Acad. Sci. Canada 36 (2014)):

- (i) `tau(x*x) = tau(xx*) >= 0`;
- (ii) `tau(a + ib) = tau(a) + i tau(b)` for self-adjoint `a, b`;
- (iii) linearity on abelian C\*-subalgebras;
- (iv) a witness `tau_2` on `M_2(A)` satisfying (i)-(iii) with
  `tau(x) = tau_2(x (x) e_11)`.

`QT(A)` is the set of normalized quasitraces.  Full details are in the artifact,
§§1-4.

**"Only if".**  Quasitraces pull back along star homomorphisms.  A pulled-back
quasitrace that is linear forces the original one to be linear when the map is
surjective.  So quotients inherit linearity.

**Standing facts.**

- (F1) On `C*(1,a)` with `a` self-adjoint, `tau` is a positive linear functional.
  Hence `|tau(a)| <= tau(1) ||a||`, and `tau(1) = 0` forces `tau = 0`.
- (F2) Using `z = u y^(1/2)` in (i), `tau(uyu*) = tau(y)` for self-adjoint `y`.
- (F3) `QT(A)` is convex, with witness `t tau_2 + (1-t) sigma_2`.  It is compact in
  the pointwise topology.  The pairs `(tau, tau_2)` lie in a product of discs, since
  `tau_2(1_2) = 2` and so `|tau_2(y)| <= 4||y||`.  They are cut out by closed
  conditions, and `QT(A)` is the image of this compact set under projection.  The
  tracial states form a closed convex subset.
- (F4) By Haagerup's Proposition 3.2, `N_tau = {x : tau(x*x) = 0}` is a closed
  two-sided ideal and `tau` factors through `A/N_tau`.  If `J subset N_tau` is a
  closed ideal, composing with `A/J -> A/N_tau` gives `tau = tau_J o q_J` with
  `tau_J` a quasitrace on `A/J`.

**Central cuts.**  Let `z >= 0` be central and put `tau_z(x) = tau(zx)`.

- (i) With `w = z^(1/2)x`, `w*w = z x*x` and `ww* = z xx*`.
- (ii) `za` and `zb` are self-adjoint.
- (iii) `C*(B, z)` is abelian for abelian `B`.
- (iv) Use `(tau_2)_(z (x) 1_2)`.

So `tau_z` is a quasitrace.  If `0 <= z <= 1`, linearity on `C*(1, a, z)` gives
`tau = tau_z + tau_(1-z)`.

**Extreme quasitraces are central characters.**  Let `tau` be extreme and
`0 <= z <= 1` central, with `t = tau(z)`.

- If `0 < t < 1`, then `tau = t(tau_z/t) + (1-t)(tau_(1-z)/(1-t))` forces
  `tau_z = t tau`.
- If `t = 0`, then `tau_z = 0` by (F1).
- If `t = 1`, then `tau_(1-z) = 0`.

So `tau(zx) = tau(z) tau(x)`.  Rescaling `u = (z + ||z||)/(2||z||)` and using
linearity on `C*(1, z, x)` extends this to every central self-adjoint `z` and
self-adjoint `x`.

`tau` is linear on the abelian algebra `Z(A)`.  Expand central `z = z_1 + i z_2` and
`w = w_1 + i w_2` into self-adjoint parts.  Then
`tau(zw) = tau(z) tau(w)`, so `tau` is a character on `Z(A)`.

**Descent to a fiber.**  Let `tau` be extreme.

1. `tau o theta` is a character of `C(X)`, so it equals `ev_p`.
2. For real `f in C_0(X \ {p})`, `tau(theta(f)* theta(f)) = f(p)^2 = 0`, so
   `theta(f) in N_tau`.  Taking real and imaginary parts handles complex `f`.
3. `N_tau` is a closed ideal, so `J_p subset N_tau`.
4. By (F4), `tau = tau_p o q_p` with `tau_p` a quasitrace on `A_p`.
5. `tau_p` is linear by hypothesis, hence so is `tau`.

**Krein--Milman.**  `QT(A)` is the closed convex hull of its extreme points, all of
which are traces.  The tracial states are closed and convex, so `QT(A)` consists of
traces.  A nonzero bounded quasitrace is a positive multiple of an element of
`QT(A)` by (F1).  QED.
