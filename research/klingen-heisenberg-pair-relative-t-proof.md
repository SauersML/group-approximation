---
rg: 2
id: klingen-heisenberg-pair-relative-t-proof
kind: route
title: Uniform projective rigidity forces the commutator center to act trivially, then Burger finishes
target: klingen-heisenberg-pair-has-relative-property-t
requires: []
---

Imports.  These are verbatim from the source of Ioana--Spaas--Wiersma,
arXiv:2006.01874, read on 2026-09-17 from the arXiv e-print TeX.

- (I1) Definition (line 228): "the pair $(\Gamma,\Lambda)$ has the
  {\it relative property (T)} of Kazhdan-Margulis if any unitary
  representation of $\Gamma$ with almost invariant vectors has a
  non-zero $\Lambda$-invariant vector."
- (I2) Burger (line 237): "the pair $(\mathbb Z^2\rtimes\Sigma,\mathbb
  Z^2)$ has the relative property (T) for any non-amenable subgroup
  $\Sigma<\text{SL}_2(\mathbb Z)$ \cite{Bu91}".
- (I3) Theorem NPSgen (lines 758-771): "Let $\Gamma$ be a countable
  group and $\Lambda$ be a subgroup such that the pair
  $(\Gamma,\Lambda)$ has the relative property (T).  Then for every
  $\eps>0$, there exist $F\subset\Gamma$ finite and $\delta>0$ such that
  the following holds: Let $\Gamma\curvearrowright^{\sigma} (A,\tau)$ be
  a trace preserving action of $\Gamma$ on an abelian tracial von
  Neumann algebra $(A,\tau)$ and $c\in\emph{Z}^2(\Gamma,\mathcal U(A))$
  be a 2-cocycle. Let $\mathcal H$ be an $A$-module and
  $\pi:\Gamma\rightarrow \mathcal U(\mathcal H)$ be a map such that
  $\pi(g)\pi(h)=c(g,h)\pi(gh)$ and $\pi(g)a\pi(g)^*=\sigma_g(a)$ ...
  Assume $\xi\in\mathcal H$ is a unit vector such that
  $(\xi,\xi)_A=1$ and $\inf\{\|\pi(g)\xi-\xi a\|\mid a\in\mathcal
  U(A)\} <\delta$, for every $g\in F$.  Then there exist a
  $\sigma(\Lambda)$-invariant projection $p\in A$ with $\tau(p)>
  1-\varepsilon$, a vector $\eta\in p\mathcal H$ with
  $(\eta,\eta)_A=p$ and a map $b:\Lambda\rightarrow\mathcal U(Ap)$ such
  that (1) $c(h,k)p=b_h\sigma_h(b_k)b_{hk}^*$, for every
  $h,k\in\Lambda$ ..."

**Step 0 (Kazhdan pairs).**  For countable `G > L`, (I1) is equivalent
to the existence of a finite `F` and `delta > 0` such that every
representation with an `(F, delta)`-invariant unit vector has a nonzero
`L`-invariant vector.  If this failed, enumerate finite sets
`F_1 < F_2 < ...` exhausting `G`.  Take representations `pi_n` with
`(F_n, 1/n)`-invariant unit vectors and no `L`-invariant vector.  Then
`(+)_n pi_n` has almost invariant vectors, and has no nonzero
`L`-invariant vector, since each component of an invariant vector is
invariant.

**Step 1 (finite central kernel).**  Let `K = <z>/<z^m>`, which is
finite and central in `Gamma'' = Gamma/<z^m>`, and let
`A'' = H/<z^m>`.  `A''` is abelian because `[H,H] = <z^m>`.  We have
`Gamma''/K = Z^2 x| Sigma` and `A''/K = Z^2`.  So by (I2) and Step 0
there is a Kazhdan pair `(F_B, delta_B)` for `(Gamma''/K, Z^2)`.  Put
`F_2 = lift(F_B) u K` and `delta_2 = delta_B/2`.  If a unit `xi` is
`(F_2, delta_2)`-invariant, then `P_K xi` satisfies
`||P_K xi - xi|| <= max_k ||pi(k)xi - xi|| < delta_2`, where `P_K` is
the average over `K`.  Its range `H^K` is `Gamma''`-invariant (`K` is
normal) and carries a representation of `Gamma''/K` in which
`P_K xi/||P_K xi||` is `(F_B, delta_B)`-invariant.  Hence there is an
`A''`-invariant nonzero vector, so `(Gamma'', A'')` has relative (T).

**Step 2 (projective rigidity kills nontrivial `z^m`-spectrum).**  Fix a
set-theoretic section `s : Gamma'' -> Gamma` with `s(e) = e`.  Write
`s(g)s(h) = z^{m k(g,h)} s(gh)` with `k` integer-valued.  Since the
commutator pairing `H/<z> x H/<z> -> <z>` is bilinear with image
`[H,H] = <z^m>`, there are `g_0, h_0` in `A''` with
`[s(g_0), s(h_0)] = z^m`.  Hence `k(g_0,h_0) - k(h_0,g_0) = 1`.

Let `pi` be a unitary representation of `Gamma` and `u = pi(z^m)`,
which is central in `pi(Gamma)`.  Let `(F_1, delta_1)` be given by (I3)
for the pair `(Gamma'', A'')` from Step 1, with `eps = 1/2`.  Let
`xi` be a unit vector that is `(s(F_1) u s(F_2), delta)`-invariant,
with `delta = min(delta_1, delta_2/sqrt 2)`.

- Let `mu` be the spectral measure of `u` at `xi`.  Put
  `A = L^infty(T, mu)` with `tau(f) = int f dmu`, which is faithful.
- Let `H_0` be the closed subspace of vectors whose `u`-spectral
  measure is absolutely continuous with respect to `mu`.  It contains
  `xi`, is `pi(Gamma)`-invariant because `u` is central, and is an
  `A`-module by the Borel functional calculus.  Moreover
  `(xi,xi)_A = 1`, since `<f(u)xi, xi> = tau(f)`.
- `pi''(g) = pi(s(g))` satisfies
  `pi''(g)pi''(h) = c(g,h) pi''(gh)` with `c = u^k` in `Z^2(Gamma'', U(A))`,
  for the trivial action, and `pi''(g) a pi''(g)^* = a`.  Also
  `inf_a ||pi''(g)xi - xi a|| <= ||pi(s(g))xi - xi|| < delta_1` on `F_1`.

(I3) gives a projection `p` in `A` with `tau(p) > 1/2` and
`c(h,k)p = b_h b_k b_{hk}^*` on `A''`.  `A''` is abelian and `A` is
commutative, so `c(g_0,h_0)c(h_0,g_0)^* p = p`, that is `u p = p`.
Thus `p <= q := 1_{1}(u)`, and `||q xi||^2 = tau(q) >= tau(p) > 1/2`.

**Step 3 (Burger on the fixed part).**  `q` commutes with `pi(Gamma)`.
On `q H_0` the element `z^m` acts trivially, so this is a
representation of `Gamma''`.  The unit vector `q xi/||q xi||` is
`(F_2, sqrt 2 * delta)`-invariant, hence `(F_2, delta_2)`-invariant.
Step 1 gives a nonzero `A''`-invariant vector, which is `H`-invariant.

So `(s(F_1) u s(F_2), delta)` is a Kazhdan pair for `(Gamma, H)`, and
Step 0 gives `(KHT)`.  For the Klingen radical, `omega` is the standard
area form and `Sigma` preserves `omega`, so the hypotheses hold with
`m = 2` (`[N(v,0),N(w,0)] = N(0, 2 omega(v,w))`, and `omega` takes the
value 1).
