---
rg: 2
id: fpbs-boundary-tilted-susceptibility-kernel
kind: claim
title: Every quasi-invariant boundary of a Cayley graph carries Hutchcroft's tilted mass transport and lambda to 1-lambda duality, a finite half-tilted susceptibility above p_c forces the worst-pair rate, trees reach p_2, and the whole package holds on an amenable group where the threshold sticks at p_c
distinct_from:
  fpbs-simon-lieb-gauge-certificates-die-at-pc: that kills left-invariant gauge-weighted l1 certificates and lists root-dependent Radon-Nikodym tilts as a survivor; this builds that survivor as a kernel with its own duality, shows it is live on trees and shows it dies on an amenable group with every structural property present
  fpbs-critical-sphere-fibre-operator-below-one: its horofunction attempt tilts a sphere-fibre operator over a hyperbolic quotient at p_c and dies on level-preserving elements; this tilts the full two-point function above p_c by a Radon-Nikodym cocycle of an arbitrary quasi-invariant probability, with no quotient and no level structure
  fpbs-worst-pair-connectivity-rate-kernel: that proves (K) gives p_c < p_u; this gives a new sufficient condition for (K), with explicit rate half the Radon-Nikodym growth
  fpbs-lq-two-point-infinite-cluster-reduction: its item (C) forces (K) from one finite l^q norm of tau; the half-tilted susceptibility is a linear l^1 functional of tau weighted by a positive-definite matrix coefficient, and neither condition implies the other a priori
  fpbs-hyperbolic-and-nonunimodular-nonuniqueness: that imports Hutchcroft's nonunimodular theorem, whose tilt is the modular function of a larger automorphism group; here the acting group is the Cayley group itself, which is unimodular, and the weight is the Radon-Nikodym derivative of a boundary probability
artifacts:
  - experiments/boundary-tilt-2026-09-17/check_boundary_tilt.py
  - experiments/boundary-tilt-2026-09-17/check_boundary_tilt.out
---

**ESTABLISHED.** Proof in `fpbs-boundary-tilted-susceptibility-kernel-proof`.

**Setting.** `Gamma` is a finitely generated group, `S` a finite symmetric
generating set, and `G = Cay(Gamma,S)` has edges `x ~ xs`. `Gamma` acts on `G`
by left multiplication, and `o` is the identity. Write `tau_p`, `chi_p`,
`kappa_p(n) = min_(v in B_n) tau_p(o,v)` and `gamma(p)` as in
`fpbs-worst-pair-connectivity-rate-kernel`.

`(Z,nu)` is a standard Borel `Gamma`-space with a quasi-invariant probability
`nu`. Put `nu_x = x_* nu` and define the **boundary modular cocycle**

```text
Delta_zeta(x,y) = (d nu_y / d nu_x)(zeta)        (x, y in Gamma, zeta in Z).
```

For `lambda` real, the **boundary-tilted susceptibility** is

```text
chi^nu_lambda(p) = sum_y tau_p(o,y) phi_lambda(y),
phi_lambda(y)    = int_Z Delta_zeta(o,y)^lambda d nu(zeta).
```

Define `p^nu_c(lambda) = sup{p : chi^nu_lambda(p) < infinity}` and
`p^nu_t = p^nu_c(1/2)`. The **Radon–Nikodym growth** at `zeta` is

```text
h_nu(zeta) = limsup_n (1/n) log max_(y in B_n) Delta_zeta(o,y) .
```

**Theorem.**

1. **Tilted mass transport on every Cayley graph.** For `nu`-a.e. `zeta` and
   all `x, y, w`:
   - `Delta_zeta(x,y) Delta_zeta(y,w) = Delta_zeta(x,w)`;
   - `Delta_(g zeta)(gx,gy) = Delta_zeta(x,y)`;
   - `int Delta_zeta(o,y) d nu(zeta) = 1`.

   If `F : Gamma x Gamma x Z -> [0,infinity]` is measurable and
   `F(gx,gy,g zeta) = F(x,y,zeta)`, then

   ```text
   sum_y int F(o,y,zeta) d nu(zeta)  =  sum_y int F(y,o,zeta) Delta_zeta(o,y) d nu(zeta).
   ```

   This is Hutchcroft's tilted mass-transport principle (arXiv:1711.02590,
   Section 2.1), with the modular function replaced by `Delta_zeta`. It holds
   even though `Gamma` itself is unimodular.
2. **Duality and convexity.** Let `p` be in `[0,1]`.
   - `chi^nu_0(p) = chi^nu_1(p) = chi_p`.
   - `chi^nu_lambda(p) = chi^nu_(1-lambda)(p)` for every real `lambda`.
   - `lambda -> chi^nu_lambda(p)` is log-convex as a `[0,infinity]`-valued
     function.
   - Hence `chi^nu_(1/2)(p) <= chi^nu_lambda(p)` for `lambda in [0,1]`, and
     `p_c <= p^nu_c(lambda) = p^nu_c(1-lambda) <= p^nu_t`.

   This is the analogue of Hutchcroft's `p_c(lambda) = p_c(1-lambda)` and
   `p_t = p_(1/2)` (arXiv:1711.02590v3, Section 1.3).
3. **The half tilt forces the worst-pair rate.** Suppose
   `nu(h_nu >= h) > 0` for some `h > 0`, and `chi^nu_(1/2)(p) < infinity`.
   Then `limsup_n -(1/n) log kappa_p(n) >= h/2`. In particular:
   - on a nonamenable `G`, every `p in (p_c, p^nu_t)` satisfies kernel (K)
     `fpbs-worst-pair-connectivity-rate-positive-above-pc-universal`, with
     `gamma(p) >= h/2`;
   - `p^nu_t > p_c` gives `p_c < p_u`, and `p^nu_t <= p_u`.
4. **Comparison with the l2 threshold.** Let `pi_nu` be the Koopman
   representation, `(pi_nu(g) f)(zeta) = (d nu_g/d nu)(zeta)^(1/2) f(g^(-1) zeta)`.
   Then `phi_(1/2)(y) = <pi_nu(y) 1, 1>`. If `pi_nu` is weakly contained in the
   regular representation, then `chi^nu_(1/2)(p) <= ||T_p||_(2->2)` for all `p`,
   so `p_(2->2) <= p^nu_t`.
5. **Trees: the half tilt reaches `p_2 = (d-1)^(-1/2)`.** Take
   `G = Cay((Z/2)^(*d))` with `d >= 3` (so `G = T_d`), `Z` the space of ends and
   `nu` the visual measure from `o`. Let `b_zeta` be the Busemann function
   normalised at `o`. Then:
   - `Delta_zeta(o,y) = (d-1)^(-b_zeta(y))` and `h_nu = log(d-1)` everywhere;
   - `phi_(1/2)(y) = (1 + |y|(d-2)/d) (d-1)^(-|y|/2)`, the Harish-Chandra
     spherical function;
   - `p^nu_c(lambda) = (d-1)^(-(1 - min(lambda,1-lambda)))` for
     `lambda in [0,1]`.

   So `p^nu_t = (d-1)^(-1/2) > 1/(d-1) = p_c`, which is the value of
   Hutchcroft's `p_t` for the end-fixing group on `T_k` (arXiv:1711.02590v3,
   caption of Figure 1). Item 3 gives `gamma(p) >= (1/2) log(d-1)` on
   `(p_c,(d-1)^(-1/2))`. The true value is `-log p`, so the bound is sharp at
   the right endpoint.
6. **Class kill: the whole package holds on an amenable group, where the
   threshold is stuck at `p_c`.** Let `H = Cay(BS(1,2) x Z, {a,t,z}^(±1))`, with
   `BS(1,2) = <a,t | t a t^(-1) = a^2>`. Let it act on `R` through the affine
   action `a: x -> x+1`, `t: x -> 2x` (`z` acts trivially), and take `nu` the
   Cauchy law. Then:
   - (i) `H` is amenable, `gr(H) >= 2^(1/4) > 1` and `p_c(H) <= p_c(Z^2) < 1`;
   - (ii) items 1–2 hold, and `h_nu(zeta) >= (log 2)/4` for **every** `zeta`;
   - (iii) `chi^nu_(1/2)(p) = infinity` for every `p > p_c(H)`, so
     `p^nu_t(H) = p_c(H)`.

   More generally, `p^nu_t = p_c` on every amenable Cayley graph with `gr > 1`
   and `p_c < 1`, for every `(Z,nu)` with `nu(h_nu > 0) > 0`.

**Class killed by item 6.** Consider arguments that prove `p_c < p^nu_t`, or
just `chi^nu_(1/2)(p) < infinity` at one `p > p_c`, for a Cayley graph `G` and a
boundary `(Z,nu)`, using only:

- (a) the facts of item 6 of `fpbs-worst-pair-collapse-realized-on-amenable-growth`,
  that is everything valid on every Cayley graph with `gr > 1` and `p_c < 1`
  (transitivity, Harris–FKG, BK, Russo, Fekete, sharpness, Hermon–Hutchcroft);
- (b) properties of `(Gamma,Z,nu)` that also hold for `(BS(1,2) x Z, R, Cauchy)`.
  These include:
  - a nonatomic quasi-invariant probability;
  - the cocycle identity and diagonal invariance;
  - the tilted mass-transport principle;
  - `lambda <-> 1-lambda` duality and log-convexity;
  - Radon–Nikodym growth positive at every point, bounded below uniformly;
  - Zimmer-amenability of the action, and weak containment of `pi_nu` in the
    regular representation (both automatic because `Gamma` is amenable).

Every such argument is invalid. The invariant is item 3: any certificate for
the half tilt yields (K), and (K) is false on `H`.

**Exact failing step.** Hutchcroft's route from `p_c` to `p_c(lambda)` has two
parts:

- the tilted Aizenman–Barsky bound, which says that at `p_c(lambda)` no
  `1/2+eps` tilted moment is finite;
- the bootstrap, which says the `1-eps` tilted moment is finite at `p_c`.

Both are built from (a) and the structure in (b), so on `H` at least one of them
must fail when transported to a boundary cocycle. The rigidity remark in the
proof shows where the transport breaks.

- *Rigidity remark.* On a Cayley graph with the Cayley group acting, a
  boundary cocycle that does not depend on `zeta` is identically `1`.
- *Consequence.* A nontrivial tilt is therefore always root-dependent. The
  layers `{x : log Delta_zeta(o,x) in [n,n+1)}` then depend on the fibre point
  `zeta`, and translating a layer moves `zeta` to `x^(-1) zeta`.
- *Where it breaks.* Hutchcroft's Fekete inputs (Section 5.2 of the source,
  items 1–3 of its overview) are supermultiplicativity statements along layers.
  Transported, they need **fibre-uniform** bounds, a supremum over the orbit
  of `zeta`. The mass-transport principle controls only the `nu`-average.
- *The nonunimodular case.* There the fibre is one point: `Delta` lives on
  `V x V`, because the acting group is a nonunimodular subgroup of `Aut(G)`
  and not the Cayley group. So the supremum and the average coincide.

A proof of `p_c < p^nu_t` on a nonamenable Cayley graph must therefore
consume nonamenability of `Gamma` itself, or harmonicity of the cocycle, which
`H` with the Cauchy law lacks. It can do so, for example, through a
fibre-uniform estimate that fails on `H`.

**Position.**

- *The new kernel.* The kernel [BT], `fpbs-boundary-half-tilt-above-pc-universal`,
  asks for a boundary with `nu(h_nu > 0) > 0` and `p_c < p^nu_t`. By items 3
  and 4 it sits between the l2 gap and (K):
  - `p_c < p_(2->2)`, plus a boundary with `pi_nu ≺ lambda` and positive
    Radon–Nikodym growth, gives [BT];
  - [BT] gives (K).
- *Harmonic measure (recalled, not load-bearing).* Take the Poisson boundary of
  simple random walk. Its action is Zimmer-amenable (Zimmer), so `pi_nu ≺ lambda`
  (Kuhn). Its Radon–Nikodym growth is at least the Avez entropy, which is
  positive on nonamenable groups (Kesten; Kaimanovich–Vershik). So for harmonic
  measure, [BT] would sit between the l2 gap and (K) on every nonamenable
  Cayley graph.
- *Known classes.* Kernel (K) itself holds on every Cayley graph of a
  hyperbolic group, of an acylindrically hyperbolic group, or with a
  quasi-transitive nonunimodular automorphism subgroup, with
  `gamma >= (log gr)/2`. This follows from
  `fpbs-hyperbolic-nonunimodular-critical-l2-gap`,
  `fpbs-acylindrically-hyperbolic-critical-l2-gap`,
  `Z_2 <= ||T_p||^2_(2->2)` and item (C) of
  `fpbs-lq-two-point-infinite-cluster-reduction`.
- *Where (K) stays open.* It remains open wherever the window is known only
  through cost (Lyons' fixed-price-above-one groups).
