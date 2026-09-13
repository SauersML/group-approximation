# Patterson–Sullivan averaged tilting and relative susceptibility

**Setting.**
* `Gamma` is finitely generated and nonamenable.
* `H` is an infinite amenable normal subgroup, and `Q = Gamma/H` is non-elementary hyperbolic.
* `pi : Gamma -> Q` is the quotient map, `X = Cay(Gamma,S)` and `d = |S|`.

Write `tau_p(x,y) = P_p(x <-> y)` and

```text
sigma_p(q) = sum_{pi(y) = q} tau_p(o,y),      chi^H_p = sigma_p(1) = E_p|K_o ∩ H|.
```

`S_p` is convolution by `sigma_p` on `l2(Q)`, and `N(sigma_p) = ||S_p||`. For amenable
`H` this equals `||T_p||` (`fpbs-fibre-summed-connectivity-operator`).

Let `nu` be a quasi-invariant, non-atomic Borel probability measure on `dQ`, such as a
Patterson–Sullivan measure. `Gamma` acts on `dQ` through `pi`. Put

```text
P(y,xi) = d(pi(y)_* nu)/d nu (xi),        Delta_xi(x,y) = P(x^(-1) y, x^(-1) xi).
```

**What this note checks.** Hutchcroft proves `p_c < p_t` for nonunimodular
quasi-transitive graphs (arXiv:1711.02590v3, `thm:pcpt`). This note checks how much of
that proof survives when the modular function is replaced by `Delta_xi` and the
direction `xi` is random with law `nu`. Line numbers refer to
`NonunimodularPercolation_Revised5.tex` in the arXiv source of 1711.02590v3.
* **Sections 1–3: what transfers.** An exact mass-transport principle; a symmetric,
  convex averaged tilted susceptibility that dominates `chi^H_p`; exact layers; and
  left-continuity of the worst-direction rate.
* **Section 4: where it stops.** Three steps need a supremum over directions or a
  positive orbit mass.
* **Section 5: the gap.** At kernel level the supremum is not controlled by the average.
  The section also records a scalar alternative.

Nothing here proves `p_c < p_u` for a new graph.

## 1. Exact mass transport with the Radon–Nikodym cocycle

**Lemma 1.** Let `F : Gamma x Gamma x dQ -> [0,infinity]` be measurable with
`F(gx, gy, g xi) = F(x, y, xi)`. Then

```text
sum_y int F(o,y,xi) d nu(xi)  =  sum_y int F(y,o,xi) Delta_xi(o,y) d nu(xi),
```

and `Delta_xi(x,z) = Delta_xi(x,y) Delta_xi(y,z)` for `nu`-a.e. `xi`.

*Proof.*
* Invariance gives `F(o,y,xi) = F(y^(-1), o, y^(-1) xi)`.
* Substitute `eta = y^(-1) xi`. Then `d nu(xi)` becomes
  `d(y^(-1)_* nu)(eta) = P(y^(-1), eta) d nu(eta)`.
* Reindex `y -> y^(-1)` and use `P(y,eta) = Delta_eta(o,y)`.
* The cocycle identity is the chain rule
  `d((gh)_* nu)/d nu (xi) = d(h_* nu)/d nu (g^(-1) xi) * d(g_* nu)/d nu (xi)`. QED.

Apply Lemma 1 to `F Delta^lambda`, using `Delta_xi(y,o) = Delta_xi(o,y)^(-1)`:

```text
sum_y int F(o,y,xi) Delta_xi(o,y)^lambda d nu  =  sum_y int F(y,o,xi) Delta_xi(o,y)^(1-lambda) d nu.
```

This is the source's tilted mass-transport principle (lines 756–760), with the sum over
orbits replaced by the `nu`-integral.

## 2. The averaged tilted susceptibility and the threshold it controls

Put

```text
chi^nu_(p,lambda) = sum_y tau_p(o,y) int Delta_xi(o,y)^lambda d nu(xi) = sum_q sigma_p(q) Xi_lambda(q),
Xi_lambda(q)      = int (d(q_* nu)/d nu)^lambda d nu.
```

* **Symmetry.** Lemma 1 with `F = tau_p` gives `chi^nu_(p,lambda) = chi^nu_(p,1-lambda)`.
* **Convexity.** By Hölder, each `lambda -> Xi_lambda(q)` is log-convex, and
  `Xi_0 = Xi_1 = 1`. So `lambda -> chi^nu_(p,lambda)` is convex. It equals `chi_p` at
  `lambda = 0` and `lambda = 1`, and is smallest at `lambda = 1/2`.
* **Sandwich.** `Xi_(1/2)(1) = 1`, and `Xi_(1/2) <= 1` by Cauchy–Schwarz. So
  `chi^H_p <= chi^nu_(p,1/2) <= chi_p`.

Let `p_t^nu = sup{p : chi^nu_(p,1/2) < infinity}`. Then `p_t^nu >= p_c`.

**Proposition 2.** If `p_c < p_t^nu`, then `p_c < p_u`.

*Proof.* Take `p` in `(p_c, p_t^nu)`, so `chi^H_p < infinity`. Suppose `p > p_u`. Then
the infinite cluster is unique, and Harris–FKG gives `tau_p(o,h) >= theta(p)^2 > 0` for
every `h` in `H`. Since `H` is infinite, `chi^H_p = infinity`, a contradiction. So
`p_c < p <= p_u`. QED.

**Upper side (imported).** `Xi_(1/2)(q) = <kappa(q) 1, 1>`, where `kappa` is the Koopman
representation on `L2(dQ, nu)`:

```text
(kappa(q) f)(xi) = P(q,xi)^(1/2) f(q^(-1) xi).
```

The boundary action of `Q` is amenable, so `kappa` is weakly contained in `lambda_Q`, by
Kuhn's theorem for amenable actions. So `chi^nu_(p,1/2) = <kappa(sigma_p) 1, 1> <= N(sigma_p)`,
and

```text
p_(2->2)  <=  p_t^nu  <=  p_u.
```

So `p_c < p_t^nu` is an intermediate target. The L2 gap implies it, through the imported
step. It implies `fpbs-amenable-wq-normal-relative-subcriticality` for normal `H`.

**Addendum to Section 5, third bullet, of `sphere-fibre-operator-is-critical-l2.md`.**
That bullet shows that the average `sum_q sigma_p(q) Xi_(1/2)(q)` is at most
`N(sigma_p)`, so it cannot feed a Schur test for `S_p`. Proposition 2 uses no Schur test:
the average dominates `chi^H_p` directly. The inequality that points the wrong way for
`p_(2->2)` is harmless for `p_u`.

## 3. What transfers on F_2 with the uniform measure

Take `Q = F_2 = <a,b>`, with `nu` uniform: a cylinder of length `n >= 1` has mass
`1/(4 * 3^(n-1))`. Take `S` tree-projected, so that every `pi(s)` lies in
`{1, a^±, b^±}`. With `(q|xi)` the Gromov product at `1`,

```text
P(q,xi) = 3^(2(q|xi) - |q|),        Xi_(1/2)(q) = (1 + |q|/2) 3^(-|q|/2) = phi_0(q).
```

For the second identity, let `n = |q|`. Then:
* `nu((q|xi) = 0) = 3/4`;
* `nu((q|xi) = j) = 3^(-j)/2` for `1 <= j < n`;
* `nu((q|xi) >= n) = 3^(1-n)/4`.

Let `h_xi(x) = log_3 Delta_xi(o,x) = 2(pi(x)|xi) - |pi(x)|`. This is a Busemann function
pulled back to `X`.
* **Exact layers.** An edge of `X` changes `h_xi` by `-1`, `0` or `+1`. So every path
  crosses each intermediate level set `L_t(xi) = {h_xi = t}`. For a general `S`, the jumps
  are at most `max_s |pi(s)|`.
* **Supermultiplicativity.** By the cocycle identity,
  `h_xi(xz) - h_xi(x) = h_(pi(x)^(-1) xi)(z)`. So re-rooting at a vertex of a layer changes
  the direction but keeps the form of the event. The infimum over `xi` of
  `P_p(o <-> L_n(xi) inside {h_xi >= 0})` is supermultiplicative, by the exploration
  argument of `lem:alpha` (source lines 1536–1557). This is Section 5, first bullet, of
  `sphere-fibre-operator-is-critical-l2.md`.
* **Left-continuity.**
  * Fix `r`, and consider connection by an open path of length at most `r`. Its
    probability is a polynomial in `p`, and it depends on `xi` only through the first `r`
    letters. So it is jointly continuous on `[0,1] x dF_2`.
  * The supremum over `r` is jointly lower semicontinuous.
  * The infimum over the compact set `dF_2` of a jointly lower semicontinuous function is
    lower semicontinuous in `p`. To see this, take near-minimizers `xi_k` for `p_k -> p`,
    and pass to a convergent subsequence.
  * This replaces the minimum over finitely many orbits at source line 1672. So the
    worst-direction rate `alpha^inf_p` is left-continuous, as in `lem:alphacontinuity`.

## 4. Where the transplant stops

Three steps in the proof of `thm:pcpt` use quasi-transitivity, through a supremum over
roots or a positive orbit mass. With random directions, each step needs a bound on the
supremum over directions.

### Sprinkling

This is the proof of `prop:tiltedmeanfieldlowerbound`, source lines 925–969.
* **In the source.** BK gives `tau~_(i+1) <= (eps/(1-p)) tau~_i A tau_p` entrywise
  (line 947). The recursion closes with
  `chi~_i <= (C_lambda eps/(1-p))^i (chi*_(p,lambda))^(i+1)` (line 954), where `chi*` is a
  maximum over finitely many orbits (line 929).
* **Pointwise in `xi`.** The same recursion closes with `chi*(p) = sup_xi chi_(p,1/2)(o,xi)`,
  where `chi_(p,1/2)(o,xi) = sum_y tau_p(o,y) Delta_xi(o,y)^(1/2)`.
* **That supremum is L2-strength.** Fix `xi` and put `f(q) = P(q,xi)^(1/2)`. Then
  `(S_p f)(q) = f(q) chi_(p,1/2)(o, q^(-1) xi) <= chi*(p) f(q)`. The Schur test gives
  `N(sigma_p) <= chi*(p)`, so `{chi* < infinity}` lies inside `[0, p_(2->2)]`.
* **Averaged over `xi`.** The `i`-th sprinkled term is
  `<kappa((sigma_p a)^(*i) * sigma_p) 1, 1>` with `a = pi_* 1_S`. This is not bounded by a
  power of `chi^nu_(p,1/2)`.

**Kesten barrier.** Let `Phi` send nonnegative symmetric functions on `Q` to
`[0,infinity]`, with `Phi(f * g) <= Phi(f) Phi(g)` and `Phi(f) >= f(1)`. Then
`f^(*2n)(1) <= Phi(f)^(2n)`. Kesten's formula `||lambda_Q(f)|| = lim f^(*2n)(1)^(1/2n)`
then gives `Phi(f) >= ||lambda_Q(f)||`. So any multiplicative closure of the relative
sprinkling recursion that dominates `chi^H_p` is at least `N(sigma_p)`. This sharpens the
fourth Attempts bullet of `fpbs-amenable-wq-normal-relative-subcriticality`.

### Tilted Aizenman–Barsky

This is `prop:tiledAizBar`, source lines 991–999.
* **In the source.** The BK step passes from a fixed vertex to the random root at a cost
  of `[inf_v P([rho]=[v])]^(-1)` (line 1270). This is finite because there are finitely
  many orbits.
* **Here.** The root is `(o,xi)` with `xi ~ nu`. The orbits of `Gamma` on `Gamma x dQ` are
  indexed by `xi`, and each has `nu`-mass 0, since `nu` has no atoms. So the constant is
  infinite.
* **Replacing it by an average.** For the tilted magnetization this needs
  `int M(o,xi)^2 d nu(xi) <= C (int M(o,xi) d nu(xi))^2`. That is the same
  supremum-versus-average problem.

### Best versus worst direction

This is `lem:probinfsup`, source lines 1571–1591.
* **In the source.** The proof uses quasi-transitivity and the maximum principle for
  `Delta` to reach the orbit of any vertex within `r_0(1+r)` steps (line 1582).
* **Here.** Directions can be compared only along `Q`-orbits in `dQ`. Harris–FKG and
  Lemma 1 give `chi_(p,1/2)(o,xi) >= p 3^(-1/2) chi_(p,1/2)(o, pi(s)^(-1) xi)` for `s` in
  `S`. So

  ```text
  chi_(p,1/2)(o, pi(g)^(-1) xi)  <=  (3^(1/2)/p)^|g|_S  chi_(p,1/2)(o,xi).
  ```

  Nothing relates different `Q`-orbits, and each orbit is `nu`-null.
* **Consequence.** `prop:tamedecay` (lines 2036–2054) and `lem:bootstrap` (a bound for
  every `v`, lines 2330–2342) rest on this comparison. So only the worst-direction rate of
  Section 3 reaches `p_c`. But the contradiction at lines 2345–2362 needs the moment bound
  in a `nu`-typical direction.

## 5. Supremum versus average

* **`T_4 □ Z`, with `S = {(a,0),(b,0),(1,1)}^±`.**
  * The stabilizer of `o` in `Aut(T_4) x {id}` preserves `tau_p` and fibres, acts
    transitively on spheres, and acts transitively on `dT_4`. So `sigma_p` is radial,
    `chi_(p,1/2)(o,.)` is constant, and `chi* = chi^nu`.
  * The end stabilizer `Aut(T_4)_xi x Z` acts transitively, and its modular function is
    `3^(± h_xi)`.
  * So the random-end tilt at `lambda = 1/2` is Hutchcroft's tilt, and his theorem gives
    `p_c < p_t^nu`. This is a consistency check.
* **`X_rig`.** By Section 3 of `research/artifacts/fpbs-f2xz-all-generating-sets-2026-09-12.md`,
  `Aut(X_rig)` is contained in `Gamma ⋊ <alpha>`, which is discrete and unimodular.
  Nothing forces `sigma_p` to be radial, and `chi_(p,1/2)(o,.)` may vary with `xi`.
* **Kernel example.** The constraints used above are Harris–FKG for fibre sums:
  `sigma(sq) >= p sigma(q)` and `sigma(qs) >= p sigma(q)` for `s` in `{a^±, b^±}`. They do
  not bound the supremum by the average. Fix `0 < p < 3^(-3/2)` and put

  ```text
  sigma(q) = sup{ p^(|g|+|h|) 3^(-n/2) : n >= 0, g, h in F_2, q = g a^n h }.
  ```

  1. `sigma(1) = 1`, and both distortion bounds hold, since `|sg| <= |g| + 1`.
  2. **The average is finite.** Bound the supremum by the sum over representations. Use
     `|g a^n h| >= n - |g| - |h|`, at most `2 * 3^i` words of length `i`, and
     `phi_0(q) <= (1 + |q|/2) 3^(-|q|/2)`. Then
     `sum_q sigma(q) phi_0(q) <= 4 sum_{n,i,j} 3^(-n) (3^(3/2) p)^(i+j) (1 + (n+i+j)/2) < infinity`.
  3. **The supremum is infinite.** Since `(a^n | a^infinity) = n`,
     `sum_q sigma(q) P(q, a^infinity)^(1/2) >= sum_n sigma(a^n) 3^(n/2) = infinity`.

  This `sigma` is only a kernel. It has not been checked to be positive definite, or to be
  the fibre profile of any percolation measure.
* **A scalar alternative.** In integrated form, Russo's formula and BK give

  ```text
  d/dp chi^H_p  <=  sum_{h in H} sum_{oriented e} tau_p(o,e^-) tau_p(e^+,h)  <=  (d/p) B^H_p,
  B^H_p = sum_q sigma_p(q)^2,
  ```

  using `sigma_p(pi(s)^(-1) q) <= p^(-1) sigma_p(q)`. Suppose we had an a priori bound
  `B^H_r <= C (chi^H_r)^2` for `r` near `p_c`, in a form that survives finite-volume
  truncation, and also `chi^H_(p_c) < infinity`. Then Riccati comparison would give
  finite `chi^H` on an interval above `p_c`.
  * **Not L2-strength.** The Section 4 kernel of `sphere-fibre-operator-is-critical-l2.md`
    has `sum_q sigma(q)^2 <= C sigma(1)^2` and `N(sigma) = infinity`.
  * **No mechanism known.** No mechanism for this bound is known.

## 6. Not verified here

* **Imported.**
  * Kuhn's weak-containment theorem for amenable actions, and amenability of the boundary
    action of `Q`. These are used only for `p_(2->2) <= p_t^nu`.
  * Monotonicity of uniqueness above `p_u` (Häggström–Peres, Schonmann), used in
    Proposition 2.
* **Section 3 is written for `F_2`, uniform `nu` and tree-projected `S`.** For a general
  hyperbolic `Q`, the Patterson–Sullivan derivative equals `exp(v h)` only up to bounded
  factors, so the layers are coarse.
* **The exploration argument** for supermultiplicativity is cited, not rewritten.
* **Line numbers.** Section 4's line numbers come from the arXiv TeX source of
  1711.02590v3. Published versions may number statements differently.
