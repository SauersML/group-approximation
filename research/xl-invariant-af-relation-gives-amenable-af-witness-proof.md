---
rg: 2
id: xl-invariant-af-relation-gives-amenable-af-witness-proof
kind: route
title: Class-averaged Reiter witnesses are central in C*(R_n); strongly proximal pairs force single-valued boundary images
target: xl-invariant-af-relation-gives-amenable-af-witness
requires: []
---

**A.1 Algebra.**  A compact open equivalence relation `R_n` on a Cantor space
is a proper étale groupoid; `x -> |[x]_n|` is locally constant and
`C*(R_n)` is a finite direct sum of algebras `C(Y_i) ⊗ M_{k_i}` over clopen
sets.  `C*(R) = lim C*(R_n)` is AF (Renault; Giordano--Putnam--Skau), unital,
and simple because `R` is minimal and principal.  It is infinite dimensional
since `X` is infinite.  Simple infinite dimensional unital AF algebras are
`Z`-stable, nuclear, UCT and have traces; traces are faithful on simple
algebras, so `A` is stably finite and classifiable.  Traces on `C*(R)`
correspond to `R`-invariant probability measures (principal groupoid).
Since `g x g` maps `R_n` onto `R_n` it is an étale groupoid automorphism of
`R_n`, compatible with the inclusions; this gives `alpha_g`.

**A.2 Witnesses.**  Topological amenability gives, for finite `S subset G`
and `epsilon > 0`, a continuous `m : X -> Prob(F)` (`F` finite) with
`sup_x ||m(gx) - g.m(x)||_1 < epsilon` for `g in S`.  For `n` fixed put

```text
n(x) = |[x]_n|^-1 sum_{y in [x]_n} m(y),     xi(h) = n(.)(h)^{1/2} in C(X).
```

Continuity: `R_n` is covered by finitely many compact open bisections, so the
sum is locally a finite sum of continuous functions.  `<xi, xi> = 1`.
Equivariance: `[gx]_n = g[x]_n` gives
`n(gx) - g.n(x) = |[x]_n|^-1 sum_{y in [x]_n} (m(gy) - g.m(y))`, so
`||xi - g.xi||^2 <= sup_x ||n(x) - g.n(g^-1 x)||_1 < epsilon` (Powers--Størmer
as in `xl-commuting-minimal-action-gives-classifiable-witness-proof`).
Centrality: `xi(h)` is constant on `R_n`-classes; for such `f` and `a in C_c(R_n)`,
`(f a)(γ) = f(r γ) a(γ) = f(s γ) a(γ) = (a f)(γ)`, so `xi` commutes exactly
with `C*(R_n)`.  Given a finite subset of `A` and `delta`, approximate it
inside some `C*(R_{n_0})`, and take `n >= n_0`; since `||xi|| = 1` the
commutators are `< 2 delta`.  Exhausting `S`, `epsilon`, `delta` gives the
quasi-central approximation property, hence amenability
(Buss--Echterhoff--Willett; Ozawa--Suzuki).

**B.1 Lemma.**  If `B` is strongly proximal, every minimal closed invariant
`N subset P(B) x P(B)` lies in `D = {(delta_c, delta_c) : c in B}`.  Take
`(mu, nu) in N`; strong proximality gives `g_i` with
`g_i (mu + nu)/2 -> delta_c`; as `delta_c` is extreme, `g_i mu -> delta_c`
and `g_i nu -> delta_c`.  So `(delta_c, delta_c) in N`, and minimality gives
`N = closure of G(delta_c, delta_c) subset D` (`D` is closed and invariant).

**B.2 Theorem.**  Let `phi : X -> P(B)` be a continuous `G`-map and put
`phi_n(x) = |[x]_n|^-1 sum_{y in [x]_n} phi(y)`, a continuous `G`-map because
`[gx]_n = g[x]_n`.  Let `M subset X` be `G`-minimal.  The image of `M` under
`x -> (phi(x), phi_n(x))` is minimal, so by B.1 `phi(x) = phi_n(x) = delta_c`;
extremality of `delta_c` forces `phi(y) = delta_c` for all `y in [x]_n`.  So
`phi` is constant on `[x]_n` for `x in M` and all `n`.  The set
`S_n = {x : phi constant on [x]_n}` is closed.  If `x in M` and `y in [x]_m`
with `m >= n`, then `[y]_n subset [x]_m`, on which `phi` is constant; so the
`R`-saturation of `M` lies in every `S_n`.  That saturation is dense by
minimality of `R`, so `S_n = X` for all `n`: `phi` is constant on the dense
`R`-classes, hence constant, and its value is `G`-invariant.  A nontrivial
boundary carries no invariant measure (an invariant `mu` has a Dirac point in
its orbit closure, so `mu = delta_c` with `c` fixed, contradicting
minimality).  The factor statement is the case `phi = delta o p`.  QED.

**B.3 Commuting case.**  For `Gamma` acting by commuting homeomorphisms with
finite subgroups `Gamma_n`, `R_n = Gamma_n`-orbits satisfy the hypotheses
whenever the action is free with clopen orbits relation; directly, for
`Gamma` any minimal commuting group, B.1 applied to `(phi, phi o gamma)` on
`M` gives `phi o gamma = phi` on `M`, hence `phi` constant.  This strengthens
`xl-commuting-minimal-action-forbids-proximal-factors` for strongly proximal
`B` from factors to maps into `P(B)`.

*Calibration.*  For `G = Z/2` flipping the first coordinate of `{0,1}^N`
with `R_n` = agreement beyond coordinate `n`, (A) gives the evident action on
the CAR algebra, and (B) is vacuous, since amenable groups have no nontrivial
strongly proximal flows.  (Closedness of `S_n`: its complement is the range
of the open set `{(x,y) in R_n : p(x) != p(y)}` under the open range map.)  For `G = F_2` on `X = boundary of F_2`, (B) says no invariant minimal
AF relation exists, so no `G`-invariant minimal AF relation exists on `partial F_2`: the Dirac map
`boundary -> P(boundary)` is a nonconstant continuous `G`-map.
