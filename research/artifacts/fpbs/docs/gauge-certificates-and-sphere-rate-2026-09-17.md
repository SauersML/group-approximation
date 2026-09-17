# Gauge-weighted Simon–Lieb certificates, and the sphere two-point rate

Worker swarm-0917-w4-pull-bs-1, 2026-09-17. All proofs are written in full
below. No computation is used. Nothing here is imported except definitions
and the rate identity node `fpbs-integrated-pivotal-rate-identity`, which is
needed only in Corollary 3.4(b).

## 1. Setting

- `G = Cay(Gamma, S)` is a Cayley graph with finite symmetric generating set
  `S`, degree `d = |S|` and root `o = e`. Distance is `|x| = d(o,x)`, spheres
  are `S_r = {x : |x| = r}` and balls are `B_r`.
- `P` is the simple random walk operator on `l2(Gamma)`, `rho = ||P||`, and
  `p^n(x,y) = <delta_x, P^n delta_y>`.
- `tau_p(x,y) = P_p(x <-> y)`, `chi_p = sum_x tau_p(o,x)`. For `A` a vertex
  set, `tau^A_p(x,y)` is the probability that `x` and `y` are joined by an
  open path using only edges with both endpoints in `A`.
- `partial S` is the set of ordered edges `(x,z)` with `x in S`, `z not in S`.
- `a_n(p) = P_p(o <-> X_n) = sum_x p^n(o,x) tau_p(o,x)` and
  `lambda(p) = lim_n a_n(p)^(1/n)`, as in Section 6 of
  `research/artifacts/fpbs/exploration-pivotal-projections.md`.

Two elementary facts are used repeatedly.

**(F1) Inversion symmetry.** `tau_p(o,u) = tau_p(o,u^{-1})`. Left
translation by `u^{-1}` is a graph automorphism, so
`tau_p(o,u) = tau_p(u^{-1},o)`. Symmetry of connection gives
`tau_p(u^{-1},o) = tau_p(o,u^{-1})`.

**(F2) Simon–Lieb inequality.** Let `Lambda` be a finite vertex set,
`S' ⊂ Lambda`, `g in S'` and `y in Lambda \ S'`. Then

```text
tau^Lambda_p(g,y) <= sum_{(a,b) in partial S', b in Lambda}
                        tau^{S'}_p(g,a) p tau^Lambda_p(b,y).
```

*Proof.* Let `C` be the open cluster of `g` in the configuration restricted
to edges inside `S'`. Take an open path from `g` to `y` inside `Lambda`, and
let `a'` be its last vertex in `C`, with `b'` the next vertex. Then `b'` is not
in `C`, and the edge `(a',b')` is open. If `b'` were in `S'`, that edge would
lie inside `S'` and force `b' in C`. So `b' in Lambda \ S'` and
`(a',b') in partial S'`, and the rest of the path joins `b'` to `y` inside
`Lambda \ C`. Hence

```text
tau^Lambda(g,y) <= sum_A sum_{(a,b) in partial S', a in A, b in Lambda}
                    P(C = A, (a,b) open, b <-> y in Lambda \ A).
```

The event `{C = A}` depends only on edges inside `S'` with an endpoint in
`A`. The edge `(a,b)` leaves `S'`, and `{b <-> y in Lambda \ A}` uses only
edges with no endpoint in `A`. The three events are therefore independent.
Bound `P(b <-> y in Lambda \ A) <= tau^Lambda(b,y)` and sum over `A` using
`sum_{A ∋ a} P(C = A) = tau^{S'}(g,a)`. QED.

## 2. Gauge-weighted Simon–Lieb certificates never certify at or above p_c

A **weight** is a function `w : Gamma -> (0, infinity)`. It is
**K-quasi-submultiplicative** (`K >= 1`) if `w(uv) <= K w(u) w(v)` for all
`u, v`. For a finite set `U ∋ o` put

```text
psi^w_p(U) = p sum_{(x,z) in partial U} tau^U_p(o,x) w(z).
```

With `w = 1` this is the Duminil-Copin–Tassion mass `phi_p(U)`.

**Theorem 2.1.** Let `w` be K-quasi-submultiplicative and `U ∋ o` finite.
If `K psi^w_p(U) < 1`, then

```text
sum_u tau_p(o,u) w(u) <= K sum_{u in U} w(u) / (1 - K psi^w_p(U)) < infinity,
```

and `p < p_c`. Equivalently, `psi^w_p(U) >= 1/K` for every `p >= p_c` and every
finite `U ∋ o`.

*Proof. Step 1 (uniform finite-volume recursion).* Put `C_U = sum_{u in U} w(u)`
and

```text
F_n = max_{g in B_n} sum_{u in B_n} tau^{B_n}_p(g,u) w(g^{-1}u),
```

a finite number. Fix `g in B_n` and put `S' = gU ∩ B_n`. It contains `g`.

- For `u in B_n ∩ gU`, use `tau <= 1`. These terms contribute at most `C_U`.
- For `u in B_n \ gU`, `u` is not in `S'`, so (F2) with `Lambda = B_n` applies.
  In each boundary edge `(a,b)` of `S'` with `b in B_n`, the vertex `b` is not
  in `gU`. So `(a,b) in partial(gU) = g partial U`, and
  `tau^{S'}(g,a) <= tau^{gU}(g,a) = tau^U(o, g^{-1}a)`.
- Quasi-submultiplicativity gives `w(g^{-1}u) <= K w(g^{-1}b) w(b^{-1}u)`.

Therefore

```text
sum_{u in B_n \ gU} tau^{B_n}(g,u) w(g^{-1}u)
  <= K sum_{(a,b) in g partial U, b in B_n} p tau^U(o,g^{-1}a) w(g^{-1}b)
         sum_{u in B_n} tau^{B_n}(b,u) w(b^{-1}u)
  <= K psi^w_p(U) F_n,
```

because `b in B_n` and the edge `(g^{-1}a, g^{-1}b)` ranges over `partial U`.
Maximising over `g` gives `F_n <= C_U + K psi F_n`, so
`F_n <= C_U/(1 - K psi)`.

*Step 2 (volume limit).* `tau^{B_n}_p(o,u)` increases to `tau_p(o,u)`, since an
open path is finite. Monotone convergence gives
`sum_u tau_p(o,u) w(u) <= C_U/(1 - K psi)`.

*Step 3 (the tilted sum dominates the susceptibility).* From
`w(e) <= K w(u) w(u^{-1})` and `w(e) = w(e e) <= K w(e)^2`, we get
`w(u) w(u^{-1}) >= K^{-2}`. AM-GM then gives `w(u) + w(u^{-1}) >= 2/K`. By (F1),

```text
2 sum_u tau_p(o,u) w(u) = sum_u tau_p(o,u) (w(u) + w(u^{-1})) >= (2/K) chi_p.
```

So `chi_p < infinity`. The bound `E_p|K_o| >= infinity * theta(p)` then forces
`theta(p) = 0`, i.e. `p <= p_c`.

*Step 4 (strictness).* `theta(1) = 1`, so `p < 1`. `psi^w_{p'}(U)` is a
polynomial in `p'`: `U` is finite and `partial U` is finite, since `G` is
locally finite. So `K psi^w_{p'}(U) < 1` for some `p' > p`, and Steps 1–3 at
`p'` give `p < p' <= p_c`. QED.

**Corollary 2.2 (every weight, through its envelope).** For any weight `w`,
put `w^#(z) = sup_v w(zv)/w(v)`.

- `w^#` is the smallest function with `w(zv) <= w^#(z) w(v)`.
- It is submultiplicative, since
  `w(zz'v)/w(v) = [w(zz'v)/w(z'v)] [w(z'v)/w(v)]`, and `w^#(e) = 1`.

Suppose `w^#` is finite on `S`, i.e. `log w` is coarsely Lipschitz under left
multiplication. Then `w^#` is finite everywhere, because it is
submultiplicative. The Simon–Lieb closure of Step 1 for the target `w`, with
`K w(g^{-1}b)` replaced by `w^#(g^{-1}b)`, uses exactly the certificate
`psi^{w^#}_p(U)`. By Theorem 2.1 with `K = 1`, `psi^{w^#}_p(U) >= 1` for every
`p >= p_c` and every finite `U ∋ o`.

In particular, a decaying target such as `w(u) = exp(-t|u|)` has envelope
`exp(t|u|) >= 1`. Its Simon–Lieb certificate dominates the DCT mass `phi_p(U)`
itself, so it is harder to satisfy than the DCT mass.

### 2.3 The class killed, the invariant and the step where it dies

**Class.** A left-invariant, gauge-weighted, finite-volume l1 certificate
consists of a weight `w` and a finite `U ∋ o`. Its certificate inequality
closes the Simon–Lieb recursion uniformly over roots, and it is meant to
certify finiteness of the tilted susceptibility `sum_u tau_p(o,u) w(u)` at
some `p > p_c`. From there one would pass to nonuniqueness or to a walk-rate
kernel. Members:

- `w = 1`, the DCT mass itself;
- exponential growth gauges `exp(t|u|)`;
- polynomial gauges `(1+|u|)^D`, which are submultiplicative;
- characters `exp(phi(u))` for homomorphisms `phi : Gamma -> R`, which are
  multiplicative;
- `exp(h(u))` for quasimorphisms `h` of defect `D`, with `K = e^D`;
- through Corollary 2.2, every coarsely Lipschitz target, including decaying
  gauges.

**Invariant.** Inversion pairing (F1) on a Cayley graph, together with the
lower bound `w(u) w(u^{-1}) >= K^{-2}`. Closing the recursion forces that
bound.

**Step where every member dies.** Step 3 of Theorem 2.1. The certified sum
dominates `chi_p/K`, and `chi_p = infinity` for every `p >= p_c`. So the
certificate inequality is false at every `p >= p_c`, whatever `w` and `U`.
Nothing is lost at the volume limit or at the continuity step: the obstruction
is in the pairing.

**Survivors** (not covered by Theorem 2.1).

1. l2 or spectral certificates, `sp(nu_{U,p}) < 1`
   (`fpbs-spectral-dt-certificate-bounds-connectivity-operator`). These bound
   an operator norm rather than a weighted l1 sum.
2. Root-dependent cocycle weights `w(g,u)` not of the form `w(g^{-1}u)`, such
   as horofunction and Radon–Nikodym tilts. There the sup over roots is not a
   single translate, and inversion pairing is replaced by a mass-transport
   identity. Those tilts are recorded dead for other reasons in
   `fpbs-critical-sphere-fibre-operator-below-one` and
   `fpbs-amenable-wq-normal-relative-subcriticality`.
3. Restricted target sums, such as `sum_{h in H} tau_p(o,h)`. The weight
   `1_H` is not positive, and Theorem 2.1 does not apply.
4. Non-recursive bounds on decaying tilts. Section 3 shows that decaying tilts
   are exactly what the walk-rate kernels need.

**Calibration (hedged, not verified here).** On nonunimodular transitive
graphs (F1) fails. The mass-transport principle inserts the modular function,
and Hutchcroft's tilted susceptibility `E sum_{x in K_o} Delta(o,x)^lambda`
(arXiv:1711.02590) is finite at `p_c` for `lambda` away from `1/2`. So the
obstruction is specific to the Cayley (unimodular) setting, as it should be.

**Corollary 2.4 (susceptibility at and above p_c).** `chi_p = infinity` for
every `p >= p_c`.

*Proof.* Suppose `chi_p < infinity`. Each inner endpoint of `partial B_n` lies
in `S_n` and meets at most `d` boundary edges, and `tau^{B_n} <= tau`. So
`phi_p(B_n) <= p d sum_{|x| = n} tau_p(o,x)`, which tends to `0`. Theorem 2.1
with `w = 1` then gives `p < p_c`. QED.

## 3. The sphere two-point rate controls the walk rate

Put `M_r(p) = sum_{|x| = r} tau_p(o,x) = E_p|K_o ∩ S_r|` and

```text
g(p) = limsup_{r -> infinity} (1/r) log M_r(p),     g_+ = max(g, 0).
```

Then `log p <= g(p) <= log gr(G)`. `g` is nondecreasing in `p`. By
Corollary 2.4, `g(p) >= 0` for `p >= p_c`, since `sum_r M_r = infinity`.

**Lemma 3.1 (Chebyshev–Carne bound, proved here).** Let `(S_n)` be simple
random walk on `Z` from `0`. For all `n >= 0` and `x in Gamma`,

```text
p^n(o,x) <= rho^n P(|S_n| >= |x|).
```

*Proof.* Let `T_k` be the Chebyshev polynomials, `T_k(cos s) = cos(ks)`. For
real `s`, `cos^n s = E[e^{i s S_n}] = E[cos(s S_n)] = sum_k P(S_n = k) T_{|k|}(cos s)`.
Both sides are polynomials in `c = cos s`, and they agree on `[-1,1]`, so

```text
c^n = sum_k P(S_n = k) T_{|k|}(c)
```

identically. `P` is self-adjoint, because `S = S^{-1}`, and
`Q = P/rho` has spectrum in `[-1,1]`. The functional calculus gives
`P^n = rho^n sum_k P(S_n = k) T_{|k|}(Q)` with `||T_{|k|}(Q)|| <= 1`. `T_{|k|}(Q)`
is a polynomial of degree `|k|` in `P`, so `<delta_o, T_{|k|}(Q) delta_x> = 0`
when `|k| < |x|`. Hence
`p^n(o,x) <= rho^n sum_{|k| >= |x|} P(S_n = k)`. QED.

**Theorem 3.2.** For every `p in (0,1]`,

```text
rho <= lambda(p) <= rho cosh(g_+(p)).
```

*Proof.* The lower bound is Section 6.1 of
`research/artifacts/fpbs/exploration-pivotal-projections.md`. For the upper
bound, fix `t > g_+(p)`, so `t > 0`. There is `C_t` with `M_r <= C_t e^{tr}`
for every `r`. Since `p^n(o,x) = 0` for `|x| > n`, Lemma 3.1 gives

```text
a_n(p) = sum_{r <= n} sum_{|x| = r} p^n(o,x) tau_p(o,x)
       <= rho^n sum_{r <= n} P(|S_n| >= r) M_r
       <= C_t rho^n sum_{r <= n} P(|S_n| >= r) e^{tr}.
```

By Markov's inequality, `P(|S_n| >= r) e^{tr} <= E e^{t|S_n|} <= 2 (cosh t)^n`.
Therefore `a_n(p) <= 2 C_t (n+1) (rho cosh t)^n`, and `lambda(p) <= rho cosh t`.
Let `t` decrease to `g_+(p)`. QED.

**Corollary 3.3 (a sphere-rate kernel for p_c < p_u).** Suppose some
`p > p_c` has `g(p) < arccosh(1/rho)`. Then `lambda(p) < 1`, and `p_c < p <= p_u`.

*Proof.* Theorem 3.2 gives `lambda(p) < 1`. `tau` is nondecreasing in `p`, so
`lambda(p') <= lambda(p) < 1` for every `p' <= p`. A unique infinite cluster at
`p'` would give `tau_{p'}(o,x) >= theta(p')^2 > 0` by Harris–FKG, hence
`a_n(p') >= theta(p')^2` and `lambda(p') = 1`. So no `p' <= p` is in the
uniqueness phase, and `p_u >= p > p_c`. QED.

**Corollary 3.4 (a sphere-rate kernel for (IS)).**

- (a) If `g(p) -> 0` as `p` decreases to `p_c`, then `lambda(p) -> rho`.
- (b) By `fpbs-integrated-pivotal-rate-identity`, (a) is (IS).

*Proof.* (a) follows from the two-sided bound of Theorem 3.2 and `cosh 0 = 1`.
(b) The identity (6.4) of the cited artifact equates the (IS) integral with
`log(lambda(p_c+epsilon)/rho)`. QED.

## 4. Calibration and position in the kernel ordering

**Regular trees (exact).** On `T_d` with `d >= 3`:

- `M_r = d (d-1)^{r-1} p^r`, so `g(p) = log((d-1)p)`, `p_c = 1/(d-1)` and
  `g(p) -> 0` as `p` decreases to `p_c`. The condition of Corollary 3.4 holds.
- `rho = 2 sqrt(d-1)/d`, and `arccosh(1/rho) = log sqrt(d-1)`, because
  `1/rho + sqrt(1/rho^2 - 1) = (d + (d-2))/(2 sqrt(d-1)) = sqrt(d-1)`.
- So `{p : g(p) < arccosh(1/rho)} = (0, 1/sqrt(d-1))`. That is the radial
  l2-boundedness range of `tau_p = p^{|x|}` on `T_d`. Reading it as
  `p_{2->2}(T_d)` uses the Haagerup radial criterion, which is not
  re-verified here.
- At `p = p_c` the bound of Theorem 3.2 is exactly `rho`, so it is sharp there.
  For `p in [1/sqrt(d-1), 1)`, `lambda(p) < 1` still holds, since
  `|X_n| >= n(d-2)/(2d)` except on an event of exponentially small
  probability. Corollary 3.3 does not see these parameters.

So the sphere-rate kernel (G), "some `p > p_c` has `g(p) < arccosh(1/rho)`",
is strictly stronger than "`lambda(p) < 1` for some `p > p_c`". On trees it
cuts out the same range as the l2 gap. That is a warning that (G) may be as
hard as an l2 input. No implication in either direction is proved in general:

- the l2 gap gives `M_r <= ||T_p|| sqrt|S_r|`, hence `g(p) <= (1/2) log gr`;
- `(1/2) log gr` exceeds `arccosh(1/rho)` whenever `rho` is close to 1 with
  `gr > 1`.

**Consistency at p = 1.** `g(1) = log gr` and `lambda(1) = 1`, so Theorem 3.2
gives `cosh(log gr) >= 1/rho`, i.e. `gr >= e^{arccosh(1/rho)}`. This is a
Carne-type growth-versus-spectral-radius inequality. It says (G) is never
satisfied under uniqueness, where `g(p) >= log(theta^2 |S_r|^{1/r})`, which
tends to `log gr`.

**Where (EG) sits.** (EG) is "`g(p) -> 0` as `p` decreases to `p_c`". We have:

- (EG) implies (G), since `arccosh(1/rho) > 0`;
- (G) implies nonuniqueness above `p_c` (Corollary 3.3);
- (EG) implies (IS) (Corollary 3.4).

Under the collapse scenario (6.6), `g(p) >= log gr` for every `p > p_c`, so
(EG) and (G) fail, as they must.

(EG) has two parts:

- **(EG0)** `g(p_c) = 0`. `g(p_c) >= 0` is Corollary 2.4. The upper bound would
  follow from Hutchcroft's bound `tau_{p_c}(o,x) <= gr^{-|x|}`
  (arXiv:1603.00555), which is not re-verified here.
- **(EG1)** right-continuity of the nondecreasing function `g` at `p_c`.

(EG1) is a statement about exponential rates, so fixed-`r` continuity of
`M_r` gives nothing. This is the same limit-order issue as in Section 6.3 of
the pivotal artifact, moved from walk time to extrinsic radius.

**Relation to Section 2.** The hypothesis of Corollary 3.3 is equivalent to
finiteness, at some `p > p_c`, of the *decaying* tilt
`sum_x tau_p(o,x) e^{-t|x|}` for some `t < arccosh(1/rho)`. By Corollary 2.2 that target cannot be certified by any Simon–Lieb
l1 certificate at `p > p_c`. A proof of (G) or (EG) must come from outside the
killed class: spectral certificates, cocycle tilts, or non-recursive
geometric input.
