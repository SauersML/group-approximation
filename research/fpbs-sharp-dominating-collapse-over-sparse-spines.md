---
rg: 2
id: fpbs-sharp-dominating-collapse-over-sparse-spines
kind: claim
title: Collapse families that contain Bernoulli, keep only Bernoulli finite clusters and match theta and local laws to any prescribed precision exist wherever invariant sparse spines exist
distinct_from:
  fpbs-soft-collapse-iff-invariant-sparse-spines: that family is critical Bernoulli plus a spine for t>p_c, so its finite clusters have the heavy critical tail and it does not contain xi_t; here omega_t contains xi_t, every finite cluster is a finite xi_t cluster (exponential Hermon--Hutchcroft tail), and theta and ball laws match Bernoulli up to a prescribed error
  fpbs-finite-energy-fkg-collapse-over-central-z2-slabs: that adds deletion tolerance and Harris--FKG on the central-Z2 class but keeps the critical finite-cluster tail; this adds supercritical sharpness, Bernoulli domination and quantitative closeness on the spine class, and leaves FKG and deletion tolerance undecided
---

**ESTABLISHED (class-killing obstruction).** Proof in
`fpbs-sharp-dominating-collapse-over-sparse-spines-proof`.

Let `Gamma` be nonamenable and finitely generated, `S` a finite symmetric
generating set, `G = Cay(Gamma,S)`, `xi_t = {e : U_e <= t}` the standard
coupling, and `t_1 = (1+p_c)/2`. Write `chi^f_t`, `tau^f_t`, `theta_xi(t)` for
the Bernoulli truncated susceptibility, truncated two-point function and
percolation probability.

**Theorem.** Suppose `G` has invariant sparse spines (in the sense of
`fpbs-soft-collapse-iff-invariant-sparse-spines`; by Theorem B there this holds
whenever some surjection `Gamma -> Z` has a finitely generated kernel). Let
`f : (p_c,t_1] -> (0,1]` be nondecreasing and `R : (p_c,t_1] -> N`
nonincreasing, both arbitrary. Then there is an ergodic probability-preserving
`Gamma`-system carrying the labels `U` and equivariant configurations
`omega_t`, `t in [0,1]`, of the form

```text
omega_t = xi_t                  (t <= p_c),
omega_t = xi_t ∪ A_{n(t)}       (t >  p_c),
```

where `(A_n)_{n>=1}` is a decreasing sequence of a.s. connected infinite
invariant random subgraphs, **independent of `U`**, and `n(t)` is nonincreasing.
It satisfies:

* **(S1)–(S4)** of `fpbs-soft-collapse-iff-invariant-sparse-spines`: monotone,
  Bernoulli joint law for `t <= p_c`, ergodic and insertion tolerant, exactly one
  infinite cluster for every `t > p_c`, with `theta_omega(t) -> 0` as `t ↓ p_c`.
* **(H1) Bernoulli domination.** `xi_t ⊆ omega_t` for all `t`. So every
  increasing event has at least its Bernoulli probability; in particular
  `theta_omega(t) >= theta_xi(t) >= K(t-p_c)` near `p_c`
  (`fpbs-transitive-sharpness-linear-lower-bound`).
* **(H2) Only Bernoulli finite clusters.** A.s., every finite cluster of
  `omega_t` is a cluster of `xi_t`. Hence
  `P(n <= |K^omega_o| < infinity) <= P_t(n <= |K_o| < infinity) <= e^{-c_t n}`
  for `t > p_c` (Hermon--Hutchcroft, arXiv:1904.10448, Theorem 1.1),
  `chi^f_omega(t) <= chi^f_t < infinity`, and
  `P(u <-> v in omega_t, |K^omega_u| < infinity) <= tau^f_t(u,v)`.
* **(H3) Density match.** `theta_xi(t) <= theta_omega(t) <= theta_xi(t) + f(t)`
  for `t in (p_c,t_1]`. With `f(t) = (t-p_c)^2`,
  `theta_omega(t)/theta_xi(t) -> 1`.
* **(H4) Local law match.** For `t in (p_c,t_1]`,
  `P(omega_t ∩ E(B_{R(t)}(o)) ≠ xi_t ∩ E(B_{R(t)}(o))) <= f(t)`, so the two
  ball laws are within total variation `f(t)`.
* **(H5) Unbounded two-point function.** For `t > p_c`,
  `P(u <-> v in omega_t) >= theta_xi(t)^2` for all `u,v`, and
  `||T^omega_t||_{2->2} = infinity`.

**Corollary (obstruction).** The graphs of Corollary C of
`fpbs-soft-collapse-iff-invariant-sparse-spines` have a genuine window
`p_c < p_u`: `T_3 x Z`, closed hyperbolic mapping tori of pseudo-Anosov
surface maps (where even `||T_{p_c}||_{2->2} < infinity`), and `F_2 x Z` with
the Pak--Smirnova-Nagnibeda generating sets. Each carries such a family for
every choice of `f` and `R`. Hence no argument proves `p_c < p_u` if its inputs
are only:

1. facts about Bernoulli percolation at `p <= p_c` (sharpness, the critical L2
   bound, critical no-percolation, critical walk correlation);
2. for `t > p_c`: invariance, ergodicity, insertion tolerance, a monotone
   coupling agreeing with the standard one up to `p_c`, and uniqueness;
3. Hutchcroft-type **supercritical sharpness**: the exponential finite-cluster
   tail, finite truncated susceptibility, truncated two-point bounds, and more
   generally every upper bound `E[F(K_o); |K_o| < infinity] <= B(t)` with
   `F >= 0` (since `{K^omega_o = H}` is contained in `{K^xi_o = H}` for every
   finite `H`);
4. **lower** bounds on increasing events from Bernoulli (the mean-field bound
   `theta >= K(t-p_c)`, FKG lower bounds for connections through `xi_t`);
5. the value of `theta` and the ball laws of `xi_t` at radii `R(t)`, known to
   any accuracy `f(t)` fixed in advance.

**Exact failing step.** The class of "under collapse, uniqueness at
`t ↓ p_c` forces a lower bound on a finite-cluster observable, or an excess of
`theta`, or a local anomaly" arguments dies here. The family is unique above
`p_c`, but its finite clusters are a subfamily of the Bernoulli ones and its
density and ball laws are as close to Bernoulli as prescribed. Every surviving
proof must use, for some `t > p_c`, an **upper** bound on an increasing
connection event at unbounded range: for example decay of `tau_t(u,v)`, BK or
Russo for increasing events, or independent sprinkling between distant
regions. It could also use mixing or deletion tolerance, which this family
lacks. In ell2 terms: `||T_{p_c}||<infinity` gives `||T_t||<infinity` for
`t>p_c` only through such a product-structure step. The family shows that the
finite-cluster part `tau^f_t`, which Hermon--Hutchcroft control, carries no
information about the infinite-cluster part `T_t - tau^f_t`.

What remains open: extending the spine hypothesis to every fixed-price-one
group, as for the parent obstruction. The coset-bypass criterion announced on
the live bus (wreath products `A wr_X Q`) would extend this theorem verbatim,
since the proof uses only the existence of spines.
