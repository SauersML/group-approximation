---
rg: 2
id: fpbs-kazhdan-uniform-walk-decorrelation
kind: claim
title: On a Kazhdan Cayley graph walk connectivity equals theta squared on uniqueness plus a p-independent exponential error, so the green-visit and non-concentration kernels are equivalent to p_c < p_u there
distinct_from:
  fpbs-green-visit-criterion-implies-nonuniqueness: that is the universal direction A(p)<infinity implies nonuniqueness; this is the converse on Kazhdan groups, A(p) <= 2|S|/kappa^2 at every nonuniqueness parameter, including p_u.
  fpbs-pu-nonuniqueness-cannot-separate: that shows nonuniqueness at p_u does not separate the thresholds; here nonuniqueness at p_u on Kazhdan groups is recovered as a quantitative corollary, and the new content is the uniform decay rate and the kernel equivalences.
  fpbs-kazhdan-ergodic-percolation-disagreement-floor: that applies the Kazhdan inequality to L2 of the configuration space; this applies it to L2 of the cluster space, whose invariant vectors are computed by indistinguishability.
  fpbs-green-visit-criterion-universal: that is the open universal kernel; this shows that on every Kazhdan Cayley graph it is equivalent to p_c<p_u, hence no easier there.
  fpbs-pivotal-nonconcentration-universal: that is the open universal kernel NC; this shows that on every Kazhdan Cayley graph NC is equivalent to p_c<p_u.
---

**ESTABLISHED.** Let `Gamma` be an infinite group, `S` a finite symmetric
generating set, `G = Cay(Gamma,S)`, and let

```text
kappa = kappa(Gamma,S) = inf over unitary reps pi without nonzero invariant
        vectors, and unit v, of max_(s in S) ||pi(s)v - v||.
```

Assume `kappa > 0`. This holds for every finite generating set when `Gamma`
has Kazhdan's property (T). Put `eta = 1 - kappa^2/(4|S|) < 1`. Let `X^L_n` be
the lazy walk with step law `(delta_e + mu_S)/2`, independent of Bernoulli(`p`)
bond percolation. Let `a^L_n(p) = P_p(o <-> X^L_n)`, let
`theta(p) = P_p(o <-> infinity)`, and let `U_p` be the event (a.s. trivial)
that there is a unique infinite cluster.

**Theorem.** For every `p in [0,1]` and every `n >= 0`,

```text
theta(p)^2 1{U_p}  <=  a^L_n(p)  <=  theta(p)^2 1{U_p} + (1 - theta(p)^2 1{U_p}) eta^n.
```

**Corollaries.** Let `a_n`, `A`, `lambda` be the simple-walk quantities of
`fpbs-green-visit-criterion-universal` and
`research/artifacts/fpbs/exploration-pivotal-projections.md`, Section 6.

1. *Uniform truncated visit bound.* For every `p`,
   `sum_n (a^L_n(p) - theta(p)^2 1{U_p}) <= 1/(1-eta) = 4|S|/kappa^2`.
2. *No uniqueness at `p_u`, quantitatively.* `a^L_n(p_u) <= eta^n`. This
   recovers the second statement of Lyons--Schramm's Kazhdan corollary.
3. *Sharp kernel thresholds.* For `0 < p <= p_u`: `A(p) <= 2|S|/kappa^2`,
   `lambda_L(p) <= eta`, and `lambda(p) <= eta^2`. For `p > p_u`:
   `A(p) = infinity` and `lambda(p) = lambda_L(p) = 1`. So
   `p_A = sup{p : A(p) < infinity} = p_u`, and `p_u` is also the supremum of
   the parameters where the walk connectivity rate is below one.
4. *Kernel equivalences.* On every Cayley graph with `kappa(Gamma,S)>0`, the
   green-visit criterion (`A(p)<infinity` for some `p>p_c`), NC
   (`lambda(p)<1` for some `p>p_c`) and `p_c<p_u` are equivalent.
5. *Uniform jump.* The rate `lambda_L` jumps by at least `kappa^2/(4|S|)` at
   `p_u`. Under a hypothetical collapse `p_c = p_u`, the truncated walk
   connectivity `sum_n (a^L_n(p) - theta(p)^2)` stays at most `4|S|/kappa^2`
   for every `p > p_c`.

**What this kills.** On the whole Kazhdan class, including `SL_3(Z)` and every
infinite (T) group, the kernels at the tip of `fpbs-benjamini-schramm-universal`
(green-visit, NC, and IS through NC) are not weaker than `p_c<p_u`. A proof of
any of them on these graphs is a proof of `theta(p_u)>0` there, with no
intermediate slack. Two kinds of separation argument are dead on Kazhdan
graphs:

* arguments that show the walk-sampled correlation length diverges as
  `p` decreases to `p_c` from above;
* arguments that show `lambda_L` rises continuously to one at `p_u`.

**General-group form.** The proof is a spectral decomposition of `a^L_n` in the
cluster Koopman representation `L2(Y,m)`, where `Y` is the space of pairs
(configuration, cluster). For any Cayley graph, the Theorem holds with `eta`
replaced by the top of the spectrum of `pi_p(mu_L)` on the orthocomplement of
the invariant vectors. Property (T) makes that top uniform in `p`, and it is
the only place (T) is used.

DERIVATION
fpbs-kazhdan-uniform-walk-decorrelation-proof
