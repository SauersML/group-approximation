---
rg: 2
id: fpbs-gap-window-fibre-mass-in-fourier-algebra
kind: claim
title: Below the relative threshold of a normal subgroup, the infinite-cluster fibre mass is a diagonal coefficient of the regular representation of the quotient
distinct_from:
  fpbs-relative-threshold-is-quotient-l2-threshold: that is Claim E, boundedness of convolution by sigma_p on l2(Q) below p_c(N;G); this is membership of sigma_p in the Fourier algebra A(Q), which Claim E implies (part 5 of fpbs-fibre-mass-positive-definite-in-gap-window) and which is not known to imply Claim E.
  fpbs-fibre-mass-positive-definite-in-gap-window: that proves sigma_p is positive definite (in B(Q)^+) and its finite-cluster part lies in A(Q); this asks for the infinite-cluster part, which is exactly the part that proof cannot reach.
  fpbs-two-point-in-fourier-algebra-near-pc-universal: that asks for tau_p in A(Gamma) at parameters decreasing to p_c; this is a statement about the fibre-summed kernel on the quotient Q = Gamma/N, on the whole window below p_c(N;G), and it is implied by Claim E, not by p_c < p_(2->2).
  fpbs-tree-product-fibre-square-root-law-below-relative-threshold: that is the summable square-root law, equivalent to Claim E on tree products; on those graphs this implies only the pointwise law f_p(n) <= (1 + n(k-2)/k)(k-1)^(-n/2) f_p(0).
---

**OPEN.** Notation as in `fpbs-fibre-mass-positive-definite-in-gap-window`.

**Claim E1.** For every finitely generated `Gamma`, finite symmetric
generating set `S`, infinite normal subgroup `N` and `p < p_c(N;G)`, there is
a Hilbert space `H` and a vector `xi in l2(Q) ⊗ H` with

```text
sigma^inf_p(q) = <xi, (rho ⊗ 1)(q) xi>     for all q in Q,
```

where `rho` is the right regular representation of `Q = Gamma/N`.
Equivalently, by part 4 of that node, `sigma_p` is such a diagonal
coefficient. By the standard description of `A(Q) ∩ P(Q)`, this is the
statement that `sigma_p` lies in the Fourier algebra `A(Q)`.

**Position in the decomposition of Claim E.**

```text
Claim E (||sigma_p||_Q < infinity below p_c(N;G))
   ==>  E1 (sigma_p in A(Q) below p_c(N;G))                         [part 5, proved]
   ==>  sigma_p in B(Q)^+, maximal at e, finite part in A(Q)        [parts 1-4, proved unconditionally]
```

- **E1 can fail on its own, and a failure refutes Claim E.**
- **The upgrade U: E1 ⇒ E can fail on its own.** A positive definite
  function in `A(Q)` need not be a bounded convolver. For example, on `Z`
  take `eta` in `l2` with `|eta^|^2` integrable but unbounded, and consider
  `eta * eta~`. For `sigma_p` itself, U is open.

**Where it is known.**

- For `p < p_c(G)` there is no infinite cluster, so `sigma^inf_p = 0`.
- It holds wherever Claim E is known: amenable quotients (C3 of the Claim E
  node, subject to the caveat recorded there) and every pair covered by an
  established instance of E.
- On tree products `T x H` it holds for all `p < p_t(G,Gamma_xi)`, by
  `fpbs-tree-product-fibre-operator-is-half-tilted-susceptibility` and part
  5. It is open on `[p_t, p_c(N;G))`.

**Falsifiable consequence (tree products).** By part 6 of the positive
definiteness node, E1 implies, for every `p < p_c(N;G)`,

```text
f_p(n) <= (1 + n(k-2)/k) (k-1)^(-n/2) f_p(0),     that is, beta_fib(p) >= 1/2.
```

The finite-cluster part obeys this bound unconditionally. So a single `p`
below `p_c(N;G)` on `F_2 x F_2` (product generators), where the
infinite-cluster fibre mass decays at a rate `(k-1)^(-beta n)` with
`beta < 1/2`, kills E1 and Claim E together. The mean-field calibration in
`fpbs-tree-product-fibre-square-root-law-below-relative-threshold` has fibre
rate exactly `1/2` at its threshold, so it is consistent with E1.

**Invariant.** The singular mass
`s_Q(p) = dist_(B(Q))(sigma_p, A(Q))`.

- By parts 3 and 4, `s_Q(p) <= ||sigma^inf_p||_B = sigma^inf_p(e)`, and
  `s_Q(p) = 0` for `p <= p_c`.
- E1 is `s_Q = 0` on `[0, p_c(N;G))`.
- On tree quotients, a nonzero `s_Q(p)` for radial `sigma^inf_p` means a
  spherical component in the complementary series.

**Class kill (calibration, not load-bearing).** Let `phi_z`, with
`0 < z < 1/2`, be the complementary-series spherical functions of the
`k`-regular tree group. They are classical (Figà-Talamanca–Nebbia; Cartier).
Each `phi_z` is:

- positive;
- radial;
- positive definite;
- equal to `1` at `e` and maximal there;
- not summable;
- decaying like `(k-1)^(-z n)`.

So `phi_z` has every property of `sigma^inf_p` proved so far: parts 1 and 3,
finiteness at `e`, and divergence of `sum_q`, since `chi_p = infinity` in the
window. Yet it violates the bound above. Hence no argument that uses only
these properties of the fibre kernel proves E1. It needs event-level input:
an equivariant square-root vector for the infinite-cluster part. The
probability-weighted root of the positive definiteness proof is not
equivariant, and its equivariant choice would give the weight `|C| = infinity`
(Step 4 of that route).

**Smallest open case.** `F_2 x F_2` or `(Z/2)^{*3} x (Z/2)^{*3}` with product
generators, `N` the second factor, and `p in [p_t, p_c(N;G))`.
