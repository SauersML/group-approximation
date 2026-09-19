---
rg: 2
id: fpbs-tree-product-fibre-square-root-law-below-relative-threshold
kind: claim
title: On a tree times a nonamenable Cayley graph, below the relative threshold of the second factor the fibre masses decay at least at the square-root rate of the tree
distinct_from:
  fpbs-tree-product-fibre-operator-is-half-tilted-susceptibility: that proves the fibre operator norm equals chi_(p,1/2) and that this law is equivalent to Claim E on tree products; this is the open law itself, for nonamenable H, the only case left open there.
  fpbs-tree-projected-square-root-fibre-law-below-pu: that is an l^(2+) hitting-probability law below p_u over an amenable normal kernel; this is a first-moment fibre-mass law below p_c(H;G) for nonamenable H, where p_c(H;G) is not p_u.
  fpbs-relative-threshold-is-quotient-l2-threshold: that is Claim E on every pair; this is Claim E restricted to T x H with product generators, in its equivalent summability form.
  fpbs-percolation-kesten-normal-gap: that is the gap p_c < p_c(N;G); on these graphs the gap is proved, and this asks for the upper identification p_c(N;G) <= p_t instead.
---

**OPEN.**

**Setting.** As in
`fpbs-tree-product-fibre-operator-is-half-tilted-susceptibility`:

- `G = T x H = Cay(Lambda x H_grp, S_Lambda ⊔ S_H)`, where
  `Cay(Lambda,S_Lambda)` is the `k`-regular tree, `k >= 3`;
- `N = {1} x H_grp`;
- `f_p(n) = E_p|K_o ∩ ({v} x H_grp)|` for `|v| = n`.

Here `H_grp` is **nonamenable**.

**Claim.** For every `p < p_c(N;G)`,

```text
sum_(n>=1) n (k-1)^(n/2) f_p(n) < infinity.
```

**Why it matters.** By part 3 of the node above, this is equivalent to Claim E
of `fpbs-relative-threshold-is-quotient-l2-threshold` on `(G,N)`, and to
`p_c(N;G) = p_t(G,Gamma_xi)`. For amenable `H_grp` it holds, via
Hutchcroft--Pan. A failure would be a counterexample to Claim E on a
product graph, with `p_t < p_c(N;G)`. In the natural exponent
`beta_fib(p) = -lim sup_n log f_p(n) / (n log(k-1))`, the claim asks for
`beta_fib >= 1/2` throughout `p < p_c(N;G)`, with the boundary case summable.

**Smallest open case.** `F_2 x F_2`, or `(Z/2)^{*3} x (Z/2)^{*3}`, with
product generators.

## Attempts

* **Transfer of the Hutchcroft--Pan proof (2026-09-18, swarm-0917 w12,
  sketch, not load-bearing).** This reads arXiv:2412.15895v1, Section 2,
  lemma by lemma, replacing `p_u` by `p_c(N;G)`.
  * **What appears general.** The steps below appear to use no amenability
    once `p_u` is replaced by `p_c(N;G)`. None of them has been rewritten
    here in full.
    * Lemma 2.2: supermultiplicativity of the slab fibre-hitting
      probability `P_p(n)`, giving the rate `beta*_p`.
    * Lemma 2.3: `beta*_(p^theta) <= theta beta*_p`, so `beta*` is strictly
      decreasing where it is positive.
    * Lemma 2.5: `E_p(n) <= C(n+1) P_p(n)`. It uses Lemma 2.6, which is
      relative sharpness (`fpbs-hp-relative-sharpness`) plus their
      companion paper's Lemma 5.5, and holds below `p_c(N;G)`.
    * Lemmas 2.10 and 2.11: the Hammersley--Welsh bound
      `chi_(p,1/2) <= (E|K_o ∩ N|)^2 exp[2 sum_n (k-1)^(-n/2) D_p(n)]`,
      with `D_p(n) = (k-1)^n E_p(n)`. This uses BK and the tilted mass
      transport principle only.

    Granting these, the claim would follow from the **backscattering bound**
    `beta*_p >= 1/2` for all `p < p_c(N;G)`. Strictness then comes from
    Lemma 2.3 applied at some `p' in (p, p_c(N;G))`.
  * **The failing step: Lemma 2.8.** It says that the point-to-point slab
    probability `Q_p(n)`, of hitting the fibre at the specific point
    `(v,o_H)`, has the same rate as the fibre probability `P_p(n)`. The proof
    embeds a branching random walk on `H` and uses "Since H is amenable, it
    follows by Kesten's theorem [29] that P^{2r}(o_H,o_H) = e^{-o(r)}". For
    nonamenable `H` this return probability decays exponentially.
    Lemma 2.9 (backscattering via twin processes `Y^{h,g}`, FKG, uniform
    survival and sprinkling) runs on point-to-point events, and so it
    transfers only in the weaker form: `gamma*_p < 1/2` implies
    `p >= p_c(N;G)`, where `gamma*_p` is the rate of `Q_p(n)`.
  * **Invariant.** The discrepancy `gamma*_p - beta*_p >= 0` between the
    point rate and the fibre rate. It is driven by the return deficit of `H`,
    and it vanishes when `H` is amenable. The transferred HP argument proves
    the claim exactly on the set of `p` where `gamma*_p` and `beta*_p` lie on
    the same side of `1/2`. A proof along these lines must produce a
    backscattering mechanism that returns to a *fibre*, not to a point.
  * **Mean-field calibration (heuristic).** Model `T_4 x T_4` by branching
    random walk with mean `m` per generation, with the uniform step on the 8
    generators. See Part 3 of
    `experiments/fpbs-tree-product-fibre-tilt-2026-09-17/check_fibre_tilt.out`.
    * The projection to the tree factor is a lazy walk with spectral radius
      `1/2 + sqrt3/4 = 0.93301`. Fibre occupation is finite iff
      `m < m_* = 1.07180`, and at `m_*` the fibre rate is exactly `1/2`. So
      `E` holds in mean field.
    * The point-occupation threshold is `1/rho(T_4 x T_4) = 2/sqrt3 = 1.15470`.
    * So point-to-point estimates certify relative percolation only at
      `m >= 1.1547`, strictly above `m_* = 1.0718`. The window
      `(1.0718, 1.1547)` is invisible to twin-process backscattering even in
      mean field. This is the quantitative form of the kill above.
* **Other routes tried (dead, recorded briefly).**
  * **Cauchy--Schwarz on the sphere.** This bounds `sum_(S_n) sigma g` by
    `(sum_(S_n) sigma^2)^(1/2) (sum_(S_n) g^2)^(1/2)`. By the tilted mass
    transport principle, `sum_(S_n) g^2 = |S_n|`. Since `sigma = f_p(n)` on
    `S_n`, the bound is `|S_n| f_p(n)`, and summing gives
    `chi_(p,1/2) <= chi_p`. This is finite only below `p_c`, so the tilt is
    lost entirely.
  * **Twin processes with central displacement.** The central-translate trick
    of `fpbs-tree-projected-square-root-fibre-law-below-pu` needs `N`
    central. Here that means `H_grp` abelian, hence amenable, which is the
    solved case. For nonamenable `H_grp` the trick does not apply, and in any
    case the obstruction is the point-to-point return in `H`, not the
    pairing of translates.
  * **Second moment with same-fibre siblings.** Lower-bounding
    `E|K_o ∩ N|` by siblings meeting in a common fibre requires those
    siblings to be positively correlated at the fibre level. FKG gives only
    the product of point events, so this returns to `gamma*`.
