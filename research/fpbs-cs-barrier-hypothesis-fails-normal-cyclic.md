---
rg: 2
id: fpbs-cs-barrier-hypothesis-fails-normal-cyclic
kind: claim
title: On every Cayley graph of a group with an infinite cyclic normal subgroup, both abstract hypotheses of Choi-Seo's L2 framework fail
distinct_from:
  fpbs-cs-set-family-hypothesis-fails-infinite-centre: that kills only the set-family hypothesis for (Gamma1), only for groups with infinite centre, and leaves (Gamma2) and F_2 x D_infinity open; this kills the roughly-branching-barrier hypothesis for (Gamma2) and the set-family hypothesis for (Gamma1) on every group with an infinite cyclic normal subgroup, central or not, including F_2 x D_infinity.
  fpbs-hyperbolic-quotient-far-halfspace-share: that asks for a vanishing cluster share on fibre-saturated far halfspaces and records that lifted barriers are heuristically too big; this is a theorem that no uniformly roughly branching nested barrier family reaches any set touching the fibre line, and it proves nothing about the share itself.
  fpbs-fibre-bubble-forces-mean-field-susceptibility: that is a fibre-counting substitute for Hutchcroft's supporting sets over hyperbolic quotients; this proves that a substitute is forced, since the Choi-Seo hypotheses are false on the whole normal-cyclic class.
  fpbs-seifert-fibred-every-generating-set: that is the open threshold statement for Seifert-fibred groups; this is an obstruction to one proof method on that class and proves nothing about thresholds.
artifacts:
  - experiments/fpbs-normal-cyclic-barrier-2026-09-17/check_normal_cyclic_barrier.py
  - experiments/fpbs-normal-cyclic-barrier-2026-09-17/output.txt
  - research/artifacts/fpbs-acylindrical-l2-gap-2026-09-16.md
---

**ESTABLISHED.** Proof route: `fpbs-cs-barrier-hypothesis-fails-normal-cyclic-proof`.

**Statement.** Let `G` be finitely generated, `S` a finite symmetric
generating set, and suppose `G` has an infinite cyclic normal subgroup
`Z = <z>`. Then on `Cay(G,S)`:

* **(A)** The hypothesis of Choi–Seo Theorem 2.17 (arXiv:2508.08932v2; TeX
  label `thm:hutchcroftIotaGen`, CS6 in the artifact) fails. No `r > 0` and no
  families `S_D`, `G_(D,E)`, `H_D` satisfy its conditions (1)–(3) together
  with its magic-lemma condition. It already fails at `epsilon = 1/2`, for
  every `D > K := #B(r) #B(r + |z|_S)` and every large enough `E`.
* **(B)** The hypothesis of Choi–Seo Theorem 2.9 (`thm:hutchcroft1plus2`, CS4)
  fails for every family `{H(g)}` and every radius `R`. A witness is
  `A = {z^j : |j| <= L} ∪ z^L B(R) ∪ z^(-L) B(R)` with `L = 2 #B(R)`.
* **(C)** The core lemma, which carries the invariant. If `B'` is the core of
  an `r`-roughly branching set (Definition 2.13(2)), then `B'` meets every
  coset `Z t` in at most one point. Hence an `r`-roughly branching set meets
  the tube `N_c(Z)` in at most `#B(r) #B(r+c)` points.

**Class covered.** It contains:
* `F_2 x Z` and `F_2 x D_infinity`, where `z` is the translation (normal but
  not central);
* `Z ⋊ F_2` with a generator inverting `z`;
* every closed Seifert-fibred 3-manifold group with infinite `pi_1`, via the
  regular fibre;
* braid groups, via the centre;
* free-by-cyclic groups `F_n ⋊_phi Z` with `phi` of finite order in `Out`;
* every central extension by `Z`.

By Remark R1 in the proof route, it also contains every group with an infinite
virtually cyclic normal subgroup. For the free-by-cyclic case, the centralizer of `F_n` (`n >= 2`) is normal,
meets `F_n` trivially and contains a power of the stable letter times an
element of `F_n`, so it is infinite cyclic. Choi–Seo say their method does not
handle `F_2 x Z`, and they pose `F_2 x Z` (Question 1.3), 3-manifold groups and
free-by-cyclic groups as open questions. This node locates the exact point
where the method breaks on all of them.

**The obstruction, as a class statement.**
* **Invariant:** the fibre-coset multiplicity of a roughly branching core. It
  equals 1 on every coset of `Z` (part C). For comparison, `{a^m b}` in `F_2`
  meets a tube around the non-normal subgroup `<a>` in infinitely many points.
* **Failing step:** the nested-barrier capacity bound (Lemmas 2.12 and 2.14,
  used in the proof of Theorem 2.17). It certifies
  `E_p #(C(id) ∩ H) <= M chi_p / D` only when there are `D` disjoint barriers
  `B_1, ..., B_D` inside one uniformly `r`-roughly branching set. If `H`
  contains even one point of `Z`, the fibre path from `id` to that point
  crosses every `B_i` inside `N_(|z|)(Z)`, so `D <= K(r)`.
* **Consequence:** barrier capacity never makes a set touching the fibre line
  carry less than a fixed share `M/K` of `chi_p`. The `(Gamma2)` test sets
  `A = {z^0, ..., z^(L-1)}` lie on the line, so every magic-lemma cover fails.

Every proof of `(Gamma2)` of the form "cover `a^(-1)A` up to `N` points by sets
certified small by uniformly roughly branching nested barriers" dies at this
step on this class. Part (B) is the analogous statement for supporting-set
proofs of `(Gamma1)`.

**Scope and limits.**
* This obstructs a method, not a conclusion. `(Gamma1)` and `(Gamma2)` are
  equivalent to `p_c < p_(2->2)` (artifact, Remark A.1), and neither is
  claimed false here.
* It does not reach normal subgroups without a normal cyclic subgroup, such as
  `Z^2 ⋊ F_2` with an irreducible action, lamplighter-normal subgroups, or
  products `F_2 x K` with `K` amenable and torsion. There, the `k = 2`
  collision of Lemma 1 is not available, and `(Fs)^k` is a twisted sumset
  whose growth is not controlled here. The counting
  version (Remark R2 of the route) gives
  `#(B' ∩ Y) <= lim_k (#Y^k)^(1/k)` for every finite `Y`. That is the precise
  test for extending the obstruction.
* Consistent with `fpbs-fibre-bubble-forces-mean-field-susceptibility`, any
  route through `p_c < p_(2->2)` on this class must count fibres or use
  another non-barrier mechanism.
