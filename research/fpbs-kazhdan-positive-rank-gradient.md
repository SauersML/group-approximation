---
rg: 2
id: fpbs-kazhdan-positive-rank-gradient
kind: claim
title: An infinite Kazhdan group has a Farber chain of positive rank gradient
root: true
---

OPEN counterexample-construction target. No such group or chain is constructed. It is kept separate from the positive universal fixed-price claim.

## Attempts

* **Build the certificate from mod-`l` homology.** Section 4 of
  `research/artifacts/fpbs/creative-branches.md` records a sufficient
  condition: a prime `l` and a Farber chain `Gamma_n` with
  `liminf_n dim_(F_l) H_1(Gamma_n;F_l)/[Gamma:Gamma_n] > 0`, since
  `d(Gamma_n)` is at least that dimension. Abert--Nikolov then makes the
  profinite boundary action have cost `1+lim_n (d(Gamma_n)-1)/[Gamma:Gamma_n]`,
  strictly above one, and `fpbs-kazhdan-groups-have-cost-one` supplies a
  cheaper action, so `fpbs-kazhdan-rankgradient-counterexample-reduction`
  closes. The certificate is stated with mod-`l` coefficients, not rational
  ones. **Where it dies:** no group and no chain are constructed. A candidate
  must hold three properties at once -- property (T), essential freeness of
  the profinite boundary action (for instance a normal chain with trivial
  intersection), and a genuinely positive asymptotic lower bound -- and the
  note states that large homology at finitely many levels, a chain that is not
  Farber, or a weighted presentation deficiency supplies none of the three.
* **Weaken the attainment requirement.** An earlier worry was that
  Hutchcroft--Pete give an infimum rather than a minimum. **Resolved, and it
  does not help:** infimal cost one already produces an action strictly
  cheaper than a positive-gradient boundary action, so no attainment theorem
  is needed. The difficulty is entirely in the construction, not in the
  comparison.
* **Look inside the known Kazhdan groups of this repository.** The property
  (T) region here is built for operator-algebraic questions and records
  finite generation (`discrete-kazhdan-groups-are-finitely-generated`) and
  residual-finiteness obstructions, not rank gradients of Farber chains.
  Nothing in it supplies a chain with the required asymptotic lower bound.
* **Force the gradient with a presentation of positive power p-deficiency**
  (Schlage-Puchta, Osin). Such a presentation gives positive `p`-gradient even
  with infinitely many relators or with torsion, and the residual pro-`p`
  image of a Kazhdan example would satisfy this claim
  (`fpbs-kazhdan-gradient-via-power-p-deficiency`). **Dead:**
  `fpbs-power-p-deficiency-excludes-property-t` proves that no such group is
  Kazhdan. Openness of (T) gives a Kazhdan finitely presented truncation of
  positive power deficiency, and Lackenby makes that truncation `p`-large.
  Weighted Golod-Shafarevich presentations are not excluded, since Kazhdan
  Golod-Shafarevich groups exist, but they give no lower bound on ordinary
  rank.
* **Necessary condition for the mod-`l` certificate: exponential subgroup
  growth.** Suppose `dim H_1(Gamma_n;F_l) >= c[Gamma:Gamma_n]`. The index-`l`
  normal subgroups of `Gamma_n` give at least `(l^(c m_n)-1)/(l-1)` subgroups
  of index `l m_n` in `Gamma`, where `m_n=[Gamma:Gamma_n]`. So
  `limsup_N log s_N(Gamma)/N >= c log(l)/l > 0`. Any candidate must therefore
  be a Kazhdan group of at least exponential subgroup growth. Ershov's survey
  (IJAC 2012, Section 14, discussion of Problem 6) records that no such
  Kazhdan group was known, and expects that the Kazhdan Golod-Shafarevich
  groups have subexponential growth. The status after 2012 was not rechecked
  here.
* **Where a candidate can still come from.** It must be residually finite and
  infinitely presented whenever the chain is a cofinal `p`-chain: for a
  finitely presented Kazhdan group, positive `p`-gradient contradicts Lackenby
  just as above. Non-cofinal chains and non-`p`-power chains are not excluded.
  Lackenby's (tau) dichotomy (arXiv:math/0509036) allows linear mod-`p` growth
  along a chain with respect to which (tau) holds.
* **Use the Ershov--Jaikin-Zapirain Kazhdan groups of positive weighted
  deficiency.** Read from source: Ershov and Jaikin-Zapirain, *Groups of
  positive weighted deficiency and their applications*, arXiv:1007.1489.
  The introduction notes that groups of positive weighted deficiency can have
  property (T), by Ershov's earlier work, and deduces residually finite
  locally zero-one Kazhdan groups and a LERF Kazhdan group (Corollary
  `longreid`). **Where it dies:** the subgroup estimates in that paper are
  weighted. Its weighted Schreier formula (Section 3, subsection on the
  `W`-index) bounds weighted rank against the `W`-index rather than the
  ordinary index. No statement there bounds `d(L)` or `dim H_1(L;F_p)` below
  linearly in the ordinary index; the phrase rank gradient occurs only in the
  bibliography.
* **Recheck the exponential-subgroup-growth status after 2012.** OpenAlex
  searches run on 2026-09-12 (Kazhdan groups with exponential subgroup growth;
  positive rank gradient, `p`-gradient or mod-`p` homology growth under
  property (T)) returned no construction of either kind. That is search
  evidence, not a verified status. The lower bound read from source is
  Theorem `subgpgrowth` in Jaikin-Zapirain's appendix on subgroup growth to
  Ershov, *Kazhdan quotients of Golod-Shafarevich groups*, arXiv:0908.3734: a
  generalized Golod-Shafarevich pro-`p` group `G` has
  `log_2 log_2 a_m(G) >= (log_2 m)^beta` for infinitely many `m` and some
  `beta>0`, where `a_m` counts open subgroups of index `m`. **Where it dies:**
  the certificate above forces `log_2 log_2 a_m(Gamma) >= log_2 m - C` along
  `m=l[Gamma:Gamma_n]`, and `(log_2 m)^beta` is far below that. The known
  bound neither supplies nor excludes a candidate.
* **Replace the chain by the `p`-gradient of the group.** Ershov's survey
  (Definition of the `p`-gradient and the Remark after it, Section on power
  `p`-deficiency) sets `RG_p(G)=inf_H (d_p(H)-1)/[G:H]` over subnormal
  subgroups of `p`-power index and records `RG_p(G)=RG_p(G')` for the image
  `G'` of `G` in its pro-`p` completion. So any infinite Kazhdan group `Gamma`
  with `RG_p(Gamma)>0` gives a counterexample, with no separate Farber check.
  Positive `p`-gradient forces an infinite pro-`p` completion, since otherwise
  the kernel `K` of `Gamma` onto that finite `p`-group has `d_p(K)=0` (a
  `p`-quotient of `K` would give, through its core, a larger `p`-quotient of
  `Gamma`) and `RG_p(Gamma) <= -1/[Gamma:K]`. Then `Gamma'` is an infinite
  residually-`p` Kazhdan quotient. For open normal subgroups `U_n` of the
  completion with trivial intersection, `Gamma'_n=Gamma' cap U_n` is a normal
  chain with trivial intersection, hence Farber, and
  `d(Gamma'_n)-1 >= d_p(Gamma'_n)-1 >= RG_p(Gamma)[Gamma':Gamma'_n]`.
  **Where it dies:** this only moves the difficulty to `RG_p(Gamma)>0`. Such a
  `Gamma` must be infinitely presented, by Lackenby's theorem that a finitely
  presented group of positive `p`-gradient is large (survey, proof of
  Corollary `Puchta1`(b)). Finitely presented Kazhdan covers give nothing,
  because a quotient can have larger `p`-gradient than its cover: `Z x F_2`
  has `p`-gradient `0` (use `p^a Z x K` with `a` large), while `F_2` has
  `p`-gradient `1`.
* **Extract what property (T) forces on the mod-`p` classes.** Let
  `(S,kappa)` be a Kazhdan pair for `Gamma`, `U` a subgroup of finite index
  `N`, `P=Gamma/U`, and `c:Gamma->F_p[P]` a cocycle whose Shapiro image
  `f(u)=c(u)(U)` in `Hom(U,F_p)` is nonzero. Then some `s in S` has `c(s)`
  nonzero at no fewer than `kappa^2 N/4` points of `P`. Proof: with
  `e(a)=exp(2 pi i a/p)`, the formula `(rho(g)phi)(x)=e(c(g)(x))phi(g^-1 x)`
  defines a unitary representation on `l^2(P)`. It permutes the coordinate
  lines transitively, and `U` acts on the line at the coset `U` by the
  character `e(f)`, so `rho` is `Ind_U^Gamma e(f)` and has no invariant
  vector by Frobenius reciprocity. The Kazhdan inequality at the constant unit
  vector `v` gives `kappa^2 <= ||rho(s)v-v||^2 <= 4|supp c(s)|/N`. So along a
  certificate chain, `H^1(Gamma_n;F_p)`, realized as cocycles on `S x P_n`
  modulo coboundaries, has dimension at least `c N_n`, and every
  representative of a nonzero class has weight at least `kappa^2 N_n/4`.
  **Where it dies:** this is necessary structure, not an obstruction. Nothing
  read here excludes subspaces with both linear dimension and linear coset
  weight, so no contradiction follows.
