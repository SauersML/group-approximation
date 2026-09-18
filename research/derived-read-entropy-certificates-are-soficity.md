---
rg: 2
id: derived-read-entropy-certificates-are-soficity
kind: claim
title: Double-count certificates with arbitrary derived reads, linear or nonlinear and with approximate laws, work on a group exactly when it is sofic
distinct_from:
  reading-model-entropy-certificates-are-soficity: that treats counts whose codes read iid site labels through index maps with exact laws; this allows any probability space, reads that are arbitrary random variables (linear functionals, nonlinear or randomized functions) and TV-approximate local laws, and reduces them to reading models by pinning through the unit incidences.
  linear-sofic-groups-are-surjunctive: that asks whether linear soficity gives surjunctivity; this shows the per-site Shannon/dimension double count cannot use linear models beyond soficity, so a linear route must avoid per-site chain-rule accounting.
  sofic-radical-localizes-bernoulli-deficit-witnesses: that proves sofic models certify Phi >= log q; this bounds the widest per-site double-count class on nonsofic hosts.
artifacts:
  - research/artifacts/derived-read-count-certificates-force-soficity-2026-09-17.md
---

Let `K` be a nontrivial finitely generated group, and let `c = (k,E,F,psi)` be a configuration as in
[[bernoulli-rokhlin-deficit-has-a-finitary-witness]], with `Y = psi(x|_E)`.

A **derived-read model** with tolerance `epsilon <= 1/2` consists of:
- a probability space, site variables `Z_i` (`i` in `I`) and read variables `v_{u,e}` (`u` in `U`, `e` in `E`),
  all with values in `A^k`, and code variables `C_u = psi((v_{u,e})_e)`;
- maps `sigma_f : I -> U`;
- a set `V` of good sites with `(Z_i)_{i in V}` iid uniform, such that for each `i` in `V` the law of
  `(Z_i, (v_{sigma_f(i),e})_{f,e})` is within TV `epsilon` of the law of `(x(1), (x(fe))_{f,e})`.

Put `mu = |sigma_F(V)|/|V|`, and let `delta(epsilon) = 2(epsilon log(q^k |R|^|F|) + h(epsilon))`, where `R` is
the range of `psi` and `h` is the binary entropy.

1. **Certificate (Lemma A').** `k Phi(c) >= k log q - (mu-1) H(Y) - (mu+1) delta(epsilon)`.
2. **Pinning (Lemma P).** Suppose `B_r ⊆ E ∩ F`, `epsilon < 1/6` and `b^2(mu-1) < 1`, where `b = |B_r|`. Then every
   `sigma_g` (`g` in `B_r`) is injective on `V`. Each read of a full code equals, with probability at least
   `1 - epsilon`, a unique good site variable. These read-backs form a reading model of
   [[reading-model-entropy-certificates-are-soficity]] with good set `V_R ⊆ V`, where
   `|V_R| >= (1 - b^2(mu-1))|V|` and ratio `mu_R <= mu/(1 - b^2(mu-1))`. Hence `K` has an
   `(r, (1+b) b^2 (mu_R - 1))`-sofic approximation.
3. **Theorem D.** The following are equivalent:
   - `K` is sofic;
   - for every `r`, derived-read models of `(B_r,B_r)` exist with `epsilon -> 0` and `mu -> 1`;
   - Lemma A' certifies `Phi >= log q` for every configuration.
4. **Obstruction.** If `K` is nonsofic, for instance `EL_D(R)` of [[openai-leavitt-unit-nonsofic]], there are `r_0`
   and `eta_1 > 0` with the following property. On any host containing `K`, every derived-read certificate for a
   configuration with `B^K_(r_0) ⊆ E ∩ F` proves at most `Phi >= log q - min(eta_1 H(Y)/k, (1/3) log q)`.

**Where every member dies.** Every member dies at the pinning step. The unit incidence `g^-1 g = 1` puts `x(1)` among
the reads of `sigma_(g^-1)(i)`. So, whatever the reads compute, a good site's local law forces that read to equal
`Z_i`, and independence of the good sites converts equality in law into identity of indices. A tight count therefore
contains a reading model, and that dies at step 1 of reading-model Lemma B.

The class covers linear double counts over finite fields run over a linearly independent family of site
functionals, nonlinear, hashed and randomized reads, non-product ambient measures with independent good sites, and
approximate laws.

It does not cover:
- counts that bound `H(Z_V | codes)` globally, for instance by the codimension of a good subspace, without a
  per-site chain rule;
- approximately independent good sites;
- volume counts and multi-count limit functionals.

The first item is the rank-metric gap of [[site-pullbacks-are-discontinuous-in-the-rank-metric]].

**ESTABLISHED 2026-09-17** by [[derived-read-entropy-certificates-are-soficity-proof]].
