---
rg: 2
id: reading-model-entropy-certificates-are-soficity
kind: claim
title: Double-count entropy certificates for Bernoulli configurations work on a group exactly when it is sofic
distinct_from:
  sofic-radical-localizes-bernoulli-deficit-witnesses: that proves sofic models certify Phi >= log q, so witnesses live on nonsofic subgroups; this shows the same count run on arbitrary non-bijective, inconsistent, partial finite models has tightness exactly equal to soficity, so no weaker finite structure helps on a nonsofic host.
  bernoulli-rokhlin-deficit-has-a-finitary-witness: that reduces Rokhlin-maximality to Phi >= log q over finite configurations; this bounds what one proof technique for that inequality can reach.
artifacts:
  - research/artifacts/reading-model-certificates-force-soficity-2026-09-17.md
---

Let `K` be a finitely generated group with ball `B_r`, and let `c = (k,E,F,psi)` be a
configuration as in [[bernoulli-rokhlin-deficit-has-a-finitary-witness]], with pattern
`P = FE ∪ {1}` and `Y = psi(x|_E)`.

A **reading model** of `(E,F)` is any finite data: sites `M`, codes `N`, maps
`tau_e : N -> M` and `sigma_f : M -> N`, with no bijectivity or relation required.
A site `v` is good if `fe -> tau_e(sigma_f(v))` is a well-defined, injective chart of `P`.
The quality is `mu = |N'|/|M_g|`, where `M_g` is the set of good sites and `N'` is the set of codes they use.

1. **Certificate (Lemma A).** `k Phi(c) >= k log q - (mu - 1) H(Y)` for every reading model.
2. **Forcing (Lemma B).** If `B_r ⊆ E ∩ F`, then `mu >= 1`, and the model yields an
   `(r, (1+b) b^2 (mu-1))`-sofic approximation of `K` on `M_g`, where `b = |B_r|`.
3. **Theorem.** The following are equivalent:
   - `K` is sofic;
   - `inf mu = 1` over reading models of `(B_r,B_r)`, for every `r`;
   - Lemma A certifies `Phi >= log q` for every configuration of `K`.
4. **Obstruction.** If `K` is nonsofic, for instance the finitely generated nonsofic
   `EL_D(R) <= L_(F_2)(1,2)^x` of [[openai-leavitt-unit-nonsofic]], there are `r_0` and `eta_0 > 0`
   such that every configuration with `B_(r_0) ⊆ E ∩ F` has only
   `Phi >= log q - eta_0 H(Y)/k` from this class. These configurations extend all
   configurations on `B_(r_0)`, and extension only lowers `Phi`.

Every member of the class dies at step 1 of Lemma B:
- a tight double count plus the unit incidences `f f^-1 = 1` make every code read back to one site per slot;
- fullness makes the local charts consistent;
- consistency makes the reading maps near-permutations.

The class covers Gromov--Weiss counting, Følner windows, partial actions, pattern-local models and models with any boundary.
It does not cover linear (dimension) models, Hilbert--Schmidt volume counts, non-product label measures,
or limit functionals that are not one double count.

**ESTABLISHED 2026-09-17** by [[reading-model-entropy-certificates-are-soficity-proof]].
