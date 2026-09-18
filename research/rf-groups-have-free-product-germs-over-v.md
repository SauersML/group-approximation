---
rg: 2
id: rf-groups-have-free-product-germs-over-v
kind: claim
title: Every finitely generated residually finite group G lies in a one-orbit finite germ extension of Thompson's V whose germ group at the singular point is G * Z
distinct_from:
  bhm-singfix-condition-forces-fp-germ-groups: that says Belk--Hyde--Matucci Theorem 2.1 needs finitely presented singular germ groups; this realizes every finitely presented residually finite group inside a finite germ extension of V whose singular germ group, G * Z, is finitely presented, so that necessary condition always holds.
  grigorchuk-groups-lie-in-one-point-germ-extensions-of-v: that computes the germ group W_ω x| Z of one explicit host, which fails to be finitely presented for aperiodic ω; this builds hosts for every residually finite group, with free-product germ groups.
  orbit-preserving-germ-corollary-extensions-of-v-are-rational: that shows hosts certified by Corollary 2.10, where (V)_p is normal in the germ group, are rational; here (V)_p = <t> is a free factor of the germ group, not normal, so that corollary does not apply and word problems are not forced to be easy.
  profinite-product-full-groups-have-no-fg-simple-hosts: that kills hosts using the profinite translation action plus independent expanding dynamics; this uses the finite quotients of G on the annuli of a point of V's Cantor set, where V's expansion does interact with them.
---

**ESTABLISHED** by `rf-free-product-germ-realization-proof` (lane proof, elementary; not
reviewed; no priority claimed).

**Setting.** `V` acts on `C = {0,1}^N`. Put `p = 0^∞`, `A_n = 0^n 1 C` for `n >= 0`, and
`α_n(w) = 0^n 1 w`. Let `τ ∈ V` be the zoom `0w ↦ 00w, 10w ↦ 01w, 11w ↦ 1w`, with germ
`t` at `p`. Let `G` be finitely generated and residually finite, and let
`G = N_0 >= N_1 >= ...` be finite-index normal subgroups with trivial intersection.

**Theorem.**
1. **Annular realization.** There are homomorphisms `ρ_n: G -> V`, each factoring through
   `G/N_n`, such that `ĝ(p) = p` and `ĝ(α_n(w)) = α_n(ρ_n(g)(w))` defines an injective
   homomorphism `G -> Homeo(C)`, `g ↦ ĝ`. Each `ĝ` preserves every `A_n` and is locally
   in `V` at every point except `p`.
2. **The host.** Let `Γ` be the full closure of `<V, Ĝ>`: all homeomorphisms that agree
   locally with `V` off finitely many points, with every germ in the groupoid generated
   by the germs of `V` and `Ĝ`. Then `Γ` is a finite germ extension of `V` in the sense of
   Belk--Hyde--Matucci, and `sing(Γ) = V·p`, one orbit of a rational point.
3. **Free-product germs.** The germ group of `Γ` at `p` is
   `(Γ)_p = <(Ĝ)_p, t> ≅ G * Z`, and already `<Ĝ, τ> ≅ G * Z` inside `Γ`.
4. So if `G` is finitely presented, the singular germ group of `Γ` is finitely presented.

**What residual finiteness buys.** Only item 1 uses it, through one fact: a finite group
acts on the Cantor set with a free clopen fundamental domain. That lets the finite images
`Q_j = ρ_j(G)` sit in ping-pong position in `V`, so `<Q_j : j >= 0> = *_j Q_j`. The zoom
conjugates the action on `A_n` to the action on `A_(n+1)`, so the copies `t^k Ĝ t^(-k)`
act on one deep annulus through the pairwise free groups `Q_(n-k)`. This makes the germ
group as free as possible.

**Consequences and limits.**
- The gate of `bhm-singfix-condition-forces-fp-germ-groups`, which stopped the Grigorchuk
  hosts and the shell envelopes, is passed for every finitely presented residually finite
  group, including the hard groups of Kharlampovich--Myasnikov--Sapir.
- It does not give Boone--Higman. Theorem 2.1 also needs the one-point group
  `SingFix_Γ({p},{p})` to be finitely presented, and for these hosts it is not
  (`annular-free-factor-germ-extensions-fail-bhm-singfix`). Whether `Γ` itself is
  finitely presented is not decided.
