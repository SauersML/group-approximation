---
rg: 2
id: fpbs-ideal-voronoi-descent-limit-exists
kind: claim
title: Every finitely generated infinite group has an ideal Voronoi descent map, a rootless geodesic-ray functional graphing in a free action weakly contained in Bernoulli
distinct_from:
  fpbs-hp-condensation-bernoulli-exit: that takes weak limits of the Hutchcroft--Pete percolation recursion; this takes the weak limit of nearest-nucleus descent maps of vanishing-intensity Bernoulli Voronoi tessellations, and records the functional graph rather than a percolation.
  fpbs-sparse-spine-cost-bound: that needs an FIID connected spine of small positive density; the limit object here has density-zero nuclei, lives only in the weak-containment closure of Bernoulli, and is not claimed to give any cost bound by itself.
---

**OPEN (written direct proof proposed in `fpbs-ideal-voronoi-descent-limit-exists-proof`; not yet fully refereed).**

**Construction.**
- Fix a finitely generated infinite group `Gamma`, a finite symmetric generating set `S` not containing `e`, a total
  order on `S`, and the word metric `d`.
- Let `(U(g), W(g))_{g in Gamma}` be iid uniform on `[0,1]^2`, and put `omega_eps = {g : U(g) < eps}`.
- For `x` in `Gamma`, the nucleus `p_eps(x)` is the point `p` of `omega_eps` minimising `(d(x,p), W(p))`
  lexicographically.
- The arrow `sigma_eps(x)` in `S ∪ {*}` is `*` if `x` is in `omega_eps`. Otherwise it is the least `s` in `S` with
  `d(xs, p_eps(x)) = d(x, p_eps(x)) - 1`.
- `nu_eps` is the law of `(sigma_eps(g), U(g), W(g))_g` on `K^Gamma`, where `K = (S ∪ {*}) x [0,1]^2`.

**Theorem.** There are `eps_n -> 0` with `nu_{eps_n} -> nu` weak-star, and every such limit has these properties.
1. `s_nu` is a free p.m.p. action of `Gamma` with `s_nu ≺ b_Gamma`, and its `[0,1]^2`-marginal is iid uniform.
2. Almost surely `sigma(g) != *` for every `g`, so the descent map has no roots.
3. Almost surely, for every `g`, the forward chain `g, g s_1, g s_1 s_2, ...` with `s_{k+1} = sigma(g s_1 ... s_k)`
   is a geodesic ray. In particular the functional graph has no cycles, and every component is infinite.

In the action, this is the Borel self-map `f(omega) = sigma(e)(omega)^{-1} . omega` of the orbit relation. It is a
candidate input for `fpbs-functional-contact-criterion`. Its cells are the classes of the tail relation of
`f`: two points are in the same cell when their chains eventually merge.

**Literature context, not used in the proof.**
- Fraczyk--Mellick--Wilkens, arXiv:2307.01194, abstract (read 2026-09-17): "Let $G$ be a higher rank semisimple real
  Lie group or the product of at least two automorphism groups of regular trees. We prove all probability measure
  preserving actions of lattices in such groups have cost one, answering Gaboriau's fixed price question for this
  class of groups."
- The same abstract says of the ideal Poisson--Voronoi tessellations used there: "these tessellations partition the
  space into ``horoball-like'' cells so that any two share an unbounded border."
- The discrete analogue on graphs appears in arXiv:2606.30517. There ideal Poisson--Voronoi tessellations are weak
  limits of Voronoi diagrams, Bernoulli nuclei give the same limit (their Lemma 4.9), and cells may have unbounded
  intersections (their Remark 2.7). That paper does not discuss cost.
- The present claim is a self-contained existence statement. It is not an identification with their object.

## Attempts

- **2026-09-17: written direct proof `fpbs-ideal-voronoi-descent-limit-exists-proof`, held at OPEN.** Two of three
  referee lenses returned survives (no failing step found: the one-step descent keeps the nucleus, the events "no
  root" and "chains are geodesic" are clopen cylinders passing to the weak-star limit, and the weak-containment
  closure argument is written inline). The third referee vote was lost, so the claim is not promoted to ESTABLISHED
  until a full referee panel survives. The proof file is kept as the attempt.
