---
rg: 2
id: sofic-torus-c2-reduces-to-rectangular-small-fibres-proof
kind: route
title: Freeze the uncertified vertices of a sofic model; the pull-back certificate makes the rest a local rectangular map, and Sylvester's inequality turns its rank into C2
target: sofic-torus-c2-reduces-to-rectangular-small-fibres
requires:
  - torus-automata-with-regular-degree-are-surjective
artifacts:
  - research/artifacts/sofic-torus-rectangular-small-fibre-2026-09-19.md
  - research/artifacts/lef-torus-small-fibre-2026-09-18.md
---

Full proof in `research/artifacts/sofic-torus-rectangular-small-fibre-2026-09-19.md`,
Sections 1–3. [LEF] is `research/artifacts/lef-torus-small-fibre-2026-09-18.md`.

1. **Data from `tau` (every group).** [LEF] Lemmas A and B give:
   - a finite `W` and `eta > 0` such that `eta`-closeness of `tau(x), tau(y)` on `W`
     gives `|x_1 - y_1| < 1/16`;
   - a finite `F` and a memory-`F` map `mu'` within `eta/3` of `ev_1 o tau`, with
     degree data `D`.

   Put `K = max(|W|, |F|)`.
2. **Model map.** For `sigma: G -> Sym(V)`, put
   `tau_sigma(u)_q = mu'((u_(sigma(f)^-1 q))_(f in F))`. With
   `sigma(a)_(v,u) = sum { a_g : u = sigma(g)^-1 v }`, the pull-back `tau_sigma^*` is
   right multiplication by `sigma(D)`. Row `v` of `sigma(a) sigma(b)` equals row `v`
   of `sigma(ab)` wherever `sigma` is multiplicative on `supp a × supp b` at `v`.
3. **Pull-back certificate (Lemma P).**
   - *Certified vertices.* Call `v` certified when `wf = w'f'` implies
     `sigma(f)^-1 sigma(w)^-1 v = sigma(f')^-1 sigma(w')^-1 v`, and `wf = 1` implies
     `sigma(f)^-1 sigma(w)^-1 v = v`.
   - *The pulled-back configuration.* At a certified `v`, the rule
     `x_(wf) = u_(sigma(f)^-1 sigma(w)^-1 v)`, `x_1 = u_v` is well defined.
   - *Control.* Its `tau`-outputs at `w in W` are within `eta/3` of `tau_sigma(u)` at
     `sigma(w)^-1 v`. So `eta/3`-closeness of `tau_sigma(u), tau_sigma(u')` on
     `C(v) = sigma(W)^-1 v` gives `|u_v - u'_v| < 1/16`, by Lemma A.
   - *Density.* A `(1 - epsilon_n)`-fraction of the vertices is certified, with
     `epsilon_n -> 0`.
4. **Sofic full-rank criterion.**
   - *Setup.* Suppose `xi D = 0` with `0 != xi in Z[G]^d` and `E = ∪ supp xi_j`.
   - *Upper bound on the product.* The rows of `sigma(xi) sigma(D)` vanish off
     `o(|V|)` vertices (Lemma Z).
   - *Lower bound on `sigma(xi)`.* Its rows at vertices where `sigma` is injective on
     `E` are non-zero. A greedy choice gives `|V|/(|E|^2 + 1) - o(|V|)` of them with
     disjoint supports (Lemma Q).
   - *Conclusion.* Sylvester's inequality gives
     `rank sigma(D) <= d|V| - |V|/(|E|^2 + 1) + o(|V|)`.
5. **Freezing.** Let `I` be the certified vertices, `J = V`, and
   `g(u) = tau_sigma(u ⊕ 0)`.
   - *The map.* `g` is a `(K, eta/3)`-local rectangular map with surplus
     `<= epsilon_n |V|`, and `rank g^* <= rank sigma(D)`.
   - *Rank.* LRSF with small `delta` gives `rank sigma(D) >= (1 - 2 delta) d |V|`,
     which contradicts step 4 once `2 delta d < 1/(2(|E|^2 + 1))`.
   - *Conclusion.* So `xi = 0`, which is C2.
6. **Surjectivity.** C2 gives surjectivity by
   `torus-automata-with-regular-degree-are-surjective`.

The only unproved input is LRSF (`local-rectangular-small-fibre-maps-lose-proportional-rank`).
Steps 1–5 use no property of `G` beyond the sofic approximation.
