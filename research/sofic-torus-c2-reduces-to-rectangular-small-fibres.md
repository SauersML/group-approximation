---
rg: 2
id: sofic-torus-c2-reduces-to-rectangular-small-fibres
kind: claim
title: For sofic groups, regularity of the degree of every injective torus automaton follows from a group-free local rectangular small-fibre lemma for finite-dimensional tori
distinct_from:
  lef-groups-are-torus-surjunctive: that uses exact LEF models, in which every vertex is certified and the model map is square, so the dimension-free small-fibre lemma applies directly; this handles sofic models with a vanishing fraction of uncertified vertices, freezes them, and isolates the only missing input as a statement (LRSF) about rectangular local maps with proportional surplus.
  injective-torus-automata-have-regular-degree: that is C2 for every group (OPEN); this proves C2 for all sofic groups, including all amenable groups, conditionally on LRSF.
  local-rectangular-small-fibre-maps-lose-proportional-rank: that is the group-free lemma itself (OPEN); this is the reduction of sofic C2 to it.
  exact-relation-models-give-torus-degree-regularity: that proves C2 per automaton from co-soficity of a finitely presented local cover and shows square models reach exactly LEF at group level; this is the defect-tolerant, rectangular reduction that is needed beyond LEF.
  torus-degree-regularity-lifts-through-li-kernels: that descends C2 along locally indicable kernels; this is an approximation reduction with no normal subgroup, which reaches sofic simple and torsion groups, such as finitely generated amenable simple groups.
artifacts:
  - research/artifacts/sofic-torus-rectangular-small-fibre-2026-09-19.md
  - research/artifacts/lef-torus-small-fibre-2026-09-18.md
---

**Setting.** `tau: (T^d)^G -> (T^d)^G` is injective, continuous and `G`-equivariant,
with degree matrix `D in M_d(Z[G])` (`tau^* xi = xi D` on `H^1 = Z[G]^d`).

**LRSF** (`local-rectangular-small-fibre-maps-lose-proportional-rank`). Call a
continuous `g: (T^d)^I -> (T^d)^J` a `(K, eta)`-*local rectangular map* when:
- each output site depends on at most `K` input sites;
- each input site `i` has at most `K` output sites `C_i` such that `eta`-closeness of
  `g(u), g(u')` on `C_i` forces `|u_i - u'_i| < 1/16`.

LRSF asserts that for every `delta > 0` there is `beta(K, d, eta, delta) > 0` such that
`|J| - |I| <= beta |I|` implies `rank g^* >= (1 - delta) d |I|`.

**Claim.** If LRSF holds, then for every sofic group `G` and every `tau` as above:
1. `rank sigma_n(D) = d |V_n| - o(|V_n|)` along every sofic approximation
   `sigma_n: G -> Sym(V_n)`;
2. `xi -> xi D` is injective on `Q[G]^d`, which is C2;
3. `tau` is surjective (by `torus-automata-with-regular-degree-are-surjective`).

So torus surjunctivity for all sofic groups, and in particular for all amenable groups,
is reduced to one statement about finite-dimensional tori that mentions no group.

**Unconditional parts.**
- The *sofic full-rank criterion*: if `xi D = 0` with `0 != xi in Z[G]^d` and
  `E = ∪ supp xi_j`, then `rank sigma_n(D) <= d|V_n| - |V_n|/(|E|^2 + 1) + o(|V_n|)`.
- The *pull-back certificate*: at every vertex where the relations
  `wf = w'f'` and `wf = 1` (`w in W`, `f in F`) hold, the model map
  `tau_sigma(u)_q = mu'((u_(sigma(f)^-1 q))_f)` controls the input by the outputs at
  `sigma(W)^-1 v`, with modulus fixed by `tau`.

**Sharpness of the needed lemma.**
- Without locality LRSF is false: [LEF] Theorem 3.
- Its constant must grow with `K`: products of small-ball embeddings
  `T^k -> T^(k+1)` lose rank `k` per surplus site (artifact, Proposition S).

**ESTABLISHED 2026-09-19** by
[[sofic-torus-c2-reduces-to-rectangular-small-fibres-proof]]
(the reduction; LRSF is OPEN). Agent-verified only.
