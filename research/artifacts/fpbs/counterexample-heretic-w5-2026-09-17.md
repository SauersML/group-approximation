# Self-commensuration gaps and the bounded-exponent kill (swarm-0917 w5 heretic)

Lane: counterexample direction toward `fpbs-fixed-price-universal`.
Target: `fpbs-fixed-price-counterexample-exists`. The w4 heretic stopped at
Theorem R, which needs a finite-cost normal subgroup `N`, and at its survivors
S1/S2. This note does not use normal subgroups. It gives two results.

1. **Theorem S (a gap machine that needs no cheap-action theorem).**
   Suppose a finitely generated group has isomorphic finite-index subgroups of
   different indices, and one of them has a Farber chain of positive gradient.
   Then the group has two free profinite-type actions whose costs differ, and
   their ratio is the index ratio. Every ingredient except Abert--Nikolov is
   elementary.
2. **Theorem K (a kill).** The only cheap-action certificate known for torsion
   groups, Donoso-Echenique--Silva Proposition 2.7 (bounded centralizers), can
   never be combined with a profinite lower bound. Every group that has a Farber
   chain is residually finite. In a residually finite group, every subgroup of
   bounded exponent is locally finite, so it has no infinite finitely generated
   subgroup, and that is exactly the hypothesis Proposition 2.7 needs.

## 0. Conventions

A *chain* in a finitely generated group `G` is a descending sequence
`G = G_0 >= G_1 >= ...` of finite-index subgroups. Its boundary `dT` is the
inverse limit `lim G/G_n`. The measure `mu` gives the cylinder of a coset
`gG_n` mass `1/[G:G_n]`. The chain is *Farber* when `G` acts on `(dT, mu)`
essentially freely. `RG(G,(G_n)) = lim (d(G_n)-1)/[G:G_n]`. Abert--Nikolov
Theorem 1 (`fpbs-abert-nikolov-rank-gradient-equals-profinite-cost`, verbatim in
its citation route) says that for a Farber chain `RG = cost(E) - 1`, where `E`
is the orbit relation on `dT`. Normality of the chain is not required.

## 1. Theorem S: unequal-index self-commensuration rescales Farber gradients

**Theorem S.** Let `G` be finitely generated, let `H_1, H_2 <= G` have finite
indices `k_1, k_2`, and let `psi: H_1 -> H_2` be an isomorphism. Let `(V_n)`
be a Farber chain in `H_1` with `r = RG(H_1,(V_n))`. Then both
`C^(1) = (G, V_0, V_1, ...)` and `C^(2) = (G, psi(V_0), psi(V_1), ...)` are
Farber chains in `G`, with

    RG(G, C^(1)) = r/k_1,        RG(G, C^(2)) = r/k_2.

So `G` has two free p.m.p. boundary actions of costs `1 + r/k_1` and
`1 + r/k_2`. If `r > 0` and `k_1 != k_2`, the group `G` does not have fixed price.

Special case: `H_1 = G` and `psi = phi` is an injective endomorphism with
`[G:phi(G)] = k >= 2`. Iterating gives Farber gradients `r/k^j` for every `j`.
So the set of Farber gradients of `G` is either `{0}` or infinite.

**Lemma 1.1 (induction).** Let `H <= G` have index `k`, and let `(U_n)` be a
Farber chain in `H` with `U_0 = H`. Then `(G, U_0, U_1, ...)` is Farber in `G`,
and its gradient is `RG(H,(U_n))/k`.

*Proof.*
- **Gradient.** `[G:U_n] = k[H:U_n]`, so `(d(U_n)-1)/[G:U_n] = (1/k)(d(U_n)-1)/[H:U_n]`.
  The limit exists and equals `RG(H,(U_n))/k`.
- **Coordinates.** Fix left coset representatives `t_1, ..., t_k` of `H` in
  `G`. Every coset `gU_n` is `t_j h U_n` for a unique `j` and a unique
  `hU_n in H/U_n`. These bijections `G/U_n = {1..k} x H/U_n` commute with the
  projections from level `n+1` to level `n`. So the boundary of `G` is
  `{1..k} x dT_H`, and its measure is uniform on `{1..k}` times `mu_H`, since
  the cylinder of `t_j h U_n` has mass `1/(k[H:U_n])`.
- **Stabilizers.** Let `xi = (t_j x_n U_n)_n` with `x_n in H`. Then `g xi = xi`
  iff `t_j^{-1} g t_j in x_n U_n x_n^{-1}` for all `n`. Each `x_n U_n x_n^{-1}`
  lies in `H`, so this holds iff `t_j^{-1} g t_j in Stab_H(x)`, where
  `x = (x_n U_n)_n`. Hence `Stab_G(xi) = t_j Stab_H(x) t_j^{-1}`.
- **Freeness.** The set of points with nontrivial stabilizer is the union over
  `j` of `{j} x {x : Stab_H(x) != 1}`. It has measure
  `(1/k) sum_j 0 = 0`. `QED`

**Lemma 1.2 (transport).** An isomorphism `psi: H_1 -> H_2` sends a Farber
chain `(V_n)` in `H_1` to a Farber chain `(psi V_n)` in `H_2` with the same
gradient.

*Proof.*
- **Gradient.** `[H_2:psi V_n] = [H_1:V_n]` and `d(psi V_n) = d(V_n)`.
- **Boundary.** The bijections `hV_n -> psi(h) psi(V_n)` preserve the level
  measures and commute with projections. They give a measure-preserving
  bijection `Psi` of the two boundaries with `Psi(h xi) = psi(h) Psi(xi)`.
- **Freeness.** `Stab_{H_2}(Psi xi) = psi(Stab_{H_1}(xi))`, which is trivial
  almost everywhere. `QED`

*Proof of Theorem S.*
- `C^(1)`: apply Lemma 1.1 to `(V_n)` with `H = H_1`.
- `C^(2)`: apply Lemma 1.2, then Lemma 1.1 with `H = H_2`.
- **Costs.** Abert--Nikolov Theorem 1 turns the gradients into costs
  `1 + r/k_1` and `1 + r/k_2` of the two boundary relations.
- **Admissibility.** Both actions are p.m.p., because `G` permutes the cosets
  at each level and so preserves `mu`, and both are essentially free.

No cheap-action theorem is used. `QED`

### 1.1 Where Theorem S can fail (independent prerequisites)

A counterexample through Theorem S needs two things.

- **(S-a)** A finitely generated group `G` with isomorphic finite-index
  subgroups of unequal index. Call such a group *self-commensurated with
  unequal index*.
- **(S-b)** A Farber chain of positive gradient in one of those subgroups.

These are the invariants each prerequisite must survive. They are recorded as
remarks, with the published inputs named. They are not new graph claims.

- **Multiplicativity kills (S-a) for a large class.**
  - Every multiplicative invariant `I(H) = [G:H] I(G)` with values in `[0,∞)`
    must vanish. This covers the Euler characteristic, every `l2`-Betti number
    `beta_i^(2)`, and the infimal rank gradient `RG(G) = inf_U (d(U)-1)/[G:U]`
    (Abert--Jaikin-Zapirain--Nikolov, whose infimum is multiplicative on
    finite-index subgroups). Free groups, surface groups and every group with
    `beta_1^(2) > 0` are out.
  - Mostow--Prasad rigidity makes covolume an isomorphism invariant of lattices
    in the semisimple case, so irreducible lattices are out too.
- **(S-b) is not killed by (S-a).** `RG(G) = 0` is an infimum. A Farber chain
  can still have positive gradient: the gradient set is closed under division
  by the index ratio, and nothing forces it down to `{0}`.
- **Every known member dies at (S-b), for the same reason.** The known members
  are `Z^d`, `BS(1,n)`, lamplighters and `Gamma(3) ltimes Z^3`
  (`affine-congruence-source-is-kazhdan`). Each has an infinite normal amenable
  subgroup, so it has fixed price one, and Abert--Nikolov then gives gradient
  zero along every Farber chain.
- **The soft kill is circular.** One would like to show that a group
  self-commensurated with unequal index has maximal cost `M_G = 1` through
  restriction and induction. What those give is:
  - `cost(Ind b) - 1 = (cost(b)-1)/k`;
  - `cost(a|H) - 1 = k(cost(a x G/H) - 1)`;
  - `cost(a) <= cost(a|H)` (commensurated transfer,
    `fpbs-fibered-3-manifold-cost-inputs`).

  Together these only give `M_G <= M_H <= 1 + k(M_G-1)`, which is consistent.
  Closing the gap needs `cost(a x G/H) = cost(a)` for finite extensions. That
  equality is the open multiplicativity question isolated in
  `fpbs-finite-fiber-cost-bound`. The Bernoulli shift cannot shortcut it: for
  nonamenable `G`, `s_G x G/H` contains the finite-dimensional representation
  `l2_0(G/H)`, which is not weakly contained in the Koopman representation of
  `s_G`, so the two actions are not weakly equivalent.
- **Infimal cost.** By Gaboriau's index formula for infimal cost,
  `C*(H)-1 = [G:H](C*(G)-1)`. So groups self-commensurated with unequal index
  have `C*(G) = 1`. In this class, fixed price is the same as fixed price one.
  Theorem S does not use this.

## 2. Theorem K: bounded-centralizer cost certificates never meet a Farber chain

Donoso-Echenique--Silva (arXiv:2608.20472), Proposition 2.7, verbatim:
"Let G be a countable group such that the centralizer C_G(g) of every
non-trivial element g∈G is abelian. Suppose that there exists n≥2 such that
sup_{g∈G\{e_G}}|C_G(g)|≤n. Let N be a subgroup of G that contains an infinite
finitely generated subgroup. Then cost(N)<∞."

In the torsion world this is the only cheap-action or finite-cost certificate
in the archive. It feeds `fpbs-bounded-centralizer-relative-cost` and the
Burnside branch. The w4 audit left Burnside-type and Tarski groups "starved".
Theorem K turns that into a precise obstruction for every combination with the
profinite lower bound.

**Theorem K.** Let `G` be an infinite finitely generated group that has a
Farber chain `(G_n)`.

1. `G` is residually finite.
2. Every subgroup of `G` of bounded exponent is locally finite.
3. Let `M` be any group with `|C_M(g)| <= n` for all `g != e`, and let
   `N <= M` also be (isomorphic to) a subgroup of `G`. Then `N` contains no
   infinite finitely generated subgroup. So Proposition 2.7 never applies to
   a subgroup of `G`.
4. `G` itself does not have uniformly bounded centralizers.

*Proof.*

1. Let `K = ∩_n core_G(G_n)`. Every `k in K` fixes every coset `gG_n`,
   because `k g G_n = g (g^{-1} k g) G_n = g G_n`. So `k` fixes every point of
   `dT`. The boundary has measure one and almost every point has trivial
   stabilizer, so `K = 1`. Each `core_G(G_n)` has finite index, so `G` is
   residually finite.
2. Let `N <= G` have exponent dividing `e`, and let `F <= N` be finitely
   generated. `F` is residually finite as a subgroup of `G`, has bounded
   exponent, and is finitely generated. By `fg-rf-bounded-exponent-groups-are-finite`
   (restricted Burnside, Zelmanov), `F` is finite.
3. For `g != e` in `M`, the cyclic group `<g>` lies in `C_M(g)`, so `g` has
   order at most `n`. Hence `M`, and with it `N`, has exponent dividing `n!`.
   By 2, `N` is locally finite, so every finitely generated subgroup of `N` is
   finite.
4. Apply 3 to `M = N = G`. `G` is finitely generated and infinite, so it would
   be an infinite finitely generated subgroup of itself, a contradiction.
   `QED`

**Where the class dies.** The class is: a torsion cheap-action or
finite-cost theorem of bounded-centralizer type, played against an
Abert--Nikolov profinite lower bound. This covers Theorem R with
`N` from Proposition 2.7, the bounded-centralizer relative cost inequality on
the ambient group, and any Burnside quotient paired with a profinite action.
- **Step where it dies:** Proposition 2.7's hypothesis "N contains an infinite
  finitely generated subgroup".
- **Invariant:** bounded exponent. It is forced by bounded centralizers and
  collapses to local finiteness under residual finiteness.
- **Consequence for the Burnside branch.** Lower bounds for `B(m,n)` above
  cost one must come from non-profinite actions. Only the Bernoulli number
  `c_n` of `fpbs-burnside-positive-upper-cost` survives, and it is untouched
  by this note.
- **Consequence for the ambient group.** A locally finite normal subgroup is
  amenable. So the w4 Theorem R, which needs `cost(N) < ∞` with `N` infinite
  normal of infinite index, gets nothing new from torsion-group technology: a
  bounded-exponent `N` is either finite or amenable, and infinite amenable
  normal subgroups already force fixed price one.

## 3. Theorem T: a torsion group whose expensive side is already proved

Theorem K removes the torsion cheap side. The expensive side, for torsion
groups, is unconditional. This makes residually-`p` torsion groups of positive
power `p`-deficiency the sharpest candidate class. Only a cheap action is
missing.

**Construction.** Fix a prime `p`. Enumerate the free group `F = F(x,y)` as
`w_1, w_2, ...`, and let

    Gamma = < x, y | w_i^(p^(i+1)), i >= 1 >,
    Gamma' = Gamma / K,  K = ∩ { normal subgroups of p-power index }.

**Theorem T.** `Gamma'` is an infinite, finitely generated, residually finite
`p`-torsion group. Put `delta = 1 - 1/(p(p-1)) >= 1/2`. Every finite-index
subgroup `U' <= Gamma'` satisfies `(d(U')-1)/[Gamma':U'] >= delta`. Hence, for
every Farber chain of `Gamma'` (normal chains with trivial intersection exist),
the boundary action is free and p.m.p. and has cost at least `1 + delta`.
In particular:

- `Gamma'` has no fixed price one;
- `Gamma'` fails fixed price iff it has a free action of cost different from
  one of these profinite costs;
- if `C*(Gamma') < 1 + delta`, then `Gamma'` refutes fixed price.

`Gamma'` has unbounded exponent (Zelmanov, Theorem K.2) and no property (T). By
`fpbs-kazhdan-cofinal-mod-p-growth-vanishes` with `c = delta`, a Kazhdan group
has a finite-index `M` whose finite-index normal subgroups `N` satisfy
`d_p(N) < delta[Gamma':N]`. Step 5 below gives the opposite bound
`d_p(N) >= 1 + delta[Gamma':N]`. (The presentation-level node
`fpbs-power-p-deficiency-excludes-property-t` does not apply directly,
because `Gamma'` is a quotient of `Gamma`.)

*Proof.*
1. **Torsion.** Every element of `Gamma` is the image of some `w_i`, so its
   order divides `p^(i+1)`. So `Gamma` and `Gamma'` are `p`-torsion.
   `Gamma'` is residually `p`, hence residually finite, and it is generated
   by two elements.
2. **Deficiency.** The relator `w_i^(p^(i+1))` is a `p^(i+1)`-th power, so
   `nu_p >= i+1`. The presentation gives
   `def_p(Gamma) >= 2 - 1 - sum_{i>=1} p^(-(i+1)) = 1 - 1/(p(p-1)) = delta`.
3. **Subnormality.** Let `U' <= Gamma'` have finite index and let `U` be its
   preimage, so `[Gamma:U] = [Gamma':U']` and `K <= U`. `Gamma'/core(U')` is a
   finite `p`-torsion group, hence a `p`-group, so `U'` is subnormal of
   `p`-power index. The same then holds for `U`.
4. **Schreier bound.** By `fpbs-power-p-deficiency-schreier-bound`,
   `d_p(U) - 1 >= delta [Gamma:U]`.
5. **Same `F_p`-rank.** `Phi = [U,U]U^p` is characteristic of `p`-power index
   in `U`, so it is subnormal of `p`-power index in `Gamma`. Such subgroups are
   open in the pro-`p` topology (Ershov survey, Section 9, remark after the
   definition of the `p`-gradient). So `Phi` contains a normal subgroup of
   `p`-power index, and hence `K`. Therefore `U/Phi = U'/Phi'` and
   `d_p(U') = d_p(U)`.
6. **Gradient bound.** `d(U') >= d_p(U')`, so
   `(d(U')-1)/[Gamma':U'] >= delta`.
7. **Infinite.** If `Gamma'` were finite, `U' = 1` would give
   `-1/|Gamma'| >= delta`, which is false.
8. **Costs.** Along any Farber chain each term is at least `delta`, so the
   gradient is at least `delta`. Abert--Nikolov Theorem 1 converts this into
   cost `>= 1 + delta`.
9. **No fixed price one.** Fixed price one would put this cost at one.
   `QED`

The inequality `RG(Gamma') >= def_p(Gamma) > 0` is stated in the survey
(Corollary 9.2 proof: "Thus, Q′ is a residually finite group with positive
rank gradient"). Steps 3-6 re-derive it from the in-graph Schreier bound.

**Decomposition of the torsion counterexample.** Put `rho = inf` over Farber
chains of the gradient, so `rho >= delta`.

- **(T-a), ESTABLISHED here.** The profinite actions of `Gamma'` cost at least
  `1 + delta`.
- **(T-b), OPEN.** Some free p.m.p. action of some finitely generated
  residually finite torsion group `Q` with `RG(Q) > 0` costs strictly less
  than `1 + RG(Q)`.

Each part can fail on its own. (T-a) cannot fail. (T-b) fails if residually
finite torsion groups have fixed price, which is exactly what fixed price
predicts. Because `RG(Q) <= rho`, a cheap action below `1 + RG(Q)` undercuts
every profinite action.

- **What does not deliver (T-b).**
  - DES bounded centralizers: dead, by Theorem K.
  - Hutchcroft--Pete: (T) is excluded.
  - Gaboriau's normal-subgroup theorem: it needs an infinite normal
    subgroup of infinite index with finite cost. The w4 Corollary 3.1 and
    Theorem K bound what torsion `N` can do.
  - Theorem S: `RG(Q) > 0` is multiplicative, so `Q` is not
    self-commensurated with unequal index.
- **A computable falsification test.** Fixed price predicts that all Farber
  chains of `Gamma'` have the same gradient. Two Farber chains of `Gamma'`,
  for example a `p`-central series chain and a chain through a non-normal
  subgroup of small index, with provably different gradients would refute
  fixed price outright.

## 4. Graph bookkeeping

- `fpbs-isomorphic-unequal-index-subgroups-rescale-gradient` (Theorem S),
  ESTABLISHED through its `-proof` route. It requires Abert--Nikolov.
- `fpbs-farber-excludes-bounded-exponent-certificates` (Theorem K),
  ESTABLISHED. It requires `fg-rf-bounded-exponent-groups-are-finite`.
- `fpbs-power-deficiency-torsion-profinite-cost-gap` (Theorem T),
  ESTABLISHED. It requires `fpbs-power-p-deficiency-schreier-bound`,
  Abert--Nikolov, `fpbs-kazhdan-cofinal-mod-p-growth-vanishes` and restricted
  Burnside.
- `fpbs-positive-gradient-torsion-group-cheap-action`, OPEN. This is (T-b).
  The route `fpbs-torsion-profinite-gap-counterexample-route` into
  `fpbs-fixed-price-counterexample-exists` requires (T-b) and Abert--Nikolov.
- `fpbs-self-commensurated-positive-farber-gradient`, OPEN. This is
  (S-a)+(S-b). The route `fpbs-self-commensuration-gradient-gap-route` into
  the root requires it and Theorem S.

**Tried and dead in this lane (do not repeat).**
- Forcing maximal cost one from a self-embedding by restriction and induction:
  circular, Section 1.1.
- Bounded-centralizer certificates played against profinite actions: dead,
  Theorem K.
