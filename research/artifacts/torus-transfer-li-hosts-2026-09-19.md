# The torus-to-finite transfer at hosts where torus surjunctivity is already proved

swarm-0917-w16-w16-gs-break, 2026-09-19. Target node:
`torus-surjunctivity-implies-finite-alphabet-surjunctivity` (C3 of
`gottschalk-via-torus-alphabet-degree-transfer`).

## 0. Notation

- `TS(G)`: for every `d >= 1`, every injective continuous `G`-equivariant self-map of
  `(T^d)^G` is onto. `𝒞 = {G : TS(G)}`, as in `torus-degree-regularity-lifts-through-li-kernels`.
- `S(G)`: for every finite alphabet `A`, every injective cellular automaton on `A^G` is onto.
- `C3(G)`: `TS(G) => S(G)`. The node C3 is `for all G, C3(G)`.
- `LI`: locally indicable groups (every nontrivial finitely generated subgroup maps onto `Z`).

## 1. Localization lemma

**Lemma 1.** For every group `G` in `𝒞`, `C3(G)` holds if and only if `S(G)` holds.

*Proof.* `TS(G)` is true, so the implication `TS(G) => S(G)` has the truth value of `S(G)`. QED.

The lemma is formal. Its content comes entirely from which groups are *known* to lie in `𝒞`.

## 2. Hosts known to lie in `𝒞`

Every item below is quoted from an ESTABLISHED node:

- (H1) every locally indicable group, at every `d`
  (`locally-indicable-groups-are-torus-surjunctive`, item (c));
- (H2) every group with an elementary-admissible normal subgroup `N` whose quotient is
  residually finite or locally residually prime-power, including every virtually locally
  indicable group, and hosts such as `BS(2,3) x A_5` and `F x A_5`
  (`torus-degree-regularity-lifts-through-li-kernels`, item 4);
- (H3) residually finite groups, and residually (LI amenable) groups
  (`torus-automata-over-rf-or-domain-groups-are-surjunctive`,
  `residually-li-amenable-groups-are-torus-surjunctive`).

**Corollary 2.** If C3 holds, then `S(G)` holds for every `G` in (H1)–(H3). In particular,
every locally indicable group is surjunctive, and so is every compiler rope `R_e`, `e in INF`.
The last statement uses `compiler-rope-is-locally-indicable`.

On (H3), `S(G)` is already known, because residually amenable groups are sofic. So the new
content of Corollary 2 is at (H1) and at the part of (H2) not already known to be sofic.

## 3. Why this is beyond the current toolkit

- **Soficity of LI groups is open.** Soficity is the only general source of surjunctivity in
  the graph, and it is not known for locally indicable groups.
  `sofic-fp-pi2-complete-or-locally-indicable-nonsofic-group` (ESTABLISHED, proposed) gives a
  dichotomy: either soficity of finite presentations is `Pi^0_2`-complete, or some finitely
  presented locally indicable group `R_e` is not sofic.
- **What Corollary 2 means for each branch.**
  - In branch (b), C3 contains Gottschalk's conjecture at a nonsofic group. No known method
    reaches that.
  - In branch (a), C3 still contains `S(R_e)` for every `e`. This is open, because
    `compiler-positive-rope-is-not-sofic` is OPEN.

## 4. Where same-class transfer mechanisms die

Let a *transfer mechanism* be a rule that takes a strict pair `(G, tau)`, meaning an injective
non-surjective automaton `tau` on some `A^G`, and returns a group `H = H(G, tau)` together with an
injective non-surjective torus automaton `sigma` on `(T^d)^H`. The obstruction (O2) on the
target node says this is the form a proof would need.

**Proposition 3.** Suppose a mechanism is correct on locally indicable inputs, and satisfies
`H(G, tau) in 𝒞` whenever `G` is locally indicable. Then no locally indicable group carries a
strict pair.

*Proof.* A strict pair over a locally indicable `G` would give a strict torus automaton over
`H in 𝒞`. That contradicts `TS(H)`. QED.

**Host operations that stay in `𝒞` on LI inputs.** Each of the following sends a locally
indicable `G` into `𝒞`:
- `H = G`;
- `G x Z^k`, and the wreath products `Z^k wr G`;
- any extension of `G` by, or of, a locally indicable group;
- `G x F` with `F` finite, and every finite-index overgroup of `G` (virtually LI, so in (H2)).

For the wreath and extension items, `LI` is extension-closed. Let `N <| E` with `N` and `E/N`
locally indicable, and let `K <= E` be nontrivial and finitely generated.
- If `K` is not contained in `N`, its image in `E/N` is nontrivial and finitely generated, so it
  maps onto `Z`.
- Otherwise `K <= N`, and `K` maps onto `Z` directly.

The base `Z^(k G)` is torsion-free abelian, hence locally indicable.

**The invariant and the step where the mechanism dies.** The output degree matrix `D(sigma)`
must be singular over `Q[H]` while `epsilon(D(sigma)) in GL_d(Z)` (the constants).
- By `locally-indicable-groups-are-torus-surjunctive` (a), its support subgroup
  `<supp D(sigma)>` is not locally indicable.
- By `torus-degree-regular-on-prime-power-residual-support`, it is not residually prime-power.
- So the mechanism must manufacture, inside `H`, a finitely generated subgroup outside both
  classes. This happens at the step that builds `H`. It needs torsion of non-prime-power order
  that no elementary-admissible kernel absorbs, as with the Bezout element, or a nontrivial
  finitely generated perfect subgroup, as with the Fox witness.
- **Not covered by any established node.** Example hosts with this property:
  - lamplighters `F wr G` with `|F|` not a prime power and `G` locally indicable and not
    residually finite. The base `F^(G)` is not locally normal, so item 4 of the descent node
    does not apply.
  - hosts containing `Alt_fin(N)`.
  Whether these hosts lie in `𝒞` is open.

## 5. The characteristic diagnosis, corrected at LI hosts

The target node gives one reason to expect C3 to be deep or false. Linear torus surjunctivity
is characteristic `0` (Kaplansky), while linear finite-alphabet surjunctivity is stable
finiteness of `F_p[G]`.

At a locally indicable host this gap is absent in rank `1`. For every field `K`, `K[G]` is a
domain (Burns–Hale gives left-orderability, hence unique products). So a one-sided unit of
`K[G]` is a unit. Linear automata on `K^G` with one-dimensional alphabet are transposes of
multiplication by `a in K[G]` on `K[G]`, since `K^G` is the algebraic dual of `K[G]`. An
injective transpose means that multiplication by `a` is onto. So `a` is a one-sided unit, hence
a unit, and the automaton is bijective.

Rank `>= 2` over `F_p` would need stable finiteness of `M_d(F_p[G])`. That would follow from
`G in D(F_p)`, which is not imported here, so it is left open.

Conclusion: at LI hosts C3 is hard although the torus side is proved and the rank-1 linear
shadows agree in every characteristic. The obstruction is not the characteristic gap. It is
Gottschalk's conjecture for LI groups itself.

## 6. Scope

- **Not claimed.**
  - That C3 is false.
  - That LI groups are non-surjunctive.
  - That the route through torus alphabets is circular. For every route of the form "P for all
    groups, and P implies the target", the second step is equivalent to the target once the
    first holds. That remark is formal and carries no information.
- **Claimed.** The torus hypothesis carries no information at LI hosts, so C3 contains, with no
  hypothesis at all, surjunctivity of every LI group.
