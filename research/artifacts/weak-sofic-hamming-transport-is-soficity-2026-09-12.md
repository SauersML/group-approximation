# Hamming transports of weakly sofic models are exactly sofic approximations

Lane `w3-weaksofic`, 2026-09-12. Supports
`hamming-transports-of-weak-sofic-models-are-soficity`, the refuted claim
`weak-sofic-models-admit-uniform-hamming-transports`, and the dead route
`weakly-sofic-surjunctivity-via-hamming-transport`. It continues
`weak-soficity-surjunctivity-route-2026-09-12.md` (below: [WS]).

Conventions are those of [WS]: a length `l` on a finite group `H` is
conjugation invariant and subadditive; `(H, l, phi)` on a finite `F` has defect
`l(phi(a)phi(b)phi(ab)^-1) <= eps` and separation `l(phi(g)) >= c`. For a finite
`H`-set `V`, `l_V(z) = 1 - fix(z)/|V|`.

## 1. The starting point: fibre absorption at a normal subgroup

[WS] left one case alive: models with a normal subgroup `N` on which `l` is
small. The natural count runs on the `H/N`-set and absorbs `N`-level defects in
the fibres.

**Lemma 1.1.** Let `N` be normal in `H` and `V = H/N` with left translation.
Then `l_V(z) = 0` for `z` in `N` and `l_V(z) = 1` otherwise.

*Proof.* `z hN = hN` iff `h^-1 z h` is in `N` iff `z` is in `N`, since `N` is
normal. So `z` in `N` fixes every coset and `z` outside `N` fixes none. QED

**Corollary 1.2.** A Gromov--Weiss chart system on `A^(H/N)` needs every defect
on the decoder products to lie in `N`, and `phi(g)` outside `N` for `g != 1` in
the window set. Then `phi mod N` is an exact homomorphism on those products and
injective on the window, which is a local embedding into the finite group `H/N`.

Absorbing defects in fibres means reading configurations that are constant on
`N`-cosets, and those are exactly the configurations on `H/N`. So the ansatz
yields LEF data on the quotient and nothing weaker. The size of `l` on `N` never
enters. That matches [WS] Section 1: the count consumes an `H`-set, not the
length.

Partial absorption, where most but not all of a defect's conjugacy class lies in
a subgroup `L`, gives the coset lengths `l_(H/L)(z) = 1 - |z^H cap L|/|z^H|`, and
mixtures of them ([WS] Lemma 5.1). Section 2 shows that every such mixture is
permutation data.

## 2. Every transport is a permutation model

Let `rho_V: H -> Sym(V)` be the permutation representation of a finite `H`-set,
and `d_H` the normalized Hamming distance on `Sym(V)`.

**Lemma 2.1.** `d_H(rho_V(x), rho_V(y)) = l_V(x y^-1)` for all `x, y` in `H`.

*Proof.* `x v != y v` iff `y^-1 x` moves `v`, so the normalized count is
`l_V(y^-1 x)`. Conjugating by `y` gives `l_V(y^-1 x) = l_V(x y^-1)`, because
fixed-point counts are conjugation invariant. QED

**Definition.** `G` admits *uniform Hamming transports of weakly sofic models*
if there is `c' > 0` such that for every finite `F` in `G` and every `delta > 0`
there are a weakly sofic approximation `(H, l, phi)` on `F` (any defect, any
separation) and a finite `H`-set `V` with

```text
l_V( phi(a) phi(b) phi(ab)^-1 ) <= delta     for a, b, ab in F,
l_V( phi(g) )                   >= c'        for g != 1 in F.
```

This is exactly what [WS] Proposition 1.2 consumes, for every finite set at
once, and it is feasibility of [WS] Corollary 5.2's linear program with vanishing
defect bound and fixed separation.

**Theorem 2.2.** `G` admits uniform Hamming transports iff `G` is sofic.

*Proof.* (If.) A sofic approximation `phi: F -> Sym(V)` is a weakly sofic
approximation with `H = Sym(V)` and `l` the normalized Hamming length. Take the
natural `H`-set `V`. By Lemma 2.1 the two displayed conditions are the sofic
defect and separation.

(Only if.) Put `psi = rho_V o phi: F -> Sym(V)`. Then `psi(1) = id`, and by
Lemma 2.1, `d_H(psi(a)psi(b), psi(ab)) = l_V(phi(a)phi(b)phi(ab)^-1) <= delta`
and `d_H(psi(g), id) = l_V(phi(g)) >= c'`. So `G` has sofic approximations with
arbitrarily small defect and fixed separation `c'` on every finite set. The
diagonal action on `V^r` multiplies defects by at most `r` and raises separation
to `1 - (1 - c')^r`, since `fix_(V^r)(z) = fix_V(z)^r`. Choosing `r` and then
`delta` gives defect below any `eps` and separation above any `c < 1`. So `G` is
sofic. QED

**Corollary 2.3.** If `G` is weakly sofic and not sofic, some finite `F` in `G`
and `delta_0 > 0` defeat every weakly sofic model and every `H`-set: some defect
has `l_V > delta_0`, or some `phi(g)`, `g != 1`, has `l_V < c'`. By
`weakly-sofic-not-sofic`, the Kun--Thom wreath is such a `G`.

So the chart-transport route cannot prove `weakly-sofic-groups-are-surjunctive`
through any statement that supplies transports for every finite set. Normal
fibres (Section 1), partial absorption, and mixtures over the subgroup lattice
are all special cases, and none can be used uniformly in a nonsofic weakly sofic
group. Every one of those groups on record is already surjunctive by the landed
permanence theorems, so the obstruction refutes a method, not the claim.

## 3. The automaton-specific escape, and why it is narrow

A counting proof for one hypothetical strict automaton `tau` needs transports
only on its own finite set `K_tau = N M u Omega Omega^-1`: defects small on the
decoder products, separation on `K_tau`. Theorem 2.2 does not exclude that.

Two landed facts bound this escape. It is recorded here as guidance, not as a
claim.

- By `sofic-radical-localizes-garden-of-eden-windows`, `Omega Omega^-1` contains
  a nontrivial `k` in the sofic radical of `<M>`. For every `eps` there is a
  finite witness set `F_k` in `<M>` and `delta_k` such that every
  `delta_k`-almost multiplicative permutation model on `F_k` moves `k` by at most
  `eps`. A transport controlling defects on `F_k` therefore loses separation at
  `k`. Any surviving transport must leave defects uncontrolled on some witness
  set: it models the window alone, not the group around it.
- By `forward-relations-of-a-counterexample-have-a-nonsofic-core`, the forward
  table of a strict design presents a group with a nonsofic core, and the
  reverse inequalities a counting proof must separate live in that core.

So a window-level transport would have to be a permutation model of a finite
partial table that separates elements invisible to every permutation model of
the table's own group. No mechanism for that is known. Section 4 recasts what is
left without transports.

## 4. What is left: metric ultraproducts

Let `(H_i, l_i)` be finite groups with invariant lengths and `omega` a
nonprincipal ultrafilter. Put `Q = prod_i H_i / N_omega`, where `N_omega` is the
normal subgroup of sequences whose lengths tend to `0` along `omega`.

**Proposition 4.1.** Every countable weakly sofic group is surjunctive iff every
such `Q` is surjunctive.

*Proof.* (If.) A countable weakly sofic group embeds in some `Q`:
- exhaust by finite sets `F_n`, and take models with defects `eps_n -> 0`;
- rescale lengths to `min(1, l_n / c_n)`, which is again an invariant length, to
  make separation `1`;
- send `g` to the class of `(phi_n(g))`.

Surjunctivity passes to subgroups (`surjunctivity-passes-to-subgroups`).

(Only if.) A strict automaton over `Q` with memory `M` is strict over `<M>`, by
the two-way coset transfer. For finite `F` in `<M>`, choose representatives with
`h_i(1) = 1`. Finitely many products agree modulo `N_omega`, and finitely many
nontrivial elements have positive limit length. So for `omega`-many `i` the map
`g -> h_i(g)` is a weakly sofic approximation on `F`. Hence `<M>` is weakly sofic
and not surjunctive. QED

**Remark 4.2 (rectangle clauses).** By
`surjunctivity-is-axiomatized-by-rectangle-clauses`, surjunctivity is a set of
sentences `for all x (AND forward equations -> OR reverse equations)`. A clause
fails in `Q` exactly when there are tuples in the `H_i` whose forward words have
lengths tending to `0` along `omega` while every reverse word keeps length above
a fixed `c > 0`. So Proposition 4.1 says the claim is *metric stability* of
rectangle clauses on finite groups with invariant lengths. The exact clauses
hold in finite groups, because finite groups are surjunctive.

**Remark 4.3 (a quotient of an ultraproduct).** `Q` is the abstract ultraproduct
`U = prod_omega H_i` modulo the image of `N_omega`. `U` satisfies every rectangle
clause by Łoś's theorem. So the claim is quotient closure for one special kind
of kernel, the infinitesimal subgroup. General quotient closure is equivalent to
Gottschalk's conjecture (`surjunctivity-passes-to-quotients`).

**Remark 4.4 (normal-subgroup lengths are harmless).** If `l_i` equals `eps_i`
on a normal subgroup `N_i` and `1` elsewhere, with `eps_i -> 0`, then `Q` is the
abstract ultraproduct of the finite groups `H_i/N_i`, which satisfies every
clause. So normal-subgroup lengths, the starting point of this lane, never
produce a strict clause. The remaining content is lengths whose small balls
generate the group: simple factors by [WS] Theorem B, and more generally factors
where the infinitesimal subgroup is not a limit of normal subgroups.

## 5. Where it stops

- **Settled.**
  - Counting on finite actions of weakly sofic models is soficity (Theorem 2.2).
  - Normal fibres give local embeddings (Section 1).
  - The chart-transport route is dead for nonsofic weakly sofic groups
    (Corollary 2.3).
  - The claim is equivalent to metric stability of rectangle clauses
    (Proposition 4.1, Remark 4.2).
- **Open.** A mechanism that uses the length itself, not a finite action, to
  force reverse equations from approximate forward equations. No such mechanism
  is known. `metric-ultraproducts-of-finite-groups-are-surjunctive` records the
  question.
