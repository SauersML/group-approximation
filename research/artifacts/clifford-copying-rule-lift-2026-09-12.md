# Lifting the Kun--Thom copying rule through the Clifford twist

Lane `w4-clifford-copy`, 2026-09-12. Host and coordinates as in Section 0 of
`research/artifacts/clifford-cover-orbital-localization-2026-09-12.md`: a group `G`, a `G`-set `X`, a
`G`-invariant graph `S`, the Clifford cover `E_S = Vtilde_S semidirect G` with central `eps`, and
`W = E_S/<eps> = (Z/2) wr_X G`. The question comes from Section 5 of
`research/artifacts/clifford-cover-phase-barrier-2026-09-12.md`: the site set `X = G/Gamma` of the Kun--Thom pair
carries the injective, non-surjective copying rule `x -> x o p`, and it was asked whether the Clifford twist lets
that rule lift to a strict automaton on `E_S`.

Nothing here decides `kun-thom-clifford-cover-nonsurjunctive`. The answer to the question as posed is no, for a
reason that does not involve the twist, and what remains is isolated exactly.

- **Theorem 1 (copying rules lift only as shifts).** The copying rule lifts to every group mapping onto `G`, but
  only as a bijective right shift. Over a group, a copy automaton is always a right shift, so the tree mechanism
  (siblings reading one parent cell) is never an automaton over any group. Every equivariant lift of site data lands
  in `eps`-invariant configurations, where an injective automaton on `E_S` is already bijective.
- **Theorem 2 (self-dual sectors are frustrated flux shifts).** For a self-dual binary rule, the `eps`-odd
  configurations modulo the global flip are conjugate to a `W`-subshift of `Z/2`-gauge fields on the Cayley graph of
  `W`, with flux `omega(r)` on each relator. For the complete graph, `omega = 1` on every lamp-commutator plaquette.
  The twist enters the sector exactly as this frustration; with zero flux the sector map is bijective whenever `W`
  is surjunctive.

## 0. Setting

- `Gamma < G` and `t in G` with `t Gamma t^(-1) <= Gamma`, `X = G/Gamma`, `o = Gamma`.
- `p(g Gamma) = g t^(-1) Gamma`. It is well defined because `t Gamma t^(-1) <= Gamma`, `G`-equivariant and onto,
  with fibres of size `d = [Gamma : t Gamma t^(-1)]`. For the Kun--Thom Theorem E pair `d >= 2`.
- `rho(x) = x o p` on `A^X`. It is equivariant, injective, and not surjective when `d >= 2`.
- For a group `E`, an automaton is `tau(x)(e) = mu((x(e m))_(m in M))` with finite memory `M`. It commutes with
  left translations `(L_h x)(e) = x(h^(-1) e)`.
- `Fix_H` is the set of configurations constant on right cosets `H e`, as in
  `injective-automata-restrict-to-schreier-graph-automata`.

## 1. Theorem 1: copying rules lift only as shifts

**Theorem 1.** Let `pi : E -> G` be an epimorphism, for example `E = G`, `W` or `E_S` with `pi` the projection.

1. **The lift exists and is bijective.** `iota(x)(e) = x(pi(e) o)` is an `E`-equivariant, continuous, injective map
   `A^X -> A^E`. For any `s in E` with `pi(s) = t^(-1)`, the right shift `R(y)(e) = y(e s)` is an automaton with
   memory `{s}`, it is bijective with inverse memory `{s^(-1)}`, and `R o iota = iota o rho`.
2. **Every equivariant lift of site data is `ker pi`-invariant.** For every `E`-equivariant map
   `phi : A^X -> A'^E`, the image lies in `Fix_(ker pi)`.
3. **Copy automata over a group are right shifts.** If an automaton `tau` over a group `E` satisfies
   `tau(x)(e) = x(P(e))` for all `x, e` and some map `P : E -> E` (with `|A| >= 2`), then `P(e) = e m` for one fixed
   `m in M`. So `P` is a bijection.
4. **Clifford covers.** Let `E = E_S` with `W` surjunctive and `tau` injective. Then `tau` maps `Fix_H` onto `Fix_H`
   for every subgroup `H` containing `eps`. In particular this holds for `Fix_(Vtilde_S)`, which contains every lift
   of site data by part 2. On the complete graph over an infinite set, and on any graph with an infinite induced
   matching, it holds for every `H` whose lamp part has finite codimension.

*Proof.*
1. `iota(h.x)(e) = x(pi(h)^(-1) pi(e) o) = iota(x)(h^(-1) e)`, and `iota` is injective because `pi` is onto.
   `R(iota x)(e) = x(pi(e) t^(-1) o) = x(p(pi(e) o)) = iota(rho x)(e)`. The right shift by `s^(-1)` inverts `R`.
2. For `k in ker pi`, `k` acts trivially on `X`, so `L_k phi(x) = phi(k.x) = phi(x)`.
3. Fix `e`. The cells `e m` (`m in M`) are pairwise distinct, by right cancellation. If `P(e)` were outside `eM`,
   changing `x` at `P(e)` alone would change `tau(x)(e)` while fixing its inputs, which is impossible. So
   `P(e) = e m_(j(e))`, and since the values `x(e m)` are arbitrary, `mu(a) = a_(j(e))` for all `a in A^M`. `mu` does
   not depend on `e`, and a coordinate projection determines its coordinate when `|A| >= 2`, so `j` is constant.
4. `Fix_H <= Fix_(eps)`. `eps` is central, so `<eps>` is normal with quotient `W`, and part 4 of
   `injective-automata-restrict-to-schreier-graph-automata` puts `Fix_(eps)` inside `tau(A^E)`. Part 1 of that node
   gives `tau(Fix_H) = tau(A^E) cap Fix_H = Fix_H`. The last sentence is
   `clifford-cover-cofinite-lamp-subgroups-contain-the-center`. QED

**Consequences for the copying question.**
- **The lift is not the source of strictness.** The copying rule is intertwined with a bijective shift over `G`,
  over `W` and over every Clifford cover, whatever the graph. The non-surjectivity of `rho` is only the statement
  that `R^(-1)` does not preserve the invariant subspace `iota(A^X)`: preimages of encoded configurations are not
  right-invariant under `pi^(-1)(Gamma)`.
- **Siblings.** The tree Garden of Eden is two siblings with different symbols. It needs siblings to read one common
  parent cell. Over a group, siblings `e k_j` (with `k_j` coset representatives of `t^(-1) Gamma t / Gamma`) read
  `e k_j s = e s gamma_j` with `gamma_j = t k_j t^(-1)` in `Gamma`. These are distinct cells unless
  `gamma_j = gamma_(j')`. Part 3 shows no rule over any group repairs this: copy automata are shifts.
- **Coset spaces.** On a Schreier graph `H\E` the reads `H e m` can coincide, and the pattern of coincidences can vary
  with the vertex. A uniform rule can then copy "the odd one out", so copy maps of Schreier graphs need not be
  bijective. By part 4, on `E_S` this needs `H cap <eps> = 1`, and on the complete graph a lamp part of infinite
  codimension. An example of such a subgroup is the lift of the span of the indicator vectors of disjoint 4-element
  blocks of sites: the block products square to `1`, pairwise commute, and generate a group not containing `eps`.
- **The relation that kills site-level lifts is twist-independent.** It is right cancellation in `E`, together with
  `ker pi >= <eps>` and surjunctivity of `W`. So any Garden of Eden of a strict automaton on `E_S` extends to no
  configuration fixed by a subgroup containing `eps` (this is the filter of
  `injective-automata-restrict-to-schreier-graph-automata` for `H = <eps>`).
