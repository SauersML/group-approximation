# Correlation along fibre lines cannot connect twisted level graphs

Lane `fixed-price-correlated-levels`, 2026-09-12. Supports
`fpbs-line-independent-twisted-levels-disconnected` (established) and the open claim
`fpbs-cross-line-correlated-transport-set-generates`.

## 0. Question

`fpbs-twisted-level-percolation-disconnected-at-low-density` refutes the transport graphing
`{t} ∪ {s|_A : s in S}` for independent open levels. Its "Not settled" paragraph leaves open sets
`A` whose open levels are strongly correlated along `t`-orbits. Examples:
- bases of `t`-Rokhlin towers, where openness along each orbit is periodic;
- sets pulled back from Sturmian or odometer factors of the `t`-action.

This note shows that correlation along `t`-orbits never helps while open levels stay independent
across fibre lines: the same `delta_0` works for every such field. So a working `A` must correlate
openness **across** fibre lines.

## 1. Setting and notation

- `Gamma = N semidirect_phi Z` is torsion-free and word-hyperbolic, with `t` generating `Z` and
  `t u t^-1 = phi(u)`. `S` is a finite symmetric subset of `N \ {e}`.
- Main's criterion `fpbs-twisted-level-graph-generates-cyclic-extension`, item (1): for a free
  p.m.p. action and a Borel `A`, the pair `(u, m) in N x Z` is *open* when `t^m (u x) in A`. An open
  pair gives edges `{u, phi^-m(s) u}`, `s in S`. The graphing generates iff this graph is
  connected for a.e. `x`.
- **Rows.** The *row* of `u in N` is the process `(omega(u, m))_(m in Z)`. For `z = u x`, it is the
  indicator of `A` along the `t`-orbit of `z`. Distinct `u` label distinct `t`-orbits in the orbit
  of `x`, because `<t> ∩ N = {e}`.

**Field hypotheses (LI).** A random field `omega : N x Z -> {0,1}` satisfies (LI) with density
`delta` when:
1. the rows `(omega(u, .))_(u in N)` are independent;
2. the law of `omega` is invariant under right translation `(u, m) -> (u w, m)`, `w in N`;
3. `P(omega(u, m) = 1) <= delta` for every `(u, m)`.

Nothing is assumed about dependence **within** a row. Rows may be periodic, Sturmian, odometer
itineraries, or arbitrary stationary processes.

## 2. Theorem

**Theorem.** Let `delta_0 = delta_0(Gamma, t, S) > 0` be the constant of
`fpbs-twisted-level-percolation-disconnected-at-low-density` (Step 4 of its artifact). Let `omega`
satisfy (LI) with density `delta < delta_0`, and let `T_omega` be the graph on `N` with edges
`{u, phi^-m(s) u}` for open `(u, m)` and `s in S`. Then `P(e <-> s in T_omega) < 1` for every
`s in S`, and `T_omega` is almost surely disconnected.

**Proof.** This follows the proof in
`research/artifacts/fpbs/docs/twisted-level-percolation-low-density-disconnection.md`, Section 4.
Steps 1, 3 and 4 there are deterministic and are used unchanged:
- Step 1, witnesses: an edge `{u, v}` is present iff one of at most `2|S|` pairs, each with first
  coordinate `u` or `v`, is open.
- Step 3, the path count `P_l(s) <= |S|^l 2^((K+2)(l+1))`, from isolated `<t>`-components and
  Osin's relative area bound.

Only Step 2 (one path) and Step 5 (0-1 law) used independence of all pairs.

*Step 2 under (LI).* Let `gamma = (w_0, ..., w_l)` be self-avoiding. If `gamma` is open, there is a
choice function `c` assigning each edge `j` an open witness in `W(w_(j-1), w_j)`, and there are at
most `(2|S|)^l` such functions.
- A witness with first coordinate `w_i` serves only edges `i` and `i+1`. So the set `L(c)` of
  first coordinates of the values of `c` has at least `l/2` elements.
- For each row `w in L(c)`, the event that the chosen pairs in row `w` are open is contained in
  `{omega(w, m) = 1}` for any one of them, so it has probability at most `delta`.
- Rows are independent (LI.1), so `P(all values of c open) <= prod_(w in L(c)) delta
  <= delta^(l/2)`.
- Hence `P(gamma open) <= (2|S|)^l delta^(l/2)`, which is exactly the bound of main's Step 2.

*Step 4.* Main's two-point bound follows verbatim: `P(e <-> s) <= A sum_l rho^l < 1` for
`delta < delta_0`.

*Step 5 under (LI).*
- Right translation by `w in N` sends `T_omega` to the graph of the translated field, and maps
  edges `{u, phi^-m(s) u}` to `{u w, phi^-m(s) u w}`. So "connected" is an `N`-invariant event.
- By (LI.1) and (LI.2), the rows are i.i.d. So `N` acts on the space of fields by permuting
  i.i.d. coordinates, freely with infinite orbits. This action is mixing, hence ergodic, and the
  event has probability 0 or 1.
- It has probability at most `P(e <-> s) < 1`, so it is 0. ∎

## 3. Where (LI) holds

**(a) Co-induced actions.**
- Let `T` be any essentially free p.m.p. action of `Z` on `(Z, nu)`, and `H = <t>`.
- The co-induced action is on `X = {f : Gamma -> Z : f(t h) = T f(h)}`, i.e. on `Z^N` through
  `f|_N`, with the product measure `nu^N` and `(g . f)(h) = f(h g)`.
- For `g = t^k n` and `u in N` write `u g = t^(c(u,g)) u'` with `u' in N`. Then
  `(g . f)(u) = T^(c(u,g)) f(u')`, and `u -> u'` is a bijection of `N`. So the action preserves
  `nu^N`.

*Freeness.* Take `g != e`. The measure `nu` has no atoms: an atom would have a finite `T`-orbit,
contradicting freeness.
- If `u' != u` for some `u`, then `f(u g) = f(u)` compares two independent coordinates, which
  agree with probability 0. So the fixed set of `g` is null.
- Otherwise `u g u^-1 in H` for every `u in N`. Taking `u = e` gives `g = t^k` with `k != 0`, and
  then every `u in N` satisfies `u t^k u^-1 in H`, so `u in E(t) = H`. With `H ∩ N = {e}` this
  forces `N = {e}`, which is false.

*Ergodicity.* This follows from mixing of the `N`-subaction, which permutes i.i.d. coordinates with
infinite orbits.

*The field.* Take `B ⊆ Z` Borel and `A = {f : f(e) in B}`. Then `(t^m u . f)(e) = f(t^m u) =
T^m f(u)`, so `omega(u, m) = 1_B(T^m f(u))`.
- The rows are functions of the independent coordinates `f(u)`, so they are independent.
- Right translation by `w` permutes the coordinates.
- Each pair is open with probability `nu(B)`.

So (LI) holds with `delta = nu(B)`.

**(b) The Bernoulli shift.** The Bernoulli shift of `Gamma` on `[0,1]^Gamma` is the co-induction
of the Bernoulli shift of `Z` on `[0,1]^Z`. The identification is `x(h) = f(h)(0)`, so
`f(h) = (x(t^j h))_(j in Z)` and `(g . x)(h) = x(h g)`. The sets `A = {f(e) in B}` are exactly the
Borel sets measurable with respect to the coordinates `x|_H`, so the theorem covers every such
**line-local** `A`. In particular it covers:
- bases of Rokhlin towers for the shift of `x|_H`;
- sets pulled back through factor maps of the process `x|_H` onto rotations (Sturmian codings) or
  odometers. These factors exist by Sinai's factor theorem, since `x|_H` is a Bernoulli
  `Z`-process of infinite entropy. This is cited from memory and is not needed for the theorem.

*Any one coordinate line.* Under `(g . x)(h) = x(h g)` the `t`-orbits of coordinates are the left
cosets `v H`, `v in N`. Let `A` be measurable in `x|_(v H)` for one `v`.
- `omega(u, m) = 1_A(t^m u . x)` reads the coordinates `v t^k u = t^k phi^-k(v) u`, `k in Z`. So
  row `u` of `omega` reads `C_u = {t^k phi^-k(v) u : k in Z}`, which meets row `phi^-k(v) u` at
  level `k`.
- For `u != u'` the sets `C_u` and `C_u'` are disjoint, because at each level `k` they lie in the
  distinct rows `phi^-k(v) u` and `phi^-k(v) u'`. Under the product measure the rows of `omega`
  are independent.
- (LI.2) and (LI.3) hold for every Borel `A`, with `delta = mu(A)`, by invariance of `mu`.

So (LI) holds, and the theorem covers every set read off a single `t`-orbit of coordinates.

*Not covered.* The `t`-action on `[0,1]^Gamma` is the product of the shifts on the lines
`x|_(v H)`, `v in N`. A Rokhlin base, or a rotation or odometer factor, of that whole action may
read several lines `x|_(v H)`, `v in F`, with `|F| >= 2`. Then rows `u` and `phi^-k(w^-1 v) u`
share a coordinate for all `v != w` in `F` and all `k in Z`. So the rows need not be independent,
and the theorem does not apply. Such sets correlate rows and belong to the open claim of Section 5.

**(c) Consequence for transport graphings.** By the criterion's item (1), the graphing
`{t} ∪ {s|_A : s in S}` does not generate the orbit relation when `mu(A) < delta_0` in either case:
- every co-induced action from a free `Z`-action;
- every `A` in the Bernoulli shift that is read off one coordinate line `x|_(v H)`.

## 4. Comparison: what does work

`fpbs-quotient-split-actions-have-cost-one` gives cost one for actions with a free finite-cost
factor of `Gamma/N`. Its set `B = phi^-1(A)` is `N`-invariant, which is the opposite extreme of
(LI): every row is a translate of every other.
- The mechanism is `s z = t^-m (t^m s t^-m) t^m z`, where `t^m s t^-m = phi^m(s)` is a word in `S`.
  Once `t^m z in B`, every letter of `phi^m(s)` is applied inside `B`.
- In the language of this note, the whole fibre word is paid for inside one invariant set.
- `fpbs-quotient-split-not-bernoulli-contained` shows the Bernoulli shift has no such factor.

So between the two extremes, a working `A` in the Bernoulli shift must correlate rows, and it
cannot do so through any factor on which `N` acts trivially.

## 5. What remains, and attempts

**Open.** `fpbs-cross-line-correlated-transport-set-generates`: for the fibre group of a closed
fibered hyperbolic 3-manifold, the Bernoulli shift has Borel sets `A` of arbitrarily small measure
whose transport graphing generates. With the criterion, `fpbs-bernoulli-maximal-cost` and the
fibered-cover transfer, this gives fixed price one. The route is
`fpbs-3-manifold-fixed-price-via-correlated-transport-sets`.

**Attempts recorded.**
1. *Sets read off one coordinate line.* Dead by the theorem above. Sets that read several lines
   are not covered (Section 3(b)).
2. *Block factors across rows.* Let `A` depend on the coordinates `x|_(H F)` for a finite
   `F ⊆ N` containing `e`.
   - The field `omega(u, m)` then depends on the rows `phi^-m(v) u`, `v in F`: from
     `v t^m = t^m phi^-m(v)`, the coordinate `v t^m u` lies in row `phi^-m(v) u`.
   - The Step 2 extraction needs `>= c l` path witnesses with pairwise disjoint row sets.
   - Isolation of `<t>`-components controls only the rows the path itself visits, not the
     `F`-stars of its levels. A self-avoiding bounded-excursion path can meet the `F`-star of one
     row at up to `(2K(l+1)+1)|F|` levels, so the dependency degree is not bounded uniformly.
   - Result: a radius-dependent `delta_0(F)` might be provable, but nothing uniform. Not pursued.
3. *Mass transport.* Charge each starting point to the witnesses on its shortest path.
   - Witnesses on a length-`L` path lie within `(K+1)(L+1)` of the start.
   - Only `|B_R| ~ exp(alpha R)` starting points can charge a given witness.
   - So receiving `1/delta` on average forces only `L >~ log(1/delta)`. There is no contradiction.
4. *Spectral gap of `N`.* The Bernoulli action of the nonamenable `N` has spectral gap, so `A`
   cannot be relatively almost invariant under `S`.
   - Working paths only need `A` to be chained along the elements `t^k s` with average `|k| <= K`,
     and clumped sets such as `A = B ∪ t^k s B` satisfy that. So spectral gap gives no obstruction by
     itself.
5. *Pseudo-Anosov Markov partitions.* The natural boundary actions of `Gamma` are not p.m.p., so
   they don't give Borel sets of the Bernoulli shift directly. No construction.

**Literature status**, as recorded on main and not re-read here:
- infimal cost one: Gaboriau, Theorem 2.56, cited on the root;
- Abert–Nikolov Theorem 2 (fixed price versus rank vs Heegaard genus): quoted on the root;
- Bernoulli maximal cost: `fpbs-bernoulli-maximal-cost`.

No novelty or priority is claimed. The theorem is a direct extension of main's proof.
