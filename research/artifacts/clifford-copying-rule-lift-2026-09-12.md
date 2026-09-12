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

## 2. Theorem 2: self-dual sectors are frustrated flux shifts

Let `E` be any group with a central involution `eps`, `W = E/<eps>`, `e -> ebar` the quotient map, and `A = F_2`.
Call a rule `mu : F_2^M -> F_2` **self-dual** if `mu(a + 1) = mu(a) + 1`, where `1` is the all-ones vector.

- The **sector** is `Tw = { x in F_2^E : x(eps e) = x(e) + 1 }`. Left translation by `eps` is the global flip
  `x -> x + 1` on `Tw`.
- `J(x)(e) = x(eps e) + 1` is an involution of `F_2^E` commuting with left translations, and `Fix(J) = Tw`.
- `Z(E)` is the set of maps `Theta : W x E -> F_2` with `Theta(w, m m') = Theta(w, m) + Theta(w mbar, m')` and
  `Theta(w, eps) = 1`, with `W` acting on the first argument.
- For a generating set `Sigma` of `E`, `Z_omega` is the `W`-subshift of `(F_2^Sigma)^W` of labelled 1-cochains `c` on
  the Cayley graph of `W` whose sum along every word `r` in `Sigma^(+-1)` with `rbar = 1` equals `omega(r)`, where
  `r = eps^(omega(r))` in `E`. The value of an inverse letter is read on the reversed edge:
  `c(w, sigma^(-1)) = c(w sigmabar^(-1), sigma)`.

**Theorem 2.** Let `tau` have a self-dual rule `mu` and memory `M`.
1. **Sector.** `tau J = J tau`, so `tau(Tw) <= Tw`. If `tau` is injective, `tau(F_2^E) cap Tw = tau(Tw)`.
2. **Gauge coordinates.** `x -> Theta_x(w, m) = x(e) + x(e m)` (any lift `e` of `w`) is a `W`-equivariant
   homeomorphism `Tw/flip -> Z(E)`. Restriction to `W x Sigma` identifies `Z(E)` with `Z_omega`.
3. **Induced automaton.** `Theta_(tau x)(w, m) = Theta_x(w, m) + mu((Theta_x(w, m_i))_i) + mu((Theta_x(w mbar, m_i))_i)`,
   where each `Theta_x(w, m_i)` is the path sum along a fixed word for `m_i`. This is a `W`-automaton `tau_Z` on
   `Z_omega`. If `tau` is injective then so is `tau_Z`, and `tau(Tw) = Tw` exactly when `tau_Z` is onto.
4. **Torsor.** `Z_omega` is a `W`-equivariant torsor under the group shift `Z_0` of flat cochains, and
   `Z_0 = F_2^W/flip`.
5. **Detecting characters untwist.** Suppose some homomorphism `theta : E -> Z/2` has `theta(eps) = 1`, and `W` is
   surjunctive. Then every injective self-dual automaton maps `Tw` onto `Tw`. The same holds when `theta` is defined
   only on the memory group `H = <M>` (with `eps in H`) and `H/<eps>` is surjunctive.
6. **Clifford covers.** Let `E = E_S` with `X = G/Gamma` transitive and `Sigma = Sigma_G union {c_o}`. Then `omega` is
   `0` on the relators of `G` and on `[b, c_o]` for `b in Gamma`, it is `q` on `c_o^2`, and it is `b_S(o, g o)` on the
   plaquette `[c_o, g c_o g^(-1)]`. These determine `omega`. On the complete graph every plaquette with `g o != o`
   carries flux `1`. Since `eps = [c_o, c_(g o)]` is a commutator, no character detects `eps` on any memory group
   containing two lamps at distinct sites, so part 5 never applies there.

*Proof.*
1. `tau(J x)(e) = mu((x(eps e m) + 1)_m) = mu((x(eps e m))_m) + 1 = J(tau x)(e)`. If `tau(x) in Tw`, then
   `tau(Jx) = J tau(x) = tau(x)`, so `Jx = x`.
2. `Theta_x` does not depend on the lift, because `x(eps e) + x(eps e m) = x(e) + x(e m)`. The cocycle identity is
   `x(e) + x(e m m') = (x(e) + x(e m)) + (x(e m) + x(e m m'))`, and `Theta_x(w, eps) = x(e) + x(e eps) = 1`.
   Conversely, for `Theta` in `Z(E)` put `x(e) = Theta(1, e)`. Then `x(e) + x(e m) = Theta(ebar, m)` by the cocycle
   identity, and `x(eps e) = Theta(1, eps) + Theta(1, e) = x(e) + 1`. `Theta_x = Theta_(x')` forces `x' - x` to be
   constant. `Theta_(L_h x) = hbar.Theta_x`. Both maps are local, so this is a homeomorphism of `Tw/flip`.
   On generators: `Theta(w, sigma^(-1)) = Theta(w sigmabar^(-1), sigma)` from `Theta(w, 1) = 0`. Path sums along two
   words for one element of `E` agree, because their quotient word equals `1` in `E` and so has holonomy `0`. A word
   `r` with `rbar = 1` has holonomy `Theta(w, r) = Theta(w, eps^(omega(r))) = omega(r)`. Conversely, a cochain with
   these holonomies defines `Theta` by path sums, and the identities follow.
3. Self-duality gives `mu(a) = a_0 + mu(a + a_0 1)`. With `a_i = x(e m_i)` and `a_0 = x(e)`,
   `tau(x)(e) = x(e) + mu((Theta_x(w, m_i))_i)`. Subtract the same expression at `e m`. Injectivity passes to `tau_Z`
   because `tau` commutes with the flip. The last sentence is part 1 read through part 2.
4. `c, c' in Z_omega` have `c + c'` of holonomy `0`, and flat cochains are coboundaries of `W`-configurations defined
   by path sums.
5. `theta` lies in `Tw`, and `L_h theta = theta + theta(h)`, so `Theta_theta(w, m) = theta(m)` is `W`-invariant.
   Every `x in Tw` is `theta + y` with `y in Fix_(eps) = F_2^W`, and
   `tau(theta + y)(e) = theta(e) + mu((theta(m_i) + y(e m_i))_i)`. So `tau` is conjugate on `Tw` to the `W`-automaton with
   rule `a -> mu(a + theta(M))` and memory `Mbar`. It is injective, hence onto. For `theta` on `H = <M>`: `tau` reads
   only cells in one left coset of `H`, so `F_2^E` splits over left cosets of `H` and `tau` acts on each as the
   `H`-automaton; `H/<eps>` surjunctive gives the conclusion on each coset.
6. `g c_o g^(-1) = c_(g o)` holds exactly in `E_S`, `c_o^2 = eps^q`, `Gamma` fixes `o`, and
   `[c_x, c_y] = eps^(b_S(x,y))`. `W = (Z/2) wr_X G` is presented by the relators of `G`, `c_o^2`, `[b, c_o]` and the
   plaquettes, and `omega` is additive on products of conjugates of relators because `eps` is central. A character
   kills commutators, so `theta(eps) = theta([c_o, c_(g o)]) = 0`. QED

**Reading.** In the split case `E = W x Z/2`, `omega = 0`, there is a detecting character, and the sector is the full
shift modulo flip, where surjunctivity of `W` applies. On `E_S` the sector is the same torsor, but its base point is
not invariant: the twist is exactly the flux `omega`, which no `W`-invariant cochain carries (an invariant cochain
has holonomy `0` on every plaquette, since each letter occurs twice in each direction).

## 3. Decoder coincidences and screens for lift designs

| design | encoder memory | decoder memory | forced coincidences | fate |
|---|---|---|---|---|
| shift lift `R` of the copying rule | `{s}`, `pi(s) = t^(-1)` | `{s^(-1)}` | none | bijective; also `amenable-decoder-memory-forces-surjectivity` (cyclic decoder group) |
| tree-style sibling decoder `min` over children | `{s}` | `{s k_j}` | needs `e k_j s = e s` for distinct `k_j` | not an automaton over any group (Theorem 1.3) |
| Schreier copy "odd one out" on `H\E_S` | several letters | several letters | coincidence partition varies with the vertex | bijective if `eps in H` (Theorem 1.4); needs `H cap <eps> = 1` and infinite-codimension lamp part |
| self-dual sector designs | must generate a group containing `eps` as a product of squares and commutators, when `<M>/<eps>` is surjunctive | nonamenable | holonomy `omega` on the relators the memory spans | only open case; bijective whenever a character of `<M>` detects `eps` (Theorem 2.5) |

**Screens a sector witness on the complete-graph Kun--Thom cover must pass**, collected:
- memory group containing `eps` in its own finite residual and nonsofic
  (`strict-automata-memory-keeps-finite-normal-kernel-residual`);
- `eps` a product of squares and commutators in the memory group (Theorem 2.5), when the image misses part of the
  sector. Theorem 2.5 applies here because `<M>/<eps>` is a subgroup of the surjunctive `W`; on a cover with
  non-surjunctive quotient this screen is not available;
- a profinitely invisible read adjacency (`clifford-cover-strict-pairs-read-invisible-adjacency`);
- nonamenable decoder memory; non-formalizable at every stabilization, since `F_2[E_S]` is stably finite;
- a Garden of Eden taking different values at `e` and `eps e`.

## 4. Where it stops

- **Decided here.** The copying rule does not lift through the twist in any site-level sense; its lifts are shifts,
  and site data is invisible to the twist. The relation responsible (right cancellation, `eps in ker pi`,
  surjunctivity of `W`) is independent of the twist.
- **Isolated.** For self-dual binary rules the twist acts only through the frustrated flux shift `Z_omega`, a torsor
  under the full shift with no invariant base point. A strict self-dual automaton on `E_S` whose image misses a
  configuration of the sector exists iff some self-dual automaton is injective on `F_2^(E_S)` while `tau_Z` misses part
  of `Z_omega`.
- **Not known.** No mechanism converts frustration into non-surjectivity, and no invariant of `Z_omega` separates it
  from `Z_0` as a `W`-subshift. Whether `Z_omega` and `Z_0` are conjugate as `W`-subshifts is open; a conjugacy
  commuting with the induced automata would settle the sector positively.
