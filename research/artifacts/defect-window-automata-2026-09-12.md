# Garden-of-Eden windows on compression defects

Date: 2026-09-12. Lane `gk-defect-automaton`. Handwritten proofs; no computation.

The lane's task was to design a strict automaton over a group carrying the one-sided
compression configuration. Its Garden-of-Eden window was to be `{1, d}`, with `d` a
compression defect, and its left inverse certified by exact relations of the
configuration. This note records what such a design needs and which parts of the
configuration cannot supply it.

- **Lemma 1.** A two-cell window `{1, d}` forces `d` into `M M^-1`. More generally, a
  minimal Garden-of-Eden window has a connected overlap graph.
- **Lemma 2.** Rigid compression defects lie in the sofic radical.
- **Theorem 3.** Surjunctive groups carry nontrivial rigid defects. So placing the
  window on a rigid defect meets the necessary condition of the localization theorem
  and still yields no strict pair.
- **Theorem 4 (inertness).** For every group `H`, subgroup `Gamma` and LEF group `K`,
  the amalgam `H *_Gamma (Gamma x K)` is surjunctive iff `H` is. In it every strict
  compressor of `Gamma` produces a nontrivial defect. A free centralizing factor
  creates defects but never strictness, and destroys none.
- **Section 5.** The configuration content still unexploited is **nesting**: the
  conjugated commuting factor lies inside `Gamma`. The nine-leaf Leavitt configuration
  has a nested nontrivial rigid defect. The surjunctive defect carriers of Theorems 3
  and 4 are built from non-nested ones. Whether nesting forces nonsurjunctivity is
  left open as a Cairn claim.

No strict automaton is constructed here.

## 0. Conventions

These are the conventions of `gottschalk-sofic-radical-localization-2026-09-11.md`.

- An automaton over `G` has a finite alphabet `A`, a finite memory `M` containing `1`,
  and a local rule `f`. It computes `tau(x)(g) = f((x(g m))_(m in M))` and commutes
  with `(h.x)(g) = x(h^-1 g)`.
- A **strict pair** `(tau, sigma, p)` consists of automata with `sigma tau = id`,
  memories `M` and `S`, and a pattern `p in A^Omega` that no `tau(x)` displays on
  `Omega`.
- `Rad(H)`, the sofic radical, is the intersection of the kernels of all homomorphisms
  from `H` to metric ultraproducts of symmetric groups.

**Rigid pairs and defects** follow `rigid-compression-defect-ladder-2026-09-11.md`.

- A rigid pair in `H` is a chain `Gamma <= G <= H` in which `Gamma` and `G` have
  property (T), and `Gamma` is infranormal in `G`: the compression semigroup
  `P_Gamma = {g in G : g Gamma g^-1 <= Gamma}` generates `G`.
- A **rigid defect** is an element `[t z t^-1, gamma]` with `t in G`, `z in C_H(Gamma)`
  and `gamma in Gamma`.
- Commutators are `[a, b] = a b a^-1 b^-1`.

## 1. The overlap lemma

For a finite `Omega`, the **overlap graph** has vertex set `Omega`, with `w` and `w'`
adjacent when `w M` meets `w' M`, that is, when `w^-1 w'` lies in `M M^-1`.

**Lemma 1.** Let `tau` be injective, and let `p` be a Garden of Eden on `Omega` that is
minimal, meaning no proper subset of `Omega` carries a Garden of Eden. Then the overlap
graph of `Omega` is connected, and `|Omega| >= 2`. In particular, if `p` is a Garden of
Eden on `{1, d}`, then `d` lies in `M M^-1`.

*Proof.*
- *Single cells display everything.* `tau` maps each constant configuration to a
  constant configuration, and it is injective. So `a -> f(a, ..., a)` is a bijection
  of `A`, and every symbol is displayed at every cell.
- *Components are independent.* Suppose `Omega = Omega_1 ⊔ Omega_2` with `Omega_1 M`
  disjoint from `Omega_2 M`. The values of `tau(x)` on `Omega_i` depend only on `x`
  restricted to `Omega_i M`. These restrictions can be chosen independently, so the set
  of patterns displayed on `Omega` is the product of the sets displayed on `Omega_1`
  and on `Omega_2`. If `p` is not displayed, one of its restrictions is not displayed,
  and that restriction is a Garden of Eden on a proper subset.

So a minimal window has a connected overlap graph and more than one cell. For
`Omega = {1, d}`, connectivity means `M` meets `d M`. QED.

**Design reading.** The memory of a defect-window automaton must contain two
addresses `m`, `m'` with `m m'^-1 = d`. The window cannot sit on a defect that the rule
never reads across.

## 2. Rigid defects are sofic-invisible

**Lemma 2.** Let `H` be countable and let `Gamma <= G <= H` be a rigid pair. Then every
rigid defect `[t z t^-1, gamma]` lies in `Rad(H)`.

*Proof.* Let `psi: H -> S_U` be a homomorphism into a metric ultraproduct of symmetric
groups. Put `H' = psi(H)`, a countable subgroup of `S_U`, hence sofic.
- `psi(Gamma)` and `psi(G)` have property (T), as quotients of Kazhdan groups.
- `psi(P_Gamma)` is contained in `P_psi(Gamma)` and generates `psi(G)`, so `psi(Gamma)`
  is infranormal in `psi(G)`.
- `psi(z)` centralizes `psi(Gamma)`.

So `psi(Gamma) <= psi(G) <= H'` is a rigid pair in a sofic group.
`sofic-groups-kill-rigid-compression-defects` gives
`psi([t z t^-1, gamma]) = [psi(t) psi(z) psi(t)^-1, psi(gamma)] = 1`. QED.

So the rigid defect is exactly the kind of window difference the localization theorem
(`sofic-radical-localizes-garden-of-eden-windows`) demands. Over the binary Leavitt unit
group the demand is empty anyway, since every element is invisible.

## 3. Invisible rigid defects in surjunctive groups

**Theorem 3.** Let `Gamma < G` be a Kun--Thom Theorem E pair, `X = G/Gamma`, and
`W = (Z/2) wr_X G`. Let `t` be a strict compressor (`t Gamma t^-1 < Gamma`), `a_x` the
lamp at `x`, and `gamma in Gamma` outside `t Gamma t^-1`. Then:

1. `W` is surjunctive;
2. `d = [t a_Gamma t^-1, gamma] = a_(t Gamma) a_(gamma t Gamma)` is a nontrivial rigid
   defect, hence a nontrivial element of `Rad(W)`;
3. no strict pair over any group has window data realizable in `W` with the
   distinguished cells kept apart.

The same holds for every Kun--Thom graph wreath with a nontrivial LEF lamp.

*Proof.*
1. This is `kun-thom-nonsofic-wreaths-are-surjunctive` (all graphs:
   `kt-lef-graph-wreaths-surjunctive-and-nonsofic`).
2. The root lamp `a_Gamma` centralizes `Gamma`, since `Gamma` fixes the coset `Gamma`.
   Then `t a_Gamma t^-1 = a_(t Gamma)`, and `gamma a_(t Gamma) gamma^-1 = a_(gamma t Gamma)`.
   These two lamps sit at different sites because `gamma` does not stabilize
   `t Gamma`: its stabilizer is `t Gamma t^-1`. So `d != 1`. The pair
   `Gamma <= G <= W` is rigid, and Lemma 2 puts `d` in `Rad(W)`.
3. This follows from `strict-pairs-transfer-to-table-realizations`: a realization
   would give a strict pair over the surjunctive group `W`. QED.

**Reading.**
- *Invisibility is not enough.* The localization theorem's necessary condition holds
  for the compression mechanism's canonical invisible element in `W`, yet `W` carries
  no strict pair.
- *The configuration's data does not certify strictness.* `W` satisfies all of it:
  a Kazhdan `Gamma` inside a Kazhdan `G`, a strict compressor, a centralizing involution
  of finite order, and a nontrivial defect.
- *What a defect-window certificate needs.* Its product tables must contain a
  coincidence that fails in every Kun--Thom graph wreath once the window pair is
  separated. The relations "`z` commutes with `Gamma`" and "`t Gamma t^-1 <= Gamma`"
  are not such coincidences.

## 4. Free centralizing factors are inert

**Theorem 4.** Let `H` be any group, `Gamma <= H` any subgroup, and `K` any group.
Put `P = H *_Gamma (Gamma x K)`, `X = H/Gamma`, `x_0 = Gamma`, and let `Lambda(K)` be
the free product of copies `K_x`, `x in X`, with `H` permuting them by
`h k_x h^-1 = k_(h x)`.

1. `P` is isomorphic to `Lambda(K) ⋊ H`.
2. If `K` is LEF, `P` is surjunctive iff `H` is surjunctive.
3. Let `t in H` satisfy `t Gamma t^-1 < Gamma`, and take `gamma in Gamma` outside
   `t Gamma t^-1` and `k in K` with `k != 1`. Then `[t k t^-1, gamma] != 1` in `P`.
   If `Gamma <= <P_Gamma> <= H` is a rigid pair, this is a nontrivial rigid defect,
   hence lies in `Rad(P)`.

*Proof.*

**(1)** Define `Phi: P -> Lambda(K) ⋊ H` by `h -> h` and `k -> k_(x_0)`.
- `Phi` agrees on the amalgamated `Gamma`.
- For `gamma in Gamma` we have `gamma k_(x_0) gamma^-1 = k_(gamma x_0) = k_(x_0)`, so
  the relations of `Gamma x K` hold.

Define `Psi` back by `h -> h` and `k_(h x_0) -> h k h^-1`.
- *Well defined.* `(h gamma) k (h gamma)^-1 = h k h^-1`, because `gamma` commutes with
  `k`.
- *Free product.* The factors `K_x` carry no relations among themselves, so `Psi` is
  defined on `Lambda(K)`.
- *Semidirect relation.* `Psi(h') Psi(k_(h x_0)) Psi(h')^-1 = h' h k (h' h)^-1
  = Psi(k_(h' h x_0))`.

On generators, `Psi Phi(k) = k`, `Phi Psi(k_(h x_0)) = h k_(x_0) h^-1 = k_(h x_0)`, and
both fix `H`. So both composites are the identity.

**(2)** `Lambda(K) ⋊ H` is the graph wreath over the empty graph on `X`, with no
internal lamp twists. `lef-lamp-graph-wreaths-are-surjunctive` assumes nothing on the
actor or the graph, and gives surjunctivity iff `H` is surjunctive.

**(3)** In `Lambda(K) ⋊ H`,
`[t k_(x_0) t^-1, gamma] = k_(t x_0) (k^-1)_(gamma t x_0)`.
The two sites differ because `gamma` lies outside `t Gamma t^-1`, the stabilizer of
`t x_0`. A reduced word of length two in a free product is nontrivial. Lemma 2 gives
the last clause. QED.

**Corollary 4.1 (defect windows of free centralizers).** For every group `H`, every
subgroup `Gamma` with a strict compressor, and every nontrivial LEF `K`:
- `P = H *_Gamma (Gamma x K)` carries a strict pair iff `H` does;
- `P` has nontrivial compression defects `[t k t^-1, gamma]`, invisible whenever the
  pair is rigid.

For `H = L_(F_2)(1,2)^x` with the nine-leaf pair, the defect windows of a free
centralizer are exactly as hard as Gottschalk's conjecture for `H` itself. The
"compression + centralizing" relations of a free commuting factor carry no strictness,
in either direction.

## 5. Nested defects

**Definition.** A rigid defect `[t z t^-1, gamma]` in `H` is **nested** when
`t z t^-1` lies in `Gamma`.

**Observation 5.1.** The defects of Theorems 3 and 4 are not nested:
- in the wreath, `t a_Gamma t^-1 = a_(t Gamma)` is a lamp, outside `G`;
- in the amalgam, `t k t^-1 = k_(t x_0)` is outside `H`.

Section 6 shows that a nested nontrivial defect in any group lives inside a nonsofic
Kazhdan subgroup. Whether those groups contain one is not decided here.

**Proposition 5.2.** The binary Leavitt unit group carries a nested nontrivial rigid
defect.

*Proof.* Use the nine-leaf configuration of `openai-nine-leaf-leavitt-configuration`
over `R = L_(F_2)(1,2)`:
- `Gamma = EL_alpha(R) ≅ EL_3(R)` and `G = EL_D(R) ≅ EL_9(R)`, both Kazhdan;
- `G = <Gamma, u, v>` with `u, v in P_Gamma`, so `Gamma` is infranormal in `G`;
- `J = V_(1000)` centralizes `Gamma`, and `u J u^-1 = V_(0001) <= Gamma`.

Take `z in J` with `z != 1`. Then `w = u z u^-1` is a nontrivial element of `Gamma`.
`EL_3(R)` is simple and nonabelian (`binary-leavitt-elementary-group-is-simple`), so its
center is trivial and some `gamma in Gamma` has `[w, gamma] != 1`. This defect is rigid
and nested. QED.

**Remark 5.3 (nesting and residual finiteness).** In the OpenAI configuration the
nested factor is non-LEF, and it embeds in `Gamma` through `u`. So `Gamma` is not LEF,
and in particular not residually finite. The Kun--Thom Theorem E pairs have residually
finite `Gamma`, so their wreaths never contain the OpenAI configuration with this `Gamma`.

**Where the architecture stands.**
- Placing the window on a rigid defect adds nothing by invisibility (Theorem 3).
- A free commuting factor adds nothing (Theorem 4).
- The remaining exact content is the nesting relation `t z t^-1 in Gamma`, together with
  whatever relations of the host it drags in.

This is recorded as the open claim `nested-rigid-defects-force-nonsurjunctivity`. Its
payoff through Proposition 5.2 is `leavitt-unit-group-nonsurjunctive`, and hence a
refutation of Gottschalk's conjecture.

A counterexample to the open claim would be a surjunctive group with a nested
nontrivial rigid defect. Such a group is nonsofic (Lemma 2). By
`gottschalk-counterexamples-lie-outside-the-permanence-closure`, if it lies in the
permanence closure `S*`, it contains no finitely presented infinite simple nonsofic
group. No such example is known here.

## 6. Nested defects live inside one nonsofic Kazhdan group

**Proposition 6.1.** Let `Gamma <= G <= H` be a rigid pair, and suppose `t in G`,
`z in C_H(Gamma)` and `gamma in Gamma` satisfy `w = t z t^-1 in Gamma` and
`[w, gamma] != 1`. Then:

1. `z` lies in `G`, so the defect is a rigid defect of the rigid pair `Gamma <= G <= G`;
2. `C_G(Gamma)` is not normal in `G`;
3. `G` is a nonsofic Kazhdan group;
4. nested nontrivial defects exist exactly when some `t in G` has
   `t (C_G(Gamma) ∩ t^-1 Gamma t) t^-1` not contained in `Z(Gamma)`.

*Proof.*
1. `z = t^-1 w t`, and `t` and `w` lie in `G`.
2. `z` lies in `C_G(Gamma)`, but `t z t^-1 = w` does not commute with `gamma`.
3. By (1) the pair `Gamma <= G <= G` carries a nontrivial rigid defect.
   `sofic-groups-kill-rigid-compression-defects` forbids that in a sofic group. With
   ambient group `G`, this is Kun--Thom Theorem B: `C_G(Gamma)` is normal in a sofic `G`.
4. An element `w` of `Gamma` fails to commute with some element of `Gamma` exactly when
   `w` is outside `Z(Gamma)`, and `z = t^-1 w t` ranges over
   `C_G(Gamma) ∩ t^-1 Gamma t`.

QED.

**Corollary 6.2.** `nested-rigid-defects-force-nonsurjunctivity` is equivalent to its
case `H = G`. That case reads: every Kazhdan group `G` with an infranormal Kazhdan
subgroup `Gamma` satisfying (4) is nonsurjunctive.

*Proof.* The case `H = G` is an instance of the claim. Conversely, suppose it holds.
- *The configuration moves into `G`.* Take `H` carrying a nested nontrivial defect.
  By (1) `G` carries the same configuration.
- *The strict pair moves back up.* The case `H = G` gives a strict pair over `G`. Its
  memories lie in `G`, and an automaton over `H` with memory in `G` acts independently
  on the left cosets of `G`. So the same rules form a strict pair over `H`.

QED.

**Corollary 6.3 (where a refutation must live).** A counterexample to the nested-defect
criterion is a surjunctive group that contains a nonsofic Kazhdan group with a nested
nontrivial defect.

Two things are not decided here:
- whether any of the known surjunctive nonsofic groups contains a nonsofic Kazhdan
  subgroup at all (the Kun--Thom wreaths, doubles and graph wreaths, and the free-lamp
  amalgams);
- whether some group of `S*` does.

**Design reading.** The nesting relation is a statement about one Kazhdan group:
- **what is known.** `G = EL_9(L_(F_2)(1,2))` carries it (Proposition 5.2);
- **what a proof needs.** A strict pair built on it must read, in its product tables,
  the failure of Kun--Thom normalization inside `G`;
- **what does not help.** A lamp, ambient extension or free centralizing factor
  contributes nothing (Theorems 3 and 4).
