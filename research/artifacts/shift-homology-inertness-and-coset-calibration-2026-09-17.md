# Shift homology is inert under automata over groups; coset-shift calibration

Lane (e) of `notes/agent-coordination-playbook-2026-09-17.md`, "Hopfian subshift
invariant", agent `a-gs-cohopfian`, 2026-09-17. Target cone:
`gottschalk-surjunctivity-conjecture`. Script:
`experiments/cohopfian-shift-homology-2026-09-17/check.py` (exact checks of every
finite computation below).

## 0. The approach being tested

A strict automaton `tau` (injective, not surjective) on `X = A^G` has a continuous
left inverse `sigma` with `sigma tau = id`. On any contravariant functor `F`,
`tau^* sigma^* = id`, so `tau^*` is split surjective. The co-Hopfian program
asks for a functorial size `F(X)` that is Hopfian, so that a split surjective
`tau^*` with nonzero kernel is impossible. The candidates named in the lane are:
- the type-semigroup class of a clopen partition;
- the `K_0` class of its characteristic projections in `C(X) x| G`.

Both factor through, or are tested against, the equivariant homology
`H_*(G; C(X, Z))`, where `C(X, Z)` is the module of continuous integer
functions with `(g f)(x) = f(g^-1 x)` and `(g x)(w) = x(g^-1 w)`.
- For `G = F_n`, the Pimsner–Voiculescu sequence with `K_1(C(X)) = 0` gives
  `K_0(C(X) x| F_n) = H_0(F_n; C(X,Z))` and
  `K_1(C(X) x| F_n) = H_1(F_n; C(X,Z))`.
- This is a remark only. Nothing below depends on it.

## 1. Permutation basis lemma

Let `Omega` be a `G`-set, `A` finite with `|A| >= 2`, `a0 in A`, and
`A' = A \ {a0}`. For finite `F ⊂ Omega` and `c : F -> A'` put
`e_{F,c}(x) = prod_{w in F} [x(w) = c(w)]`. Here `e_{∅} = 1`.

**Lemma 1.** The `e_{F,c}` form a `Z`-basis of `C(A^Omega, Z)`. Moreover
`g e_{F,c} = e_{gF, c o g^-1}`. Hence
`C(A^Omega, Z) = Z·1 ⊕ ⊕_{[F,c], F ≠ ∅} Z[G/G_{F,c}]` as `ZG`-modules, where
`G_{F,c}` is the stabilizer of the pattern, contained in the setwise stabilizer
of `F`.

*Proof.*
1. `C(A^Omega, Z)` is the direct limit over finite windows `W` of
   `Z^(A^W) = ⊗_{w in W} Z^A`.
2. `Z^A` has basis `{1} ∪ {delta_a : a in A'}`. So `Z^(A^W)` has basis the
   tensor products of these vectors, which are exactly the `e_{F,c}` with
   `F ⊆ W`.
3. These bases are compatible with enlarging `W`, so their union is a basis of
   the limit. The script checks unimodularity for `|A| in {2,3}` and `|W| <= 3`.
4. For the action: `e_{F,c}(g^-1 x) = prod_{w in F}[x(gw) = c(w)] = e_{gF, c o g^-1}(x)`.
5. So `G` permutes the basis. A permutation module on a basis is the direct sum
   of `Z[G/stabilizer]` over the orbits. ∎

## 2. Theorem A (inertness)

**Theorem A.** Let `G` be a group and `A` a finite alphabet. For `n >= 1`, the
inclusion of constants `iota : Q -> C(A^G, Q)` induces an isomorphism
`H_n(G; Q) -> H_n(G; C(A^G, Q))`. When `G` is torsion-free, the same holds
over `Z`.

Consequently, for every automaton `tau : A^G -> B^G` (continuous and
equivariant), the map `tau^* : H_n(G; C(B^G,Q)) -> H_n(G; C(A^G,Q))` is the
canonical identification with `H_n(G;Q)`. In particular every self-automaton,
strict or not, acts as the identity on `H_n(G; C(A^G, Q))` for `n >= 1`.

More generally, let `Y` be any compact totally disconnected `G`-space and
`Phi : Y × A^G -> Y × A^G` any equivariant continuous map with
`pr_Y o Phi = pr_Y`. Then `Phi^*` is the identity on `H_n(G; C(Y × A^G, Q))`
for `n >= 1`.

*Proof.*
1. **Finite stabilizers.** For `Omega = G` and nonempty finite `F`, `gF = F`
   forces `g in F F^-1`, so `G_{F,c}` is finite.
2. **Projectivity.** For finite `H`, `e_H = |H|^-1 sum_{h in H} h` is an
   idempotent of `QG`. Then `Q[G/H] ≅ QG e_H` is a direct summand of `QG`,
   hence projective.
3. **Vanishing.** `H_n(G; M) = Tor_n^{ZG}(Z, M)`. For a `QG`-module `M` this is
   `Tor_n^{QG}(Q, M)`, by flat base change `ZG -> QG`. Tor vanishes on
   projectives in degree `n >= 1` and commutes with direct sums.
4. **Conclusion.** By Lemma 1, `C(A^G,Q) = Q ⊕ P` with `P` projective, so
   `H_n(G; C) = H_n(G; Q)` via `iota`.
5. **Torsion-free case.** All stabilizers are trivial and `P` is free over
   `ZG`, so the same argument works over `Z`.
6. **Automata.** `tau^*(f) = f o tau` is a `ZG`-module map and fixes `1`, so
   `tau^* o iota_B = iota_A`. Functoriality of `H_n(G; -)` then gives the
   claim.
7. **Fibred version.** Locally constant functions on a product of compact
   totally disconnected spaces form the algebraic tensor product. So
   `C(Y × A^G, Q) = C(Y,Q) ⊕ ⊕ C(Y,Q) ⊗ Q[G/H]` with finite `H`, carrying the
   diagonal action.
8. `M ⊗ Q[G/H] ≅ QG ⊗_{QH} Res_H M`, via `m ⊗ gH -> g ⊗ g^-1 m`.
   `Res_H M` is projective over `QH` by Maschke, and induction preserves
   projectives. So `H_n(G; C(Y × A^G,Q)) = H_n(G; C(Y,Q))` for `n >= 1`, via
   `u -> u ⊗ 1`.
9. `Phi^*(u ⊗ 1) = u o pr_Y o Phi = u ⊗ 1`, so `Phi^*` fixes that image. ∎

**Calibration on a real strict map over a group.** Apply the fibred version to
the hotel map `Phi(φ, x) = (φ, x o f_φ)` of
`nonamenable-groups-carry-arrow-shift-strict-automata`, taking `Y = X_S`.
- That map is strict over every nonamenable group.
- It covers `id_{X_S}`, so it acts as the identity on positive-degree rational
  homology.
- So the invariant is blind to strict maps that genuinely exist over groups. It
  does not merely fail to be monotone.

## 3. Degree 0 reduces to the measure lane

`H_0(G; C(X,Z))` is the coinvariants. For a full shift it is free abelian on
`G \ Pat`, with unit `[1]` and positive cone the image of the nonnegative
functions.
- **Split surjective, non-injective.** Let `tau` be strict. The image
  `tau(X)` is closed and proper, so its complement contains a cylinder `U`.
  Then `tau^*[1_U] = [1_{tau^-1 U}] = 0`. But `[1_U] ≠ 0`, because the
  Bernoulli trace `t(e_{F,c}) = |A|^-|F|` is a well-defined positive functional
  on `H_0` with `t(1_U) > 0`.
- **States are invariant measures.** A unital positive homomorphism
  `s : H_0 -> R` is a finitely additive `G`-invariant probability on clopens.
  It is countably additive on the clopen algebra by compactness, so it extends
  to a `G`-invariant Borel probability `mu`, and conversely.
- **What a proof via states needs.** `s o tau^* = s` iff `tau_* mu = mu`. The
  inequality `s o tau^* >= s` on the cone already forces equality, because both
  sides are probabilities. So a state-based monotone argument is exactly a
  `tau`-invariant, `G`-invariant measure charging a Garden-of-Eden cylinder. By
  the proof of `injective-measure-preserving-ca-is-surjective`, this is the
  measure lane (`every-injective-ca-preserves-uniform-bernoulli-measure` and
  its relatives). Nothing new is available in degree 0 through states.
- **Link to the index lane.** For `G = F_n`, `K_0` of the crossed product is
  this `H_0`. So candidate 2 (the `K_0` class) is the degree-0 case, and
  its states were already recorded as dead by the index lane attempt on
  `gottschalk-surjunctivity-conjecture`.
- **No Hopficity.** `H_0` is an infinitely generated free abelian group, so a
  split surjective endomorphism with kernel is no contradiction in itself.

## 4. Calibration: the BS(1,2) coset shift (discrete end-fixing tree)

**Setup.**
- `G = BS(1,2) = Z[1/2] x| Z`, with `t a^r t^-1 = a^(2r)`.
- `K = <a> = Z`, and `V = G/K` is the vertex set of the Bass–Serre tree `T_3`.
- `c = t^-1`, so `c^-1 K c = t K t^-1 = <a^2>`, which is proper in `K`.

**Parent map.** `p(gK) = g t^-1 K` is well defined, because
`k t^-1 K = t^-1 k^2 K`.
- It is `G`-equivariant and surjective, with fibres of size 2.
- `G_{p(eK)} = t^-1 K t = <a^(1/2)>`, and `[G_{p(v)} : G_v] = 2`.
- This is the discrete version of `end-fixing-tree-symmetries-carry-strict-automata`,
  and the automaton `tau(x)(v) = x(p(v))` is strict there. The script checks
  all of this.

**Degree 1 is not inert.** Take `A = {0,1}` and `a0 = 0`.
1. `tau^* e_F = e_{p(F)}`, so the singleton summand `Q[V] ⊂ C(A^V, Q)` is
   `tau^*`-stable, with `tau^* e_{v} = e_{p(v)}`.
2. By Eckmann–Shapiro, `Q[G/K] = QG ⊗_{QK} Q` and `QG` is free over `QK`. So
   `H_1(G; Q[V]) = H_1(K; Q) = Q`.
3. The module map `v -> p(v)` factors as the projection
   `G/K -> G/L` with `L = t^-1 K t`, followed by the isomorphism
   `G/L -> G/K`, `gL -> g t^-1 K`.
   - The projection induces corestriction `H_1(K) -> H_1(L)`. It sends `[a]`
     to `2[a^(1/2)]`, since `a = (a^(1/2))^2`.
   - The isomorphism induces conjugation `h -> t h t^-1`, with
     `t a^(1/2) t^-1 = a`.
4. So `tau^*` acts on `H_1(G; Q[V]) = Q` as multiplication by `2`.
5. `Q[V]` is a direct summand, so this `Q` injects into `H_1(G; C(A^V,Q))`.
   Hence `tau^* ≠ id` there.

The eigenvalue is the compression index `[G_{p(v)} : G_v] = 2`, which is the
modular ratio of lane (c). The homological trace of the modular imbalance lives
exactly in the degree that Theorem A makes inert over groups.

**Where Theorem A needs a group property.** The step used is step 1 of
Theorem A: setwise stabilizers of finite site sets are finite, which makes the
permutation modules projective. On `V` the stabilizers are conjugates of
`K ≅ Z`, so `Q[V]` is not projective, and `H_1(K;Q) ≠ 0` survives.

**Degree 0 on the calibration.** It has every structural feature of §3:
- free on orbits, a unit, a cone and an invariant trace;
- `tau^*` split surjective and non-injective;
- `1_U = e_c - e_{c,c'} -> 0` for siblings `c, c'`, with kernel element
  `[e_{c,c'}] - [e_v]`.

Only `t o tau^* = t` fails: `t(e_{c,c'}) = 1/4` but
`t(tau^* e_{c,c'}) = t(e_{p(c)}) = 1/2`. Degree 0 separates the tree from
groups only through the Bernoulli trace, which is the existing measure lane.

## 5. Candidate 1: type-semigroup class of the one-site partition

`tau^*[U] = [tau^-1 U]` is a well-defined unital endomorphism of the type
semigroup, because pieces pull back and `tau^-1(gU) = g tau^-1 U`. It kills
the class of every Garden-of-Eden cylinder. Equidecomposition implies equal
`H_0` classes, so §3 applies.

**Not a conjugacy invariant, over every nontrivial group.**
1. Fix `s ≠ e` and `A = {0,1,2}`, and let
   `tau(x)(g) = swap_{1,2}(x(g))` if `x(gs) = 0`, and `x(g)` otherwise.
2. `tau` is an involution, since the condition sees only whether a letter is
   `0`, and `tau` never changes that. So `tau` is bijective.
3. Let `nu` be uniform Bernoulli on `{0,1}^G ⊂ A^G`. The site marginal is
   `(1/2, 1/2, 0)` for the partition `[0]_e, [1]_e, [2]_e`, and `(1/2, 1/4, 1/4)`
   for `tau^-1` of it.
4. Equidecomposable sets have equal mass under every invariant measure, and
   the two mass vectors are not permutations of each other. So no bijection
   matches the one-site partition with its pullback class by class.

**On the calibration.** `tau^-1 [a]_v = [a]_{p(v)} = g [a]_v` for any `g` with
`gv = p(v)`, so the strict parent-copy automaton fixes every one-site class. It
is not monotone there, and it is fixed rather than decreased.

## 6. What survives

- **Rational homology of positive degree:** dead for full shifts over groups
  (Theorem A), and even for fibred strict maps over arrow shifts.
- **Integral torsion in positive degree** for groups with torsion: it is
  concentrated in `⊕ H_n(G_{F,c}; Z)` over finite stabilizers. Theorem A does
  not settle whether `tau^*` acts there as a permutation-like map, and no
  monotonicity is visible there.
- **Cohomology `H^n(G; C(A^G, Z))`:** not covered by Theorem A.
  - Finite-stabilizer permutation modules have nonzero `H^1`, which is end or
    boundary data. For example `H^1(F_2; Z[F_2]) ≠ 0`.
  - For finitely presented `G`, `H^1` commutes with the direct sum of Lemma 1,
    and `tau^*` does not preserve summands (`e_{c,c'} -> e_{p(c)}` on the tree).
  - Whether `tau^*` can be split surjective with kernel on `H^1` is open. It
    would still need a Hopficity principle.
  - This is the only candidate left in this family, recorded as a spark.

## 7. Verdict for lane (e)

**Killed:** co-Hopfian proofs through functorial equivariant homology of the
shift coefficient module.
- **Positive degree.** Every such invariant is constant on all automaton maps
  over groups (Theorem A). It dies at the step "inclusion of constants is an
  isomorphism", which uses finiteness of stabilizers of finite site sets.
- **Degree 0.** The invariant reduces to invariant measures, which is the
  existing measure-preservation lane.

**Calibration.**
- On the BS(1,2) coset shift the invariant is non-inert, with eigenvalue 2,
  exactly where Theorem A's group property fails.
- On the arrow-shift hotel map it is inert, despite strictness.

No new decomposition with independently failable prerequisites came out of
this lane.
