# Swarm attack on fpbs-normal-subgroup-bounded-cost-fixed-price-one (2026-09-16)

Agent lane: `swarm-fpbs-normal-subgroup-bounded-c`. The target was locked for
the duration of the attack and unlocked at the end. Nothing was committed.

## 1. Setup

**Target (OPEN).** `N` is an infinite normal subgroup of a countable group
`Gamma`, `Q = Gamma/N` is infinite, and every essentially free p.m.p. action
of `N` has cost at most `K < infinity`. Conclusion: `Gamma` has fixed price
one.

Notation used throughout:
- `pi : Gamma -> Q` is the quotient map.
- `rho : Q -> Out(N)` is the outer action. For `gamma in Gamma`, conjugation
  by `gamma` restricts to an automorphism of `N`. Its class in `Out(N)` depends
  only on `pi(gamma)`, because conjugation by elements of `N` is inner.
- `Q_0 = ker rho` is the set of cosets acting on `N` by inner automorphisms.
- A subgroup `H <= L` is wq-normal when every proper subgroup `K` with
  `H <= K < L` admits some `g in L \ K` with `g K g^-1 ∩ K` infinite. This is
  the definition in `fpbs-wq-normal-hull-is-almost-malnormal`.

Established inputs used:
- `fpbs-wq-normal-price-one-subgroup-forces-price-one`. Here `H` is an
  infinite wq-normal subgroup. If `H` has fixed price one, then so does the
  group. As a consequence, an infinite amenable wq-normal subgroup forces fixed
  price one.
- Two elementary observations:
  - A subgroup containing an infinite normal subgroup of `Gamma` is wq-normal:
    `g K g^-1 ∩ K ⊇ N` for every `g`.
  - A normal subgroup is wq-normal in its ambient group.

## 2. What was proved

Full proofs are in
`research/artifacts/fpbs-normal-bounded-cost-quotient-trichotomy-2026-09-16.md`.

### 2.1 Lemma L: an amenable subgroup of the outer kernel

**Lemma L** (`fpbs-amenable-outer-kernel-forces-price-one`, proved). Let `N` be
an infinite normal subgroup of a countable group `Gamma`. Suppose `Q_0`
contains an infinite amenable subgroup `A`. Then `Gamma` has fixed price one.
No cost hypothesis on `N` is needed.

Proof sketch.
- Let `Lambda = pi^-1(A)` and `C = C_Gamma(N) ∩ Lambda`.
- `pi(C) = A`. For `gamma in Lambda`, conjugation by `gamma` on `N` equals
  conjugation by some `a in N`, so `a^-1 gamma` centralizes `N` and has the
  same image.
- `C ∩ N = Z(N)` is abelian. So `C` is an extension of an abelian group by
  `A`, hence infinite and amenable.
- `C` is normal in `Lambda`.
- The consequence of the wq-normal claim gives `Lambda` fixed price one. The
  claim itself then lifts this to `Gamma`, since `Lambda ⊇ N`.

### 2.2 Proposition R: the quotient trichotomy reduction

**Proposition R** (route `fpbs-bounded-cost-normal-via-quotient-trichotomy`).
The target follows from Lemma L, the wq-normal claim and the three special
cases below. Each uses the target's standing hypothesis: `N` is infinite and
every free action of `N` has cost at most `K`.
- **(Z')** `N semidirect_phi Z` has fixed price one when `phi` has infinite
  order in `Out(N)`. Id: `fpbs-bounded-cost-outer-cyclic-extension-price-one`.
- **(LF')** `Gamma` has fixed price one when `Q` is infinite locally finite
  and `Q_0` is finite. Id: `fpbs-bounded-cost-locally-finite-outer-price-one`.
- **(T')** `Gamma` has fixed price one when `Q` is infinite, finitely
  generated and torsion, and `Q_0` contains no infinite amenable subgroup. Id:
  `fpbs-bounded-cost-fg-torsion-quotient-price-one`.

Proof sketch. If `Q_0` contains an infinite amenable subgroup, Lemma L
applies. Otherwise:
- **(a) `Q` has an element `q` of infinite order.**
  - Then `<q> ∩ Q_0 = 1`.
  - Pick `gamma in pi^-1(q)`. Then `pi^-1(<q>)` is isomorphic to
    `N semidirect_phi Z`, where `phi` is conjugation by `gamma`.
  - `phi` has infinite order in `Out(N)`, so (Z') applies.
  - The subgroup `pi^-1(<q>)` contains `N`, so it is wq-normal.
- **(b) `Q` is torsion and locally finite.**
  - Then `Q_0` is locally finite, hence amenable, hence finite by assumption.
  - (LF') applies.
- **(c) `Q` is torsion with an infinite finitely generated subgroup `A`.**
  - The outer kernel of `pi^-1(A)/N = A` is `A ∩ Q_0`, which has no infinite
    amenable subgroup.
  - (T') applies to `pi^-1(A)`, and wq-normality lifts the conclusion.

The three cases are exhaustive. Conversely, each of (Z'), (LF') and (T') is a
special case of the target. So the target is equivalent to their conjunction.

### 2.3 Downstream routes with weaker premises

- **3-manifolds** (route `fpbs-hyperbolic-3-manifold-via-outer-cyclic-extension`).
  - Take a fibered finite cover with group `pi_1(S_g) semidirect_phi Z`.
  - If `phi` has infinite order in `Out`, apply (Z').
  - If `phi` has finite order `k`, the outer kernel is `kZ`, and Lemma L
    applies.
  - Transfer back through finite index.
  - So the 3-manifold case needs only (Z'), not the target.
- **Burnside** (route `fpbs-burnside-upper-cost-one-via-fg-torsion-quotient`).
  - For `G = B(m,n) = N semidirect H`, with `H ≅ B(m-1,n)`, the outer kernel
    is `pi(C_G(N))`.
  - `C_G(N) ⊆ C_G(x_1)`, which is cyclic, so the kernel is finite. So (T')
    applies with `K = 2`.
  - The Burnside branch therefore needs only (T').

### 2.4 Remarks recorded (not promoted)

- **(LF') is vacuous in some cases.** Suppose every locally finite subgroup of
  `Out(N)` is finite. Then `rho(Q)` is finite, so `Q_0` is infinite. This
  happens, for instance, when `Out(N)` is virtually torsion-free: a torsion
  subgroup meets a torsion-free normal subgroup of finite index trivially, so
  it embeds in the finite quotient.
  - Examples believed standard but **not verified in this session**: `Out(F_n)`
    (Baumslag--Taylor) and mapping class groups of closed surfaces.
- **Further harmless assumptions.** In the target one may also assume two
  things. Otherwise the wq-normal claim already concludes.
  - `N` does not have fixed price one.
  - `Gamma` has no infinite amenable wq-normal subgroup. In particular `Z(N)`
    and the amenable radical of `N` are finite.
- **Refining (LF').** Every infinite locally finite group has an infinite
  abelian subgroup (Hall--Kulatilaka, Kargapolov; **unverified here**). If
  that is used, (LF') could be refined to a few abelian types of quotient.
  This was not used in any node.

## 3. Approaches tried and where they die

1. **Direct proof of (Z'): exploit the cyclic quotient.** Every known cost-one
   argument for `N semidirect Z` needs one of the following.
   - An `N`-invariant factor. This is Theorem A, which fails when `N` acts
     ergodically, as in the Bernoulli shift.
   - Connectivity of twisted level percolation. This is refuted at low
     density by `fpbs-twisted-level-percolation-disconnected-at-low-density`.
   - A correlated transport set, which is still open.
   - The literal Khezeli horoball metric, which needs finite conjugacy orbits.

   Nothing new was found beyond the recorded obstructions.
2. **Slutsky's product-neighbourhood test for `pi_1(M')`.**
   - The aim was either to find sets passing the test or to prove that none
     exist.
   - The obstruction attempt compared twisted and untwisted multiplicative
     energies of a finite set, using non-inner-amenability of the group.
   - **Where it dies:** this gives only a constant-factor comparison between
     the energies. It does not bound the untwisted energy by `O(|F|^2)`, so it
     neither proves nor excludes the criterion.
   - Ruzsa-type covering bounds lose a factor at each iteration and do not
     iterate.
   - This was exploratory and nothing is claimed.
3. **(LF') by exhaustion and finite-index costs.**
   - Write `Q` as an increasing union of finite groups `Q_n`, and let
     `Gamma_n = pi^-1(Q_n)`.
   - Absorbing each element of `Gamma` on a small complete section of `R_N`
     gives `C(Gamma↷X) <= inf_n C(Gamma_n↷X)`.
   - The coset extension has
     `C(Gamma_n↷X x Gamma_n/N) = 1 + (C(N↷X)-1)/|Q_n|`, which tends to one.
   - **Where it dies:** passing from the coset extension back to `X` needs
     `C(X) <= C(X x F)` for a uniform finite-fibre extension.
     `fpbs-finite-fiber-cost-bound` gives only
     `C(X) <= 1 + q(C(Y)-1) = C(N↷X) <= K`. Equality is exactly the open
     finite-index multiplicativity question.
   - Pseudocost exhaustion (Tucker-Drob, arXiv:1211.6395, Prop. 6.7, as
     recorded in `fpbs-fixed-price-countable-from-finitely-generated`) gives
     only `PC <= liminf C(Gamma_n↷X) <= K`.
4. **(LF') through the ergodic decomposition of `R_N`.**
   - `Q` acts on the space `Z` of `N`-ergodic components.
   - If this action is free, Theorem A gives cost one, because `Q` is amenable.
   - **Where it dies:** in the Bernoulli shift `Z` is a point and the
     stabilizer is all of `Q`. Intermediate invariant random subgroups of `Q`
     are not handled.
5. **(T') when `Q_0` is infinite without infinite amenable subgroups.**
   - Take an infinite finitely generated `B_0 <= Q_0`, and set
     `Gamma_0 = pi^-1(B_0) = N C`, where `C = C_Gamma(N) ∩ Gamma_0`.
   - `N` and `C` commute and `N ∩ C = Z(N)`. If `Z(N)` is infinite, Lemma L
     applies.
   - **Where it dies:** if `Z(N)` is finite, `Gamma_0` is a quotient of
     `N x C` by a finite central subgroup.
     - Khezeli's theorem covers `N x C`. The passage to a finite central
       quotient is not established.
     - The class-bijective extension from a free `N x C` action over `X` bounds
       cost in the wrong direction.
     - A measurable lift of a free `Gamma_0`-action to a free `N x C` action
       needs a vanishing 2-cocycle.
6. **Finite-index and compact-extension tricks for (Z').**
   - Replacing `phi` by `phi^k` changes nothing, since fixed price one passes
     up finite index by wq-normality.
   - Gaboriau's normal criterion bounds `C(Gamma↷X)` only by `C(N↷X) <= K`.

## 4. Literature gate (checked 2026-09-16)

WebSearch was unavailable in this session because its budget was exhausted.
The gate used the arXiv export API: lexical queries, then an `id_list` query
to verify the metadata of every arXiv source cited here.

Queries on 2026-09-16:
- **`all:"fixed price"`, math categories, newest first.** 2607.20273, Slutsky,
  "A Product-Neighbourhood Criterion for Fixed Price One", 2026-07-22; 2510.05459,
  Bevilacqua--Bowen, "Metric criteria for fixed price of countable groups",
  2025-10-06; 2509.08325v4, Khezeli, "Products of Infinite Countable Groups
  Have Fixed Price One", 2025-09-10; 2504.02435, Grebík--Recke, "Poisson-Voronoi
  percolation in higher rank"; 2307.11728, Mellick, "Gaboriau's criterion and
  fixed price one for locally compact groups"; 2307.01194,
  Fraczyk--Mellick--Wilkens, "Poisson-Voronoi tessellations and fixed price in
  higher rank"; 2102.07710, Abért--Mellick; 1810.11015, Hutchcroft--Pete,
  "Kazhdan groups have cost 1".
- **Burnside and cost.** 2608.20472, Donoso-Echenique--Silva, "Free Burnside
  groups of large odd exponent have cost 1", 2026-08-20. This gives infimal
  cost, as recorded in the target.
- **Khezeli as author.** 2606.30517 (D'Achille--Khezeli, Poisson--Voronoi,
  Diestel--Leader); 2603.19717 (Baccelli--Khezeli, one-or-two-ended forests);
  2511.23317 (Voronoi percolation on products). None concerns extensions.
- **Gaboriau as author.** No new cost result.
- **2608.20165.** Wróbel, "Orbit equivalence and total weak mixing of free
  group actions", 2026-08-20. Not relevant.
- **`abs:"fixed price" AND abs:"normal subgroup"`.** No hits.
- **`abs:"cost" AND abs:"mapping torus"`.** No hits.
- **`abs:"fixed price" AND abs:"3-manifold"`.** 2102.07710 and math/0701361
  (Abért--Nikolov). Both old.
- **1211.6395.** Tucker-Drob, "Shift-minimal groups, fixed price 1, and the
  unique trace property". Used only through the repository's existing record.

**Conclusion.** No source found resolves the target, fixed price for
fibered hyperbolic 3-manifold groups, or the upper cost of large odd Burnside
groups. The status stays OPEN. **Limitation:** the arXiv API search is lexical
and not exhaustive, and journals and MathOverflow were not searched.

## 5. Candid assessment

- Lemma L and Proposition R are elementary, and I am confident they are
  correct. They are a genuine reduction but not a breakthrough.
- (Z') still contains the fibered hyperbolic 3-manifold case, which is open.
  (T') still contains the Burnside case.
- The practical gains:
  - The 3-manifold and Burnside branches now depend on strictly smaller
    premises.
  - Finite-order monodromy and amenable inner parts are removed for good.
  - (LF') is vacuous for a broad class of `N`.

## 6. Validation

**Command.** `check.sh` was run on the eight new research nodes and the
artifact, against landed `b30d892f0`.

**Result.** It exited 0.
- `fpbs-amenable-outer-kernel-forces-price-one` is established.
- The 3-manifold route is missing only (Z').
- The Burnside route is missing only (T').
- The similarity notes against Lemma L are answered by `distinct_from`
  entries. Neither (LF') nor (T') is decided by L, since both assume the
  outer kernel has no infinite amenable subgroup.

## Referee (2026-09-16)

**What was checked.**
- Read all ten solver files in full, together with the committed nodes they
  use: the target, `fpbs-wq-normal-price-one-subgroup-forces-price-one` and
  its proof route, `fpbs-wq-normal-hull-is-almost-malnormal`,
  `fpbs-fibered-3-manifold-cost-inputs`, `fpbs-burnside-normal-closure-split`,
  `fpbs-burnside-common-upper-cost`, `fpbs-burnside-embedding-input`,
  `fpbs-burnside-upper-cost-one-via-normal-closure`,
  `fpbs-finite-fiber-cost-bound`, and the two root claims. `git status` shows
  no further files under this lane's slugs.
- **Lemma L.** Checked each step line by line.
  - `C_Gamma(N)` is normal in `Gamma`, so `C = C_Gamma(N) ∩ Lambda` is normal
    in `Lambda`.
  - `pi(C) = A` uses only that `A` acts by inner automorphisms.
  - `C ∩ N = Z(N)`, so `C` is abelian-by-`A`: infinite and amenable.
  - Infinite normal subgroups, and overgroups of an infinite normal subgroup
    of `Gamma`, are wq-normal under the intermediate-subgroup definition.
  - Weakest step (i) of the report: the amenable consequence of the wq-normal
    claim is covered by that claim's own proof route (Theorem 2.20 of
    Gaboriau's notes, Ornstein--Weiss). So Lemma L is sound as a COMPLETE
    route over one established premise.
- **Proposition R.** Checked the following.
  - The trichotomy is exhaustive.
  - `<q> ∩ Q_0 = 1` in case (a).
  - The isomorphism `(u,k) -> u gamma^k` onto `pi^-1(<q>)` is a homomorphism,
    injective and onto.
  - The outer class has infinite order.
  - In case (b), a finite `Q_0` follows from local finiteness.
  - In case (c), the restricted outer kernel is `A ∩ Q_0`.
  - The converse: each of Z', LF' and T' is a special case of the target.

  No hidden finite-generation or ergodicity assumption was found. The route
  correctly lists all five premises.
- **3-manifold route.** Correct over its premises.
  - The finite-order branch never occurs for closed hyperbolic mapping tori,
    but covering it is harmless.
  - The finite-index transfer is item 3 of the inputs.
- **Burnside route.** Correct over its premises.
  - The equality `Q_0 = pi(C_G(N))` reuses step 1 of Lemma L, which does not
    use amenability.
  - `C_G(N) <= C_G(x_1)` is cyclic, hence finite in exponent `n`, as in
    `fpbs-burnside-normal-closure-split`.
  - Weakest step (ii) of the report is the same reading as that established
    split lemma.
- **Attempts sections.** Spot-checked the arithmetic.
  - The induced cost of the coset extension is
    `1 + (C(N↷X)-1)/|Q_n|`.
  - The upper bound `1 + q(C(Y)-1)` of `fpbs-finite-fiber-cost-bound` then
    returns exactly `C(N↷X)`.
  - A characteristic infinite `Z(N)` is normal in `Gamma` and forces fixed
    price one.

  All referenced node ids exist. `fpbs-twisted-level-percolation-connected`
  is indeed REFUTED.
- **Duplicates.** Ran `bin/cairn search --similar` for the four new claims.
  No existing claim duplicates them. The nearest are the wq-normal claim and
  the target, and both are answered by `distinct_from`.
- **Literature.** WebSearch was unavailable (budget exhausted).
  - The arXiv export API confirmed the metadata of 2608.20472
    (Donoso-Echenique--Silva, 2026-08-20), 2607.20273 (Slutsky, 2026-07-22),
    2509.08325 (Khezeli, 2025-09-10) and 2510.05459 (Bevilacqua--Bowen,
    2025-10-06).
  - A newest-first `all:"fixed price"` query in math showed nothing after
    2607.20273.
  - No resolution of the target, the 3-manifold claim or the Burnside claim
    was found. The status stays OPEN.
- **Novelty.** Lemma L and Proposition R are elementary. They are presented
  as a reduction, not as progress on the core difficulty, and that is an
  accurate description.

**What was changed.** In `fpbs-bounded-cost-outer-cyclic-extension-price-one`,
the vague references "Remark H of the normal-subgroup note", "Proposition F"
and "the notes file of 2026-09-16" now name their files.

**Verdict.** Sound. Landed with that minor fix.
- Established: Lemma L (`fpbs-amenable-outer-kernel-forces-price-one`).
- Open: the target, which is now equivalent to the conjunction of Z', LF' and
  T'.
- The 3-manifold and Burnside roots now each wait on a single special case.
