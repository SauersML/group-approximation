# Swarm attack on `sl3-laurent-f2-is-flexibly-hs-stable` (2026-09-16)

Agent: `swarm-sl3-laurent-f2-is-flexibly-hs-` (lock held 2026-09-16, released
at the end of the run).  Nothing committed.

## 0. Outcome in one paragraph

The target stays **OPEN**; no 2024--2026 source settles it.  The run
produced one new claim (status computed by the graph, not declared here),
`laurent-sln-fq-lattices-are-charfinite`, with the route
`laurent-sln-fq-lattices-charfinite-proof`.  It imports Bader--Boutonnet--
Houdayer--Peterson Theorem A (arXiv:2009.09952v3) over `F_q(t)` after checking
every hypothesis, and derives:
- for every group commensurable with `SL_n(F_q[t,1/t])`, `n >= 3`: the radical
  is scalar, extremal characters are finite or central (character rigidity),
  normal subgroups are finite central or of finite index, and finite-dimensional
  unitary representations have finite image;
- for `A = SL_3(F_2[t,1/t])`: `A` is ICC, every character is uniquely
  `s·delta_e + sum c_i tr∘pi_i`, and a model's limit algebra has no injective
  summand iff its limit trace is `delta_e`, in which case it is `L(A)`.

This removes the "character rigidity; not verified for this group in the graph"
caveat from the target's Kazhdan-projection splitting sketch.  It is **not** a
smaller reduction of the target: the `delta_e` restriction already follows from
existing graph nodes, and the known unstable Kazhdan group has its witness at
`delta_e`.  Outcome recorded as `status_update`.

## 1. Setup

- **Target.**  `A = SL_3(F_2[t,1/t])` is flexibly HS-stable (Dogon,
  arXiv:2211.10492, Definition 1.2): every asymptotic representation
  `alpha_n: A -> U(d_n)` is normalized-HS close to the compression of a genuine
  representation on `C^(D_n) ⊇ C^(d_n)` with `D_n/d_n -> 1`.
- **Consumers.**  `stable-host-from-laurent-hecke-pair` (stable host with the
  co-dense Kazhdan subgroup `SL_3(F_2[t])`), feeding
  `hnn-over-codense-kazhdan-subgroup-not-hyperlinear` and the Kun--Thom doubles.
- **Known facts in the graph used here.**
  - `A` has (T): `elementary-groups-over-fg-rings-have-property-t`, plus
    `SL_3 = EL_3` over the Euclidean ring `F_2[t,1/t]`.
  - Strict stability fails: `infinite-hyperlinear-kazhdan-group-is-not-hs-stable`.
  - `kazhdan-hs-instability-lives-on-properly-nonamenable-limits` (A1)--(A3):
    amenable traces of a Kazhdan group are atomic, and stability reduces to
    models with no injective summand in the limit algebra.
  - `residual-finite-regularization-removes-the-weak-ucp-quantifier` and
    `kazhdan-weak-ucp-stability-is-flexible-stability`: for residually finite
    Kazhdan groups, flexible stability is equivalent to correcting every
    hyperlinear approximation, i.e. every model with limit trace `delta_e`.
  - Cohomological mechanisms are void: Harder's vanishing
    (`harder-function-field-s-arithmetic-cohomology-vanishing`) gives
    `H^2(A(f), R) = 0` on congruence subgroups, and
    `laurent-sl3-central-covers-never-witness-instability` handles central covers.
  - `A` is finitely presented, so the infinitely-presented corollary of
    `kazhdan-cover-models-round-iff-kernel-fixed-mass-one` does not apply.
- **Building.**  `A` is dense in `SL_3(F_2((t)))` and the Iwahori subgroup is
  open, so `A` is transitive on chambers of the `t`-adic building.  The vertex
  stabilizers are conjugates of `SL_3(F_2[t])`; edge and chamber stabilizers
  have index 7 and 21 in a vertex stabilizer (points/lines and flags of
  `PG(2,2)`).

The one hole locked and attacked was the target itself.

## 2. External literature gate (dated)

Question asked: has anyone (2024--2026) proved or refuted flexible HS
stability for `SL_3(F_2[t,1/t])`, for `SL_n` over a Laurent ring, or for any
higher-rank lattice in positive characteristic?  Answer found: **no**.  Status
of the target on 2026-09-16: OPEN.

- **Dogon--Vigdorovich, arXiv:2506.20843v2.**  The equivalence "character rigid
  iff hyperfinitely HS-stable" and the corner theorems are for lattices in real
  Lie groups.  Already in the graph as
  `character-rigidity-equals-hyperfinite-hs-stability`.  Hyperfinite stability
  is automatic for Kazhdan groups ((A2) of the graph node), so this gives nothing
  beyond it for flexible stability.
- **Fournier-Facio, arXiv:2512.09180v2.**  Concerns Frobenius-norm stability,
  not normalized-HS flexible stability of lattices.  No bearing on the target.
- **Dogon, arXiv:2211.10492.**  Definitions 1.2 and 1.5 and Theorem 1.3
  (central-extension instability) are the definitions and mechanism already
  used in the graph.  No statement about function-field lattices.
- **Becker--Lubotzky, arXiv:1809.00632.**  TeX source read on 2026-09-16
  (Definition 1.1; the flexible variant in section 4.4).  Excludes strict
  stability for infinite hyperlinear Kazhdan groups, already in the graph.
- **Bader--Boutonnet--Houdayer--Peterson, arXiv:2009.09952v3** (12 April 2022;
  Invent. Math. 229 (2022) 929--985).  TeX source `main.tex` read on
  2026-09-16.  **Theorem A covers arithmetic groups of product type over any
  global field**, including `F_q(t)`, and gives charfiniteness under a (T)
  place with unbounded image, when `S` is finite or `G` is simply connected.
  This is the input imported below.
- **Dogon--Glasner--Gorfine--Hanany--Levit, arXiv:2507.21862v1** (29 July
  2025).  TeX source `arXiv_v1.tex` read on 2026-09-16.  Non-uniform
  higher-rank lattices are character rigid; the semisimple groups allowed are
  products over arbitrary local fields, and their section 8 states that in the
  product-type case charfiniteness is BBHP Theorem A.  Used only as a
  cross-check.  Character rigidity is not HS stability.
- **Bader--Boutonnet--Houdayer, arXiv:2112.01337.**  Fetch failed
  (connection reset by peer at the agent proxy).  **Unverified; not relied
  upon.**

Verdict: charfiniteness of the Laurent lattices is available from the
literature (with hypotheses checked in the route).  Flexible HS stability of
any higher-rank lattice, in any characteristic, was not found proved or
refuted in the sources checked.

## 3. What was proven: charfiniteness of the Laurent lattices

New files:
- `research/laurent-sln-fq-lattices-are-charfinite.md` (claim);
- `research/laurent-sln-fq-lattices-charfinite-proof.md` (route; requires
  `elementary-groups-over-fg-rings-have-property-t` and
  `kazhdan-hs-instability-lives-on-properly-nonamenable-limits`).

Search before inventing: `character rigid`, `charmenable`, `charfinite`,
`BBHP`, `Laurent`, `normal subgroup theorem` over `research/`.  The graph had
character rigidity only for the Kac--Moody lattice
(`km-246-lattice-is-character-rigid`), subshift elementary groups
(`subshift-elementary-groups-are-character-rigid`, whose lattice remark on
`EL_3(F_2[u^{+-1}])` is exactly what the new claim supplies), and the real-Lie
Dogon--Vigdorovich equivalence.  All resolved in `distinct_from`.

**Hypothesis check for BBHP Theorem A** (Step 1 of the route).
1. `K = F_q(t)` is a global field; `SL_n` is connected, non-commutative,
   absolutely almost simple and simply connected.
2. BBHP's `def:arith` literally writes `O_S = {alpha : s(alpha) <= 1 for s in
   S}`, so `S` is the set where integrality is imposed.  With `S` = all places
   except `v_0, v_inf`, `O_S = F_q[t,1/t]`.  Under the usual convention
   (`S = {v_0, v_inf}` the places where poles are allowed) the ring is the
   same.  Both readings give `Lambda_S = SL_n(F_q[t,1/t])`.
3. Product type: bounded at every place except `v_0, v_inf` (`R ⊆ O_v`);
   unbounded at both, by `h = diag(t, 1/t, 1, ...)`.
4. (T) place: `EL_n(R)` has (T) and is dense in `SL_n(F_q((t)))`; a dense image
   of a Kazhdan group forces (T) on the locally compact group (short proof
   written out).  Every commensurable `Gamma` contains a power of `h`, so its
   image at `v_0` is unbounded.
5. Simply connected, so the charfinite clause applies whichever reading of `S`
   is used (one reading has `S` infinite, the other finite; the theorem's
   disjunction covers both).

**Derived consequences** (Steps 2--7).
- (CF1) `Rad(Gamma) = Gamma ∩ mu_n(F_q)·I`: a finite normal subgroup has a
  finite-index centralizer, which meets each root group `U_ij` in a nonzero
  element, and commuting with `I + x E_ij` for all `i != j` forces scalars.
- (CF2) Extremal characters are von Neumann amenable (hence amenable, hence
  finite by item 5) or supported on the radical.  Extremal plus finite GNS
  gives `tr_k∘pi` (the factor argument is written out).
- (CF3) `prop:NST` plus (CF1).
- (CF4) Proved without Margulis: a finite-index piece of `U_12` is an infinite
  elementary abelian `p`-group; its image in `U(d)` has at most `p^d`
  elements, so the kernel is infinite, hence of finite index by (CF3).
- (CF5) `A` is ICC (the FC-centre is amenable normal, so trivial); soft
  charm plus (A1) give `phi = s·delta_e + sum c_i tr∘pi_i`; the GNS algebra
  is `L(A) ⊕ ⊕ M_(k_i)` by disjointness (the regular representation of an
  infinite group has no finite-dimensional subrepresentation), and the
  decomposition is unique via the minimal central projections.
- (CF6) The limit trace of any model is a character, the limit algebra is its
  GNS algebra, `L(A)` is not injective (a hypertrace would give an invariant
  mean on `A`), so "properly non-amenable" = "limit trace `delta_e`", and then
  `N_omega ≅ L(A)`.

**Weakest steps a referee should attack.**
- Importing Theorem A for a function field.  BBHP state it for any global field
  and remark explicitly on positive characteristic (quoted in the route), but
  the proof of the function-field case was not re-verified line by line.  The
  DGGHL cross-check agrees.  The literal `O_S` convention is handled by
  checking both readings.
- The disjoint-sum/uniqueness argument in (CF5)(iv), which is standard but
  written out in full.

## 4. What this does and does not buy for the target

**Buys.**
- The target's Kazhdan-projection sketch no longer depends on an unverified
  character-rigidity hypothesis.  Every extreme character is `delta_e` or
  `tr∘pi` with `pi` factoring through a finite quotient.  This uses (CF4) only,
  not the congruence subgroup property: the kernel has finite index.
- There are no "twisted" non-amenable sectors: the only properly non-amenable
  limit algebra is `L(A)` with its canonical trace.  No limit algebra of the
  form `L(A/N)` for an infinite quotient, and no infinite-dimensional
  non-regular factor representation, can occur.
- Across the whole commensurability class, no witness can factor through an
  infinite proper quotient `Gamma/N`, and none can concentrate on characters
  induced from an infinite normal subgroup of infinite index.  (CF3) forbids
  such `N`.  Covers `Gamma~ -> Gamma`, which are not normal subgroups of
  `Gamma`, are untouched; see 5(a) and 5(e).

**Does not buy.**
- *Not a smaller reduction.*  For residually finite Kazhdan groups,
  `residual-finite-regularization-removes-the-weak-ucp-quantifier` together
  with `kazhdan-weak-ucp-stability-is-flexible-stability` already reduce
  flexible stability to correcting hyperlinear approximations, i.e. models with
  limit trace `delta_e`.  (CF6) re-derives that restriction by a different route
  and identifies the limit algebra, but the set of models to be corrected is the
  same.
- *Charfiniteness cannot decide the target by itself.*  The only known unstable
  residually finite Kazhdan group in the graph, `Gamma_g = Z^(2g) ⋊ Sp_(2g)(Z)`
  (`rf-kazhdan-group-not-flexibly-hs-stable`), has its witness at `delta_e`:
  projective regular representations of Heisenberg quotients.  `Gamma_g` is not
  charfinite, since `Z^(2g)` is an infinite normal subgroup of infinite index.
  Its instability mechanism uses a non-torsion class in `H^2(Gamma_g, R)`, which
  vanishes for `A`.  So both properties that separate `A` from `Gamma_g`
  (charfinite, `H^2 = 0`) are already known, and neither is a theorem that
  forces rounding in the regular regime.
- *No new route to the target.*  A route "charfinite + (T) + finitely presented
  + `H^2(., R) = 0` => flexibly HS-stable" would need a theorem not known for
  any infinite group; see the obstruction remark in 5(f).  No such route was
  written.

## 5. Approaches tried and where each dies

### (a) Non-central Kazhdan covers `EL_3(R~) -> A`

- *Idea.*  Choose a finitely generated ring `R~` with a surjection onto
  `R = F_2[t,1/t]` and kernel `I`.  For example `R~ = F_2[x_1, x_2]` with
  `x_1 -> t` and `x_2 -> 1/t`, so `I` is generated by `x_1 x_2 - 1`.  Then
  `EL_3(R~)` has (T), and it maps onto `EL_3(R) = A`.  The kernel contains the
  relative elementary group `E_3(R~, I)`.  Pull a model of `A` back to the
  cover and use `kazhdan-cover-models-round-iff-kernel-fixed-mass-one`: the
  model rounds iff the kernel's fixed subspace has asymptotically full
  dimension.
- *What works.*  Relative (T) of `(EL_3(R~), e_ij(R~))` gives fixed mass
  `-> 1` for each `e_ij(x)`, `x in I`, in any genuine representation close to
  the pulled-back model.  By a union bound the same holds for any fixed finite
  family of conjugates.
- *Where it dies.*
  - The kernel is the normal closure of finitely many elements, since `A` is
    finitely presented.  But the fixed subspace of the normal closure is the
    intersection of the fixed subspaces of **all** conjugates, and
    `rho(g) Fix(k) = Fix(g k g^(-1))`.
  - Near-full fixed mass for each conjugate individually gives no uniform lower
    bound on this infinite intersection.
  - This is exactly the gap the target's abelian-kernel bullet isolates.  The
    argument reproduces it and does not close it.

### (b) The adjoint module `sl_3(R) ⋊ A`

- *Idea.*  Test the target's remaining shape, abelian kernels without relative
  (T), on the most natural module.  The sketch: Burger's criterion on the dual
  of `sl_3(R)`; relative (T) of the column module `R^3 ⋊ SL_3(R)`; and a
  Weyl-element / `e_21(1)` Cartan argument moving an invariant mean on the dual
  away from non-trivial characters.
- *Status.*  This suggests `(sl_3(R) ⋊ A, sl_3(R))` has relative (T), which
  would place it in the case the target's bullet already excludes.  Not
  written as a node: it is a sub-case, and the sketch was not completed to
  proof standard.
- *Where it dies.*  It does not touch the case left open in the target,
  permutation modules on the vertex set `V = A/SL_3(F_2[t])`.  There relative
  (T) genuinely fails for `(⊕_V F_2) ⋊ A`: the dual is `{0,1}^V`, the
  Bernoulli(`p`) product measure is `A`-invariant with no atom at `0` for
  `p > 0` (`V` is infinite), and it converges weak-* to `delta_0` as `p -> 0`.
  So no relative-(T) argument can reach that case.

### (c) Gluing vertex roundings over the triangle of groups

- *Idea.*  `A` acts on the contractible `t`-adic building with a chamber as a
  strict fundamental domain, so `A` is the colimit of its triangle of groups.
  - The vertex groups are `SL_3(F_2[t])` and its conjugates by
    `diag(t,1,1)` and `diag(t,t,1)`.  These matrices lie in `GL_3(R)` and
    normalize `A`, so all three vertex groups are isomorphic to
    `SL_3(F_2[t])`.
  - Edge groups have index 7 in a vertex group, and the chamber group has
    index 21.
  - Round a model on each vertex group, then glue.
- *Where it dies.*
  - **Vertex rounding.**  The vertex groups are infinitely presented Kazhdan
    groups.  Their flexible stability is itself open; the graph calls it "the
    open crux" in `kazhdan-cover-models-round-iff-kernel-fixed-mass-one`, and
    the infinitely-presented corollary there makes instability the expected
    answer.  Restricting a model of `A` to a vertex gives an actor-extendable
    vertex model.  Rounding those is `hs-stable-vertex-rounding-for-every-model`
    territory, at least as hard as the target.
  - **Holonomy.**  Even with genuine vertex representations, gluing needs the
    three edge restrictions to agree exactly.  The approximate conjugacies
    between them compose around the chamber to a holonomy unitary.  It
    commutes approximately with the chamber group, but it need not be close to
    a unitary that can be absorbed, and nothing in the building structure
    forces it to be trivial.

### (d) Jung-type non-conjugate embeddings of `L(A)`

- *Idea.*  Since (CF6) pins the only relevant limit algebra to `L(A)`, try to
  show stability contradicts some rigidity of embeddings
  `L(A) -> ∏^omega M_(d_n)`.  For example, look for non-conjugate embeddings
  that could not both be roundable.
- *Where it dies.*  Roundable models already give non-conjugate embeddings with
  the same trace `delta_e`.
  - Take regular representations of congruence quotients `A/A(f_n)` and
    `A/A(g_n)` with coprime levels, e.g. `f_n = (t+1)^n` and
    `g_n = (t^2+t+1)^n`.  Both towers separate points, so both limit traces
    are `delta_e`.  Use multiples to equalize dimensions.
  - By (T), approximately conjugate genuine representations share most of
    their irreducible constituents: Kazhdan-average the intertwiner.
  - Here `A -> SL_3(R/f_n g_n R) = SL_3(R/f_n R) × SL_3(R/g_n R)` is
    surjective, since elementary matrices lift.  So `A(f_n)A(g_n) = A`, and a
    common constituent is trivial.  The trivial representation has
    multiplicity-fraction `1/|A/A(f_n)| -> 0`.
  - So non-conjugacy is compatible with stability, and gives no contradiction.

### (e) Central extensions

- ISW Theorem A and Dogon's Theorem 1.3 need real second cohomology, and
  `H^2(A, R) = 0` (Harder node; `A` is its own level-one congruence subgroup).
- Finite central extensions are handled by
  `laurent-sl3-central-covers-never-witness-instability`: central Kazhdan covers
  have finite kernel, and pulled-back models round strictly.
- Not settled: whether `A` has a non-residually-finite finite central
  extension.  That would need the metaplectic kernel of `SL_3` over `F_2(t)`
  with `S = {v_0, v_inf}`, which was not checked.  It is not needed for any
  claim written in this run.

### (f) Obstruction remark

In the graph and the sources checked, **no charfinite, finitely presented,
residually finite Kazhdan group is known to be not flexibly HS-stable**, and
none is known to be flexibly HS-stable.
- `Gamma_g` is not charfinite.
- `SL_3(Z)`, `Sp_(2g)(Z)`, `SL_3(Z[1/2])` and `A` are open in the graph.
- `SL_3(F_q[t])` is not finitely presented.

So any resolution of the target is a genuinely new kind of theorem: a stability
proof for an infinite charfinite group, or an instability witness in the
regular regime that uses neither `H^2`, nor normal subgroups, nor infinite
presentation.  The second must be a model with limit algebra `L(A)` whose
defect is not scalar.

A proof of stability cannot be dimension-blind either.
`sl3-projective-transfer-enemy-dichotomy` makes this firewall remark for the
number-field analogue, and the same reasoning applies here.
- Put `H = <A, s | [s, SL_3(F_2[t])] = 1>`.  Inside `L(H) ⊇ L(A)`, the unitary
  `s` commutes exactly with `SL_3(F_2[t])`.  The trace restricts to `delta_e`
  on `A`, and `[s, h]` is maximally far from 1.
- A roundable model forces almost `SL_3(F_2[t])`-central unitaries to almost
  commute with `h`, by item 3 of
  `function-field-hecke-pair-is-perfect-codense-kazhdan`.  So any argument
  valid in arbitrary tracial von Neumann algebras, such as positivity, root
  relations, (T) averaging or Hecke operators, cannot prove it.
- Any completion must use that the models are matrices.

## 6. Duplicates found (nothing written for these)

Each of these was considered as a node and rejected because the graph already
has it.
- **Upward transfer along finite index.**  "If a finite-index subgroup of `A`
  is flexibly stable then so is `A`" and the converse for Kazhdan groups.
  Already `finite-index-correction-is-equivalent-for-kazhdan-groups` (and
  `subgroup-exact-outliers-do-not-exist`).
- **Properly non-amenable reduction for `A`.**  Already (A3) of
  `kazhdan-hs-instability-lives-on-properly-nonamenable-limits`.  The new
  claim only identifies the limit algebra.
- **`delta_e` reduction.**  Already the combination of
  `residual-finite-regularization-removes-the-weak-ucp-quantifier` and
  `kazhdan-weak-ucp-stability-is-flexible-stability`.
- **Central covers / projective models.**  Already
  `laurent-sl3-central-covers-never-witness-instability`.

## 7. Suggested next moves

1. **Review the new claim.**  A referee should check the positive-characteristic
   case of BBHP Theorem A, in particular the finiteness-of-representations and
   amenable-character steps.  If the review passes, the target's
   Kazhdan-projection bullet can cite `laurent-sln-fq-lattices-are-charfinite`
   instead of "character rigidity; not verified".  That edit to the committed
   target file was **not** made here.
2. **Permutation-module shape.**  The concrete open shape is models of
   `(⊕_V F_2) ⋊ A` (or of a non-central cover with such a kernel) that
   concentrate at the trivial character without an atom; Bernoulli measures show
   they exist at the level of traces.  The question is whether matricial models
   of `A` can be twisted by such kernels without rounding.  This is the
   coset-wreath polarity of `function-field-hecke-pair-is-relatively-embeddable`.
3. **Metaplectic kernel.**  Determine the metaplectic kernel of `SL_3` over
   `F_2(t)` for `S = {v_0, v_inf}`, to know whether finite central extensions
   of `A` can be non-residually-finite.  This is cheap and would close 5(e)
   completely.
4. **Test case in the graph.**  A flexibly HS-stable or unstable charfinite
   finitely presented Kazhdan group would be a first data point for 5(f).  The
   graph currently has none.

## 8. Literature consulted

Read from primary sources in this run (dates are arXiv version dates; all
accessed 2026-09-16):
- U. Bader, R. Boutonnet, C. Houdayer, J. Peterson, *Charmenability of
  arithmetic groups of product type*, arXiv:2009.09952v3 (12 April 2022);
  Invent. Math. 229 (2022) 929--985.  TeX source `main.tex`.  Quoted verbatim
  in the route: the character-type definition, `def:charmenable`, `def:arith`,
  `thm:AG`, Lemma `soft charm`, Proposition `prop:NST`, and the
  positive-characteristic remark in section 7.1.
- A. Dogon, M. Glasner, Y. Gorfine, L. Hanany, A. Levit, *Non-uniform
  higher-rank lattices are character rigid*, arXiv:2507.21862v1 (29 July
  2025).  TeX source `arXiv_v1.tex`.  Quoted in the route: section 8 proof
  excerpt and `def:character rigidity`.  Cross-check only.
- O. Becker, A. Lubotzky, arXiv:1809.00632.  TeX source read (Definition 1.1,
  section 4.4 flexible variant).

Consulted through their graph nodes (statements already quoted there):
- A. Dogon, arXiv:2211.10492 (Definitions 1.2, 1.5; Theorems 1.3, 1.10).
- A. Dogon, I. Vigdorovich, arXiv:2506.20843v2.
- F. Fournier-Facio, arXiv:2512.09180v2, and Glebsky--Lubotzky--Monod--
  Rangarajan, arXiv:2301.00476, via `agent-bcl-two-kazhdan-literature-audit`.
  The second is uniform stability for lattices in semisimple groups with
  submultiplicative norms, not normalized-HS flexible stability.
- M. Ershov, A. Jaikin-Zapirain, arXiv:0809.4095v2, via
  `elementary-groups-over-fg-rings-have-property-t`.
- A. Ioana, P. Spaas, M. Wiersma, arXiv:2006.01874v2, via
  `rf-kazhdan-group-not-flexibly-hs-stable`.
- G. Harder's function-field vanishing theorem, via
  `harder-function-field-s-arithmetic-cohomology-vanishing`.

Attempted but not obtained:
- U. Bader, R. Boutonnet, C. Houdayer, arXiv:2112.01337.  Fetch failed
  (connection reset at the agent proxy).  **Unverified; nothing depends on
  it.**
