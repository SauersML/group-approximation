# Completing the independent-set injection to a quantum bijection

Lane `ex-kac-quantum-bijection`, 2026-09-13.  The mathematics lands as Cairn
nodes.  This note records source verification, the calculations behind the
Attempts, and the map of where the route stands.

## 0. Outcome in one paragraph

The route "complete the quantum injection of the constant-question
independent-set games to a quantum bijection" reduces, exactly, to a square
presentation of the source synchronous game itself.  The question half of the
injection is already a quantum bijection
(`independent-set-injection-splits-as-question-bijection`).  The canonical
square syntax is torsor/coset syntax:

- `torsor-cfi-isomorphism-algebra-is-coset-constraint-algebra` (lane
  ex-kac-quantum-compiler, first);
- `coset-systems-are-torsor-isomorphism-games`, the pair-subgroup version
  with the union symmetry of the rung.

Three firewalls now bound the torsor route:

- `coset-refinement-forces-rectangular-central-splitting`: pair algebras must
  split centrally into accepted rectangles;
- `exact-label-coset-refinements-are-affine`: exact labels on single-variable
  edges give only affine allowed sets, hence the group endpoint;
- `port-generated-square-completions-force-coset-support` and
  `torsor-cfi-port-profiles-are-cosets` (peer): completions inside the port
  algebra, and gadgets, land in cosets.

A fourth theorem covers hidden shared labels:
`hidden-labels-import-cross-context-commutation`.  Any refinement makes each
non-rectangular context split into pieces on which its variables commute with
the far neighbours, so factor models with nonzero commutators admit none.  On
perfect traces this split is equivalent to (RCS), and every perfect trace of a
constraint-variable presentation passes it
(`forbidden-pair-splits-are-central-rectangle-splittings`, lane
ex2-kac-forbidden-pair).  So it is not a further firewall for Boolean gap
sources.

What survives:

- lifting a perfect trace of a constraint-variable presentation to a coset
  refinement, with hidden labels on its variable questions;
- multi-variable edges with nonabelian exact label groups;
- square completions whose fibres are not torsors;
- in every case, a system with no affine relabeling
  (`relabelable-coset-systems-are-solution-group-corners`).

The open targets are `tracial-non-ru-coset-system-with-nonabelian-fibre-exists`
and `non-group-dual-colored-qc-qa-pair-exists`.

## 1. Sources verified at source (arXiv text, extracted with ghostscript on MSI)

- **Lin, *MIPco = coRE*, arXiv:2510.07162v1, §6.3.3.**
  - Definition 6.14 defines the `δ`-Bell test separation problem with
    yes-set `ω*(G) = ω^co(G)` and no-set `|ω*(G) − ω^co(G)| >= δ`.
  - Theorem 6.15: "The 1/2-Bell test separation problem is RE-complete".
  - The paragraph after it says the reduction has "the “no” case consisting
    of games G such that ω^co(G) = 1 and ω*(G) <= 1/2 (where the G in both
    cases are synchronous 12-th level CL sample games)".
  - The repository's `perfect-qc-separation-yields-finite-bcs-with-no-matrix-model`
    and `lin-explicit-synchronous-bell-gap-game` quote this correctly.
- **Mančinska--Spaas--Spirig--Vernooij, arXiv:2505.05253, §1, §3, §5.**
  - **Theorem A.**  For a synchronous game `G` with uniform question
    distribution there is a `t`-independent-set game `Ĝ` on `X(G)`, with
    `t = |Q|` and diagonally weighted questions, such that
    `ω*(G) = 1 ⟹ ω*(Ĝ) = 1` and `ω*(G) < 1 − ε ⟹ ω*(Ĝ) < 1 − O(ε^8/t^4)`.
  - **Corollary B.**  There is a constant-`t` RE-complete `(1,s)`-gap family.
  - **Theorem 3.1 ([MRV15]).**  `G` has a perfect quantum strategy iff
    `(X(G), t)` does.  Its proof is written for PVMs in a tracial von
    Neumann algebra `(M, τ)`.  Footnote 8 records that for positive `A, B`,
    `τ(AB) = 0` iff `AB = 0`.
  - **Remark 3.2** covers attainment.  The introduction states that the
    proofs apply to the commuting-operator value.
- **Consequence used here.**  For the perfect `qc`/`qa` separation of the
  independent-set source, only the algebraic Theorem 3.1 is needed:
  - it gives a tracial state and no `R^U` model;
  - an `R^U` model would be a perfect `qa` strategy, forcing `ω* = 1`;
  - the quantitative gap of Theorem A is not needed.

## 2. The injection splits

For a perfect tracial model `(P_i^(q,a))` of `(X(G), |Q|)`:

- `W_(iq) = sum_a P_i^(q,a)` is a magic unitary;
- `P_q^a = sum_i P_i^(q,a)` is a perfect model of `G`;
- `P_i^(q,a) = W_(iq) P_q^a = P_q^a W_(iq)`.

Conversely, any perfect model of `G` together with a magic unitary `W` that
commutes with the answers of its own question gives a perfect model of the
independent-set game.  So the squareness defect sits in the answers of `G`,
not in the question labels.

## 3. Uncoloured completions and why they are never colour-uniform

**The quantum swap.**  Let `E = (e_(av))` be any `t x n` quantum injection:
rows are PVMs, columns are orthogonal, and `q_v = sum_a e_(av)`.  Then

```text
U = [[0, E], [E^T, 1 − diag(q)]]        on [t] ⊔ [n]
```

is a magic unitary, a quantum involution.

- Rows `v`: `q_v + (1 − q_v) = 1`.
- Columns `a`: `sum_v e_(av) = 1`.
- `e_(av)(1 − q_v) = 0`.

So every quantum injection completes to a quantum bijection of `t + n` points.

**The swap never respects the independent-set colours.**

- The products `u_(av) u_(v'v') = e_(av)(1 − q_(v'))` are nonzero for
  `v != v'` in general, whether `v, v'` are adjacent or not.
- A colouring respecting `U` would need `col(a, v') = col(v, v')` for both
  kinds of pairs.  That merges the adjacent and non-adjacent classes, which
  are exactly what the rule must separate.
- Linking closure merges the question pair `(a,a')` with the answer pair
  `(v,w)` for `v ~ w`, so the induced trace is not closure-safe.
- Classically this is the statement that the swap `a ↦ f(a), f(a) ↦ a` must
  see the adjacency between `f(a)` and the fixed points.

**Squareness is forced along fibres.**

- **Fibres.**  By the argument of Lupini--Mančinska--Roberson,
  arXiv:1712.01820v2, Theorem 4.6 and Corollary 4.7 (read at source), a
  quantum isomorphism sends quantum orbitals to quantum orbitals and diagonal
  classes to diagonal classes.  So its magic unitary is block diagonal along
  orbits, with square blocks.  "Choosing a subset" is therefore not
  expressible in isomorphism syntax; only fibrewise permutations are.
- **Central cross mass.**  In a Kac host, a central cross-mass projection `P`
  with `h(P) > 0` counts rows and columns equally, so the two parts have the
  same size.  This is the Haar counting in the rung theorem.
- **Complexity.**  A uniform classical-solution-preserving gadget would
  reduce NP-complete independent set to graph isomorphism.  Babai's argument
  on `qc-isomorphic-not-qa-isomorphic-graph-pair-exists` blocks this.  So any
  completion must destroy classical solutions.

## 4. Torsor syntax and the three firewalls

**Implications.**

```text
tracial non-R^U coset system with nonabelian fibre image
  => (coset dictionary, T1–T4) colored qc-but-not-qa pair, union symmetry not a group dual
  => (closure-safe rung) non-Connes-embeddable Kac quantum group, not a group dual.
```

**Sources enter through coset refinements**: groups `K_q`, padding maps
`beta_q`, and cosets inside the accepting sets.

- **(RCS).**  The refined trace splits every pair algebra centrally into
  accepted rectangles.
  - Three-colouring presentations force commuting adjacent PVMs.
  - Context presentations pass.
  - Without padding the condition is coset-hull safety, which contains the
    Mal'tsev closure.
- **(EL).**  On context games with single-variable edges, label-exact
  refinements only reach affine allowed sets, which is the linear-system
  endpoint.
- **Peer theorems.**  Latin completions from the port projections force
  regular groups and coset-hull safety.  Torsor gadget port profiles are
  cosets.

## 5. Hidden shared labels: the one mechanism left in torsor syntax

**Example.**  NAND on `(x_u, x_w)` is the image of a subgroup.

- Take `T = {(ℓ, 2ℓ)} <= Z_3 x Z_3` and `ψ = [0,0,1]` on both coordinates.
- Then `(ψ(ℓ), ψ(2ℓ))` runs over `00, 01, 10`.
- The label `ℓ_u` is not a function of `x_u`: `ℓ_u = 0` iff `(x_u,x_w) = 00`,
  and `ℓ_u = 1` iff `(x_u,x_w) = 01`.
- If `ℓ_u` is the shared label on the edge to a context `c'` containing `u`,
  then `[x_u = 0][x_w = 1]` must commute with `P_(c')`.
- So hidden labels import commutation of `x_w` with a context that does not
  contain `w`, on the sector `x_u = 0`.

**General shape (now a theorem).**

- The label pair of two edges of a context lies in a coset of a subgroup of
  `L_(e') x L_(e'')`.
- Goursat splits that coset into class rectangles, and the class projections
  lie in `W*(p_c) ∩ W*(p_(c')) ∩ W*(p_(c''))`.
- If the allowed restriction to `(u,w)` misses a pattern, each class has
  constant `u` or constant `w`.
- This is `hidden-labels-import-cross-context-commutation`.  There is a
  projection `m` with `[X_u, P_(c'')] m = 0` and `[X_w, P_(c')] (1-m) = 0`.
  - Factor models with both commutators nonzero admit no coset refinement.
    An `M_3` example is recorded on the node.
  - For synchronous sources with NAND pair contexts, every forbidden pair
    `(q,a; q',a')` splits into local commutation of `P_q^a` with `P_(q')` and
    of `P_(q')^(a')` with `P_q`.
- On perfect traces this split is equivalent to (RCS), and constraint-variable
  presentations pass it automatically
  (`forbidden-pair-splits-are-central-rectangle-splittings`).
- What survives in torsor syntax:
  - lifting a perfect trace of a constraint-variable presentation to a
    non-relabelable coset refinement;
  - multi-variable edges with nonabelian exact label groups.

## 6. Plain graphs

Roberson--Schmidt, arXiv:2111.12362v1, pp. 12--17:

- Theorem 4.7 removes vertex colours when all degrees are at least 3.
- Edge decoloring by subdivision (Definition 4.9, Lemma 4.10) sends a
  subdivision vertex to `u_(vx)u_(wy) + u_(vy)u_(wx)`.  That is a projection
  only if the products commute (Lemma 4.8).
- So it does not transfer coset systems whose adjacent fibre PVMs fail to
  commute.
- No colored-to-plain reduction preserving both `qc` and `qa` for such systems
  is known here.

## 7. Literature bound

- **Web search.**  Unavailable in this session: the budget was exhausted.
- **Read at source.**
  - Lin §6.3.3;
  - MSSV §§1, 3, 5;
  - Roberson--Schmidt pp. 5--17;
  - Lupini--Mančinska--Roberson §4.1--4.2 (Theorems 4.2, 4.4, 4.6,
    Corollaries 4.3, 4.7).
- **Grep-level reads.**  BCEHPSW, AMRSSV and Paddock--Slofstra, through the
  local extractions of lane ex-nh-mipstar.
- **Novelty statements.**  They are bounded to these files and the repository.

## 8. Sharpest next targets

1. **Lifting constraint-variable traces.**
   - The earlier target, whether Lin/MSSV traces have the forbidden-pair
     splits, is answered.  The splits are equivalent to (RCS), and every
     perfect trace of `G_cv(B_I)` passes them
     (`forbidden-pair-splits-are-central-rectangle-splittings`).
   - Next: lift a perfect trace of `G_cv(B_I)` to a coset refinement with no
     affine relabeling, or prove that hidden labels on its variable questions
     collapse to an affine relabeling.
2. **Multi-variable edges.**  Is there an `MIP*=RE`-type source with an exact
   nonabelian label group, for example `Q_8` or `D_4` on three-variable
   edges?
3. **Non-torsor square completions.**  The peer's `S_3` orbital example shows
   closure-safe traces outside coset syntax.  Classify closure-safe square
   presentations whose fibres carry non-regular quantum actions.
4. **Decoloring.**  Find a colored-to-plain reduction preserving both `qc`
   and `qa` for noncommuting adjacent fibres.  Without one, the plain-graph
   claims receive no route.
