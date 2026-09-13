# Q3.4, affirmative side: the rounding routes under `hyperlinear-implies-sofic`

Lane `q34-rounding-routes`, 2026-09-12.  Graph read at main `72601a4ae`.
Target: `hyperlinear-implies-sofic` (every hyperlinear group is sofic), under
root `q3-4-resolved`.  The hyperlinear-nonsofic side belongs to lane
`q34-bc-witness-hyperlinear` and is not touched here.

Two ESTABLISHED claims of the graph carry everything below:

- `finitely-presented-nonsofic-group-exists`: some group `G_ns` is not sofic
  (kernel-checked, `Endpoint/MainResults.exists_finitelyPresented_nonsofic_group`);
- `markov-sofic-equals-sofic`: a group whose finite tables all have
  finite-state doubly stochastic models with vanishing multiplication, identity
  and trace defects is sofic.

No external separation theorem is imported.  §4 explains why none of the
standard ones transfers to the regular-character face.

## 1. Verdicts

| route | premises (besides established imports) | verdict |
|---|---|---|
| `markovization-via-branching-traffic` | `traffic-branching-rounding-hierarchy`, `branching-traffic-markov-reconstruction` | **(a)** second premise refuted, §2 |
| `hyperlinear-implies-sofic-via-traffic-lift` | `traffic-branching-rounding-hierarchy` + unstated realization step | **(a)** realization step false, §2 |
| `hyperlinear-implies-sofic-via-markovization` | `regular-character-markovization` | (c) premise windowwise equivalent to the target; LG test, §3 |
| `markovization-via-ternary-relative-distribution` | `permutation-valued-ternary-relative-distribution` | (c) LG test, §3 |
| `hyperlinear-implies-sofic-via-cpsd-face-collapse` | `group-table-cpsd-cp-face-collapse` | (c) tracial version false; no CP/CPSD separator lands on the face, §3–§4 |
| `hyperlinear-implies-sofic-via-bounded-width-compiler` | `bounded-width-regular-character-compiler` | (c) finite dimension must enter clause 1 or the import's scope, §3 |
| `hyperlinear-implies-sofic-via-definetti-rounding` | `definetti-group-table-rounding` | (c) DF1–DF4 cannot all hold tracially, §3 |
| `hyperlinear-implies-sofic-via-orbital-integerization` | `coherent-configuration-orbital-rounding` | (c) integrality is not the obstruction, finiteness is, §3 |
| `hyperlinear-implies-sofic-via-spherical-design` | `geometric-schreier-design` | (c) finite-dimensional from step one; crux unchanged |
| `hyperlinear-to-sofic-via-defect-congruence` | `spherical-defect-congruence-preserves-separation` (+5 cloud lemmas) | (c) crux unchanged: percolation of the congruence closure |
| `hyperlinear-to-sofic-via-local-holonomy-gauge` | `spherical-short-holonomies-admit-local-gauge` (+7) | (c) crux unchanged: nonempty private-label core |
| `markovization-via-random-intermediate-basis` | — | already invalidated (`haar-random-basis-depolarization`) |
| `sofic-model-via-quantum-birkhoff-channel-rounding` | — | already dead (`asymptotic-quantum-birkhoff-false`) |
| `sofic-model-via-unistochastic-dephasing` | — | already dead (`dephasing-destroys-multiplicativity`) |

The traffic pair comes first because it is the only case with a proof: one
established obstruction kills a live route into each of
`hyperlinear-implies-sofic` and `regular-character-markovization`, and leaves
`traffic-branching-rounding-hierarchy` without a consumer.  Nothing reached
verdict (b) beyond the trivial scoping in §2.4.

## 2. The rooted Cayley law and the traffic pair

Recorded as `cayley-traffic-law-refutes-markov-reconstruction` with proof
route `cayley-traffic-law-refutes-markov-reconstruction-proof`.

**2.1 The law.**  Fix a group `G` and a finite window `F` containing `e` and
closed under inverses.  A test graph is a finite connected directed graph `T`
with edges labelled by `F`.  A homomorphism of `T` into the left Cayley graph
is a map `phi: V(T) -> G` with `phi(w) = l(e) phi(v)` on every edge `e: v -> w`.

```text
lambda_G(T) = #{ phi : phi(v_0) = e }                              (CL1)
```

Right translation `phi -> phi . phi(v_1)^{-1}` shows (CL1) does not depend on
the root.  Along a spanning tree `phi` is determined by `phi(v_0)`, so
`lambda_G(T) = 1` when every cycle word of `T` is trivial in `G` and `0`
otherwise.  On a directed cycle this is the regular trace `1[w = e]`; on every
connected test graph it is the canonical value that
`permutation-traffic-is-simultaneous-fixed-points` identifies as the forced
limit at the regular character.  So `lambda_G` satisfies every permutation
traffic identity exactly, on every test graph, with regular cycle values.

**2.2 Positivity.**  The law has the properties of a finite-action law that
are proved one homomorphism at a time:

- (P1) values in `[0,1]`, value `1` on the one-vertex graph;
- (P2) reflection: reversing edges and relabelling `s -> s^{-1}` changes no
  homomorphism;
- (P3) Gram positivity: glue `k`-rooted connected test graphs `T_i`, `T_j`
  along their roots; homomorphisms of the glued graph are pairs agreeing on
  the roots, so with `f_i(x) = #{phi hom of T_i : phi(roots) = x}`,

  ```text
  lambda_G(T_i o T_j) = sum over x in G^k with x_1 = e of f_i(x) f_j(x),
  sum_{i,j} c_i conj(c_j) lambda_G(T_i o T_j) = sum_x |sum_i c_i f_i(x)|^2 >= 0.
  ```

  Each `f_i` is `0/1` with at most one nonzero point, so the sums are finite.
  A finite action on `X` gives the same identity over `X^k` with factor `1/|X|`.
- (P4) injective counts `tau^0` (homomorphisms injective on vertices) are
  nonnegative and `tau = sum over partitions pi of tau^0(T/pi)`.

It even satisfies exactly the identities finite actions satisfy only
approximately, such as subdividing a `k`-edge into `g, h` with `gh = k`.

**2.3 What finiteness adds.**  The closure `K` of finite-action laws is convex
(disjoint unions give rational mixtures).  When `lambda_G` lies outside `K`,
Hahn–Banach gives a finite linear inequality valid on `K` and violated by
`lambda_G`.  Such an inequality is finiteness-sensitive by construction.
P1–P4 are not of that kind.

**2.4 Theorem and scoping.**  Let `P` be any class of graph-indexed laws that
contains `lambda_H` for every group `H`, for example the laws satisfying
P1–P4.  Say RP_G(P) holds when for every window `F` of `G` and `eps > 0` there
are finitely many test graphs and `delta > 0` such that every law in `P`
within `delta` of the canonical values on them yields a finite state space and
doubly stochastic `P_g` (`g in F`) with multiplication, identity and trace
defects `< eps`.  Then **RP_G(P) holds if and only if `G` is sofic.**

- If `G` is sofic, a sofic approximation supplies the conclusion without using
  the law.
- If RP_G(P) holds, apply it to `lambda_G`, which has deviation `0` on every
  test graph.  Every window of `G` gets a finite Markov model of every
  accuracy, so `G` is sofic by `markov-sofic-equals-sofic`.

With `G = G_ns` the uniform principle is false.  Whatever positivity notion
the reconstruction uses, as long as Cayley laws satisfy it, the principle
carries no information beyond the soficity of the ambient group.  The same
argument refutes the realization step RL of the traffic-lift route: if every
law in `P` near the canonical values were near a finite-action law, the
permutations of that action would already be a sofic model.  RL fails even
without `markov-sofic-equals-sofic`.

The finite state space matters.  With measure spaces allowed, a Bernoulli shift
of `G` gives exact measure-preserving kernels with fixed-point measure `0`, for
every group.

**2.5 Graph consequences.**

- `branching-traffic-markov-reconstruction`: refuted.  Its own Attempts bullet
  asked for "a finite set/hierarchy of branching identities that forces a
  Markov realization".  No such set exists, because `lambda_{G_ns}` satisfies
  them all.
- `markovization-via-branching-traffic`: invalidated through that refutation.
- `hyperlinear-implies-sofic-via-traffic-lift`: invalidated.  Its realization
  step is RL.
- `traffic-branching-rounding-hierarchy`: stays open, with two readings.
  - Weak reading (P1–P4 and canonical values): witnessed by `lambda_G` for
    every group, with no microstate, so it says nothing.
  - Strong reading (the law is within `delta` of `K` on the tested graphs):
    near `lambda_G` this is per-window soficity, so the claim becomes the
    target.

## 3. The LG test for dimension-free premises

**Lemma.**  Let `C` be a class of tracial von Neumann algebras.  Let S(C) be
the statement: for every finite table `T` and `eps > 0` there is `delta > 0`
such that every unitary model of `T` in an algebra of `C` has the following
property.  If its multiplication, identity and regular-trace defects are
`< delta`, it yields a finite doubly stochastic model of `T` with defects
`< eps`.

1. If `C` contains `L(G_ns)`, then S(C) is false.
2. S(matrix algebras) is equivalent to S(R^omega-embeddable algebras).

*Proof.*  For part 1, `{lambda_g}` is an exact model of every window of `G_ns`
with zero defects.  S(C) would make `G_ns` Markov-sofic, hence sofic.  For
part 2, a model in an R^omega-embeddable algebra with defect `< delta/2` on
finitely many relations lifts to matrix unitaries with defect `< delta`.  ∎

So any proof of a premise whose conclusion is a finite Markov or permutation
model of the window must use finite dimension, equivalently
R^omega-embeddability, at a step that fails for `L(G_ns)`.  Arguments built
only from tools valid in every tracial algebra cannot be the whole proof:

- trace inequalities and positivity of `tau(x^* x)`;
- operator-norm bounds and functional calculus;
- tensor amplification `M (x) M^op` and conditional expectations.

This is silent on whether `G_ns` is hyperlinear.  If it is, every premise
below is false outright (the other lane's question).

- `regular-character-markovization`.  It is windowwise **equivalent** to the
  target.
  - Suppose the target holds but the claim fails at `(T, eps)`.  Take matrix
    models with `delta_n -> 0` and no Markov model.
  - Their classes in `prod_omega M_{d_n}` satisfy `T` exactly, with trace `0`
    on the tested `g != e`.  The group they generate is hyperlinear, hence
    sofic.
  - Its sofic approximation, restricted to `T`, is a permutation model with
    defect `< eps`.  Contradiction.
  - A proof must use finite dimension (lemma).
- `permutation-valued-ternary-relative-distribution`.  Any construction of
  the contextual triple object from traces alone would run on `L(G_ns)`,
  which has exact cubic traces.  Decoding it would make `G_ns` sofic.
- `group-table-cpsd-cp-face-collapse`.  Replace "finite-dimensional quantum"
  by tracial models and the collapse is false on the regular face.
  - `L(G_ns)` gives a feasible point there.
  - Points of `closure(C_class)` near the face are finite partial actions with
    small loss.
  - The closure of the finite-dimensional cone is the R^omega cone (part 2),
    so the collapse must separate R^omega-embeddable data from `L(G_ns)`.
- `bounded-width-regular-character-compiler`.  Clauses 1 and 3, together with
  `bounded-width-operator-csp-no-gap`, would make `G_ns` sofic if clause 1
  held for `L(G_ns)` and the no-gap theorem covered the assignments built
  from it.  So finite dimension enters one of two places:
  - clause 1 itself; or
  - the operator class of the imported no-gap theorem (Bulatov–Živný,
    arXiv:2404.11709; its class is not quoted in the node).
- `definetti-group-table-rounding`.  Balanced amplification, HS norms and
  symmetric extensions all exist over `L(G_ns) (x) L(G_ns)^op`, and DF4 is
  exactly the forbidden output.  So DF1–DF4 cannot all be tracial.
  - The dimension-freeness they ask for must mean constants uniform in `d`,
    not "never uses `d`".
  - The step using `d` is most plausibly DF3, where classicalization reads
    atoms, i.e. a basis.  `L(G_ns)` has none when `G_ns` is icc.
- `coherent-configuration-orbital-rounding`.  The tracial analogue is
  ill-posed rather than false.
  - The pair-space commutant of `lambda (x) conj(lambda)` contains the
    orbitals `A_c = rho_c`, `c in G`.
  - This thin scheme is exactly integral: `A_c A_{c'} = A_{cc'}`.
  - It is infinite, and nothing near it is finite.  Integrality is not where
    a nonsofic group escapes; the finite rank or multiplicity input is.
- Cloud claims (`geometric-schreier-design`,
  `spherical-defect-congruence-preserves-separation`,
  `spherical-short-holonomies-admit-local-gauge`).  The test does not bite.
  - These start from iid points on the sphere of `C^d` and tight matchings
    whose existence is concentration in dimension `d`.
  - Their recorded cruxes stand: percolation of the congruence closure and
    the nonempty private-label core.
  - The positive regions stand too: empty core, and exact-model-close
    finite-group tables.

## 4. Known separations: model tests of the transfer

None was imported.  Each was tested for whether its separating object can be
a regular-character table of a hyperlinear group without an approximate
permutation model.

1. **CP versus CPSD** (Laurent–Piovesan arXiv:1312.6643, Sikora–Varvitsiotis
   arXiv:1506.07297, as cited in `group-table-cpsd-cp-face-collapse`).
   Separating matrices are generic Gram data.  On the regular face the
   second-order data of a model is `tau(U_h^* U_g) ~ delta_{g,h}` whenever
   `h^{-1} g` is tested.  That is the identity matrix, which is CP.  A
   separator on the face has to use product (associativity) data, which is
   Q3.4 itself.  No transfer.
2. **Linear-system games with `J -> -1`** (solution groups; Slofstra's
   embedding theorem and non-closure).
   - Perfect and near-perfect strategies represent the solution group with
     the central sign `J` sent to `-1`.  That character is not the regular
     character: `tau(lambda_J) = 0`.
   - At the regular character `lambda(Gamma)` is always an exact tracial
     model.
   - These results separate operator classes at `J -> -1`.  None of them
     exhibits a hyperlinear nonsofic group.
3. **Magic square.**  The perfect strategy uses two-qubit Pauli observables,
   which generate a finite group.  Every finite group has an exact permutation
   model, the regular action.  The quantum advantage lives at `J -> -1`, not
   at the regular trace.
4. **MIP* = RE** (arXiv:2001.04383).  It separates commuting-operator from
   finite-dimensional correlations, so it produces non-R^omega-embeddable
   algebras.  Every premise here starts from matrix microstates, which is
   R^omega-embeddable data.  The only transfer is the LG test of §3, which
   uses a nonsofic group instead and needs no separation.
5. **Bounded width versus affine** (arXiv:2404.11709 as imported).  Bounded
   width has no gap.  The affine gaps sit on abelian equations with sign
   constraints, the `J -> -1` phenomenon again.  Nonabelian `xy = z` is not
   preserved by the coordinatewise Mal'tsev term (compiler node, first
   Attempt).  So neither half applies to group tables as they stand.

No external source was quoted verbatim here: the arXiv API answered "Rate
exceeded" from MSI and WebSearch was exhausted.  Nothing in §2–§3 depends on
an external source.

## 5. Sharpest remaining cruxes

- Every surviving premise is a statement about finite-dimensional unitary
  tables at the regular character.  It has to use dimension (§3), and it
  cannot be "positivity plus identities" on graph laws (§2).
- Cloud routes: produce joint rounding on every nonempty private-label core,
  or find a fixed core table with vanishing unitary defect and a positive
  coherent-shadow radius floor.
- The single fact that would move the most: whether `G_ns` is hyperlinear
  (lane `q34-bc-witness-hyperlinear`).  If it is, every premise in §3 is
  false.

## 6. Not done

- No numerical search.  For the reconstruction claim the deferred small-graph
  searches are superseded: `lambda_G` has zero deviation on every graph they
  could test.
- `hyperlinear-implies-sofic` and `q3-4-resolved` remain OPEN; see the
  lane's `cairn why` run.
