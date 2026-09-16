# Lane note: `fournier-facio-simple-factor-not-hyperlinear`

Agent `swarm-fournier-facio-simple-factor-n`, 2026-09-16. The hole was locked for this lane.
Nothing was committed. The long proofs are in
`research/artifacts/fournier-facio-simple-factor-corner-2026-09-16.md`. The exact-arithmetic
check is in `experiments/fournier-facio-simple-factor-corner-2026-09-16/`.

## 1. Setup

**Target.** "Let S be the finitely presented infinite simple torsion-free group chosen in
`fournier-facio-torsion-free-skeleton` (a Burger--Mozes or Hyde--Lodha group). Then S is not
hyperlinear." Its Attempts section said "Deferred". No route targeted it.

**Consumers.**

- `fournier-facio-nonhyperlinear-via-simple-factor`, towards
  `fournier-facio-has-no-purely-singular-free-near-representation`.
- `fournier-facio-gamma-not-hyperlinear-via-simple-factor`, towards
  `fournier-facio-compression-subgroup-not-hyperlinear`.
- Both use only `S ≤ G` (by W8 or injectivity of `π|_S`) and heredity of hyperlinearity.

**The ambiguity is real.** Fournier--Facio, arXiv:2608.02025v2, Section 2, read from the PDF:
"A finitely presented simple torsion-free group S, e.g. a Burger–Mozes [BM97] or Hyde–Lodha
group [HL25]". The construction accepts any such `S`. For the two named families the target
is a different problem:

- a Burger--Mozes lattice `S` in `Aut(T_a) × Aut(T_b)` is Haagerup and CAT(0), and does not
  contain `F`;
- a Hyde--Lodha group `Q_n` is left-orderable and contains `F` (result C below).

## 2. What was proved

All proofs are handwritten and not independently reviewed. Nodes created:

**A. `torsion-free-lattice-embeds-in-complement-crossed-product`.**

- **Route.** `torsion-free-lattice-complement-crossed-product-proof`, `requires: []`.
- **Setting.** `H` is lcsc, `K` is compact open, `Λ ≤ H` has `H = ΛK` and `Λ ∩ K = 1`, and `S` is
  a lattice with `S ∩ K = 1`.
- **Result.** `L(S)` embeds trace-preservingly into the corner `p(L^∞(H/S) ⋊ Λ)p`, with
  `p = 1_{KS/S}`.
- **The unitaries.** `u_s = Σ_λ v_{λ^{-1}} 1_{A_{s,λ}}` is a finite sum over the coupling
  cocycle `ks = λ(k,s)κ(k,s)`. It satisfies `u_s u_t = u_{ts}` and `τ(u_s) = δ_{s,1}τ(p)`.
- **No freeness needed.** It works with the crossed product, not the orbit relation.
- **Comparison.** This is the algebra the Hecke transfer lacked: by (HC5) of
  `hecke-corner-uniform-lattice-transfers-embeddability`, all Hecke algebras of a product of
  trees are CE, while `L^∞(H/S) ⋊ (W_a × W_b)` is non-CE whenever `S` is not hyperlinear.

**B. `tree-lattices-hyperlinear-if-f2xf2-crossed-products-ce`.**

- **Route.** `tree-lattices-hyperlinear-if-f2xf2-crossed-products-proof`, which requires A and
  the hyperlinearity dictionary.
- **Result.** If every p.m.p. crossed product of `F_2 × F_2` is CE, then every torsion-free
  lattice in `Aut(T_a) × Aut(T_b)` (`a, b ≥ 3`) is hyperlinear.
- **Proof outline.** Corner A with `Λ = W_a × W_b`; restriction to the free finite-index
  subgroup `K_a × K_b` (matrix embedding `π(x)_{ij} = E_0(v_{g_i} x v_{g_j}^*)`); induction to
  `F_2 × F_2` (a corner of the induced crossed product); Bernoulli upgrade for freeness.
- **Contrapositive.** A proof of the target for a Burger--Mozes `S` would produce an essentially
  free action of `F_2 × F_2` with a non-CE crossed product.

**C. `hyde-lodha-fp-simple-groups-contain-thompson-f`.**

- **Route.** `hyde-lodha-fp-simple-groups-contain-thompson-f-proof`, which requires
  `brin-plo-i-one-sided-approach-gives-a-copy-of-f`.
- **Result.** `F ≤ Q_n = [Γ_n, Γ_n]` for every `n ≥ 2`.
- **Proof.**
  - Take `η = n(n+1)` and the bump `f ∈ F_η` with nodes `(0,0)`, `(η^{-2}, η^{-1})`,
    `(1 − η^{-1}, 1 − η^{-2})`, `(1,1)`.
  - Put `u = f ∘ f`, `v_1 = f` rescaled to `[1/η, 2/η]`, `v_2 = f` rescaled to
    `[2/η − η^{-2}, 2/η]`, and `k_i = [u, v_i^{-1}]`.
  - `u^{-1}` pushes `supp v_i` below `2η^{-2} < 1/η`. So `⟨k_1, k_2⟩` has the orbital
    `(1/η, 2/η)`, and `k_2` approaches `2/η` in it but not `1/η`.
  - Brin's Theorem 1 gives `F`. It lands in `[F_η, F_η] ≅ [Stab_{Γ_n}(0), Stab_{Γ_n}(0)] ≤ Q_n`
    by HL Proposition 1.4(2).
- **Machine check.** The supports and orbitals are checked in exact arithmetic for
  `n = 2, ..., 6` (script and saved output in `experiments/`).

**D. Route `fournier-facio-simple-factor-via-thompson-f`.**

- **Target.** `fournier-facio-simple-factor-not-hyperlinear`.
- **Requires.** C and `thompson-f-is-not-hyperlinear`.
- **Instantiation.** It fixes `S = Q_n`, which the construction and the skeleton's wording both
  allow.
- **Effect.** Nonhyperlinearity of `F` gives the target. Conversely, for this `S`, refuting the
  target proves `thompson-f-is-hyperlinear`.

**Outcome class.** This is a reduction, plus the fence B for the other choice. The target stays
open.

- For `S = Q_n` there is one implication: nonhyperlinearity of `F` gives the target.
  Refuting the target would prove `F` hyperlinear, but that is the same implication read
  backwards.
- No reverse implication is known. A hyperlinear `F` would not make `Q_n` hyperlinear.

## 3. Approaches and where each dies

**Why the target cannot be proved outright now.** No finitely generated group is known to be
non-hyperlinear. A direct proof of the target, for either choice of `S`, would give the first
example. This lane therefore aimed for reductions and fences, not a proof.

1. **Rigidity or compression defect.**
   - A Burger--Mozes lattice is Haagerup: it acts properly on a product of two trees. So
     `a-t-menable-groups-have-no-rigid-compression-defect` rules out any defect built on
     relative property (T) inside `S`.
   - For `Q_n`, an infinite Kazhdan subgroup would answer Navas' question
     `infinite-left-orderable-kazhdan-group`, which is OPEN. Dies there.
2. **Residual finiteness, LEF, residual amenability.** `S` is infinite, simple, finitely
   presented and non-amenable, so none of these hold. That blocks the standard proofs of
   hyperlinearity, but not hyperlinearity itself, so it gives no lower bound. Dies as a method
   for proving non-hyperlinearity.
3. **Hecke corner transfer.** (HC5) of `hecke-corner-uniform-lattice-transfers-embeddability`
   makes every Hecke algebra of `Aut(T_a) × Aut(T_b)` CE. So the Hecke corner cannot carry a
   non-CE obstruction to `L(S)`. The corner lemma A replaces the Hecke algebra by the
   complement crossed product `L^∞(H/S) ⋊ Λ`, which is not automatically CE. This is what
   produced B.
4. **Crossed products of free groups.** Brown--Dykema--Jung (not re-read here) makes p.m.p.
   crossed products by `F_r` CE. This is why B lands on `F_2 × F_2` and not on one free group.
   The graph audit of Manzoor, arXiv:2502.06697v2, records a non-CE equivalence-relation
   algebra. It does not give a non-CE crossed product of an essentially free `F_2 × F_2`
   action, so B does not close.
5. **Whole-group or quotient attacks.** Attacking `S` through its quotients is impossible, since
   `S` is simple. Attacking it through its subgroups needs a subgroup already known to be
   non-hyperlinear. Result C shows `Q_n ⊇ F`, which shifts the problem to `F`. `F` does not
   embed in a Burger--Mozes lattice (solvable subgroup theorem for CAT(0) groups, not re-read),
   so this route serves the Hyde--Lodha choice only.
6. **A new hole C1 was considered and not created.** C1 is artifact §5.3: "every pmp action
   of `F_2 × F_2` has a CE crossed product". By B it would refute the target for every
   Burger--Mozes choice of `S`. It is the Connes-embedding sibling of
   `f2xf2-in-paunescu-class`, which implies it, since sofic essentially free actions have CE
   crossed products (after the Bernoulli upgrade FI4). No attack on C1 was made here, and a new
   hole needs a real Attempts section, so it is recorded only in this note and the artifact.

## 4. Literature

- Fournier--Facio, arXiv:2608.02025v2. Section 2 read from the PDF, including the wording of
  the simple input `S`.
- Hyde--Lodha, arXiv:2302.04805. Read from the PDF: Theorem 1.3 (finitely presented, `F_∞`,
  simple), Proposition 1.4(2) (`F_η ≅ Stab_{Γ_n}(0)`), §3.1 (1-periodic action) and the
  definition of `F_η`.
- Brin, arXiv:math/9705205, "The ubiquity of Thompson's group F in groups of piecewise linear
  homeomorphisms of the unit interval". Used through the committed node
  `brin-plo-i-one-sided-approach-gives-a-copy-of-f`, whose definitions of orbital and approach
  are quoted in route C. Brin's proof was not re-derived.
- Hyde--Lodha, arXiv:1807.06478. Seen only through the committed node
  `hyde-lodha-groups-contain-thompson-commutator-subgroup`, which is used for distinctness.
- Manzoor, arXiv:2502.06697v2. Seen only through the graph artifact that cites it; not
  re-read.
- Brown--Dykema--Jung (free entropy dimension and crossed products by free groups), and
  Bridson--Haefliger (solvable subgroup theorem). Standard; not re-read; no page references
  are claimed.
- The WebSearch budget ran out during this lane. Later lookups used the arXiv API through
  `curl`. No other sources were consulted, and no citation here was invented.
