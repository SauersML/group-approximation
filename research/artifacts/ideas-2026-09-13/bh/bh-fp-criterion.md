# Idea lane bh-fp-criterion: finite-presentation criteria beyond finite-state full groups

Lane `bh-fp-criterion`, 2026-09-13. Target `boone-higman-conjecture`. These are **unreviewed ideas**:
nothing here is established, and no Cairn node was edited. The lens is finite-presentation criteria
for derived or alternating full groups of ample groupoids that are not finite-state.

## 0. What was read

**Sources.** Web tools were available. Anything marked "(abstract)" was read only at abstract level;
"(fetch summary)" means the fetch tool summarized the page and the statement was not read verbatim.
- **Matui, arXiv:1210.5800.** PDF text extracted locally.
  - §6.5: Theorem 6.12 (Brown [4, Corollary 3.3]); the poset `B`; Lemma 6.13 (directedness);
    Lemma 6.14 ((1) transitivity on equal rank, (2) vertex stabilizers `≅ ⊕_ξ Σ_rank(u)(ξ)`).
  - §6.2 Theorem 6.4 (for SFT groupoids: `[1_A] = [1_B]` in `H_0` iff a compact open G-set maps `A` onto `B`).
  - Lemma 5.3 (purely infinite `G`: every class in `H_0` is `[1_A]` for a nonempty clopen `A`).
- **Witzel–Zaremsky, "Thompson groups for systems of groups, and their finiteness properties".**
  PDF text extracted. Theorem 5.3 (Brown's criterion), Lemma 5.5 (cocompactness), Proposition 5.9
  (`G_k` eventually of type `F_n` and `L(G_k)` eventually `(n-1)`-connected ⇒ `T(G_*)` of type `F_n`).
- **Farley–Hughes, arXiv:1206.2692** (abstract): FSS groups acting on compact ultrametric spaces are `F_∞`.
- **Belk–Hyde–Matucci, "Finite Germ Extensions", arXiv:2407.03149**, Theorem 2.1 (fetch summary).
  If `G` is a finite germ extension of `B`, `B` has finitely many orbits on `sing(G)^n`, and the
  groups `SingFix_G(M, M′)` have type `F_n` for `M ⊆ M′ ⊆ sing(G)`, `|M′| <= n`, then `G` has type `F_n`.
- **de Cornulier, arXiv:math/0509090** (abstract): `W wr_X G` is finitely presented iff `W` and `G`
  are finitely presented, stabilizers are finitely generated, and `G` has finitely many orbits on `X^2`.
- **Grigorchuk–Medynets.**
  - arXiv:1105.0719 (abstract): an elementary proof that `[[T]]′` is infinitely presented, for minimal subshifts.
  - arXiv:1508.04454 (abstract): generators and relations for these commutator subgroups; the word problem
    in `[[T]]` is solvable iff the subshift's language is recursive.
- **Proietti–Yamashita, arXiv:2310.09928** (abstract): a Künneth formula for products of groupoids.

**Main.**
- `complexity-bounded-host-classes-are-not-universal`
- `kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`
- `arithmetic-near-shift-actions-have-mixed-relations`
- `shell-cantor-embeddings-are-finite-germ-extensions`
- `research/artifacts/full-group-homology-fp-obstruction-2026-09-13.md` (Li filtration, Corollary 2)
- `research/artifacts/boone-higman-free-shift-presentation-obstruction-2026-09-08.md` (mixed near relations)
- `research/artifacts/boone-higman-finite-state-and-shell-germ-limits-2026-09-08.md`
- The root's Attempts section.

## 1. The input that actually fails without finite-state structure

Matui's `F_∞` proof for SFT full groups has four inputs. The cloning-system and FSS proofs have the same shape.
- **(I1) Finitely many vertex types.** Families of compact open G-sets with sources among the finitely
  many `D_ξ`, `ξ ∈ V`. The rank vector counts them.
- **(I2) A finite, confluent expansion rule.** Simple expansions follow the finitely many edges out of
  `ξ`. Directedness (Lemma 6.13) comes from one claim: every compact open G-set becomes a union of
  canonical `U_{µ,ν}` after finitely many expansions.
- **(I3) Small cell stabilizers.** In Matui they are finite (Lemma 6.14(2)). In Witzel–Zaremsky they
  are the input groups `G_k`, which must already be of type `F_n` (Proposition 5.9).
- **(I4) Descending links** whose connectivity grows with height.

**What breaks.** For a groupoid that is not finite-state, (I2) is the first input to fail. A compact
open bisection whose germs carry unbounded information (a Λ-cocycle over a minimal subshift with a
complicated language, or a Turing-machine germ) never becomes a union of canonical rule pieces after
boundedly many expansions. With (I2) gone, (I1) goes too: the orbit of a vertex has to record
arbitrary clopen pieces. And (I3) is where any complexity must then live.

## 2. Approaches

### A1. Finite stabilizers plus finite rules give bounded complexity — survives as a constraint (sketch)

- **Idea.** Suppose Brown's criterion is run on a directed expansion poset with (I1), (I2), and
  finite cell stabilizers.
  - Every group element is a fraction of two rule forests of the same rank, modulo a finite stabilizer.
  - To compose two elements, expand to a common refinement. Directedness through a finite confluent
    rule set makes the refinement depth linear in the depth of the inputs.
  - Deciding identity is then a normal-form comparison of size exponential in word length.
  - So every group certified this way has a uniformly bounded word problem, and by
    `complexity-bounded-host-classes-are-not-universal` no such class is a universal host.
- **What it would prove.** One statement covering both recorded walls. A Brown-type finite-presentation
  route to a universal host must put the input's complexity into infinite cell stabilizers (I3), not
  into the vertex set or the rules.
- **Kill test.** Is there a known Thompson-like group of type `F_∞`, certified with finite
  stabilizers, whose word problem is not exponentially bounded? Result:
  - Higman–Thompson `V_{n,r}` and SFT full groups (Matui), FSS groups (Farley–Hughes abstract) and
    Brin–Thompson `nV` are all certified this way.
  - Every one of them has a word problem decidable by rule normal forms, and main records `nV`'s as
    coNP-complete.
  - No counterexample was found.
- **Verdict.** Survives as a constraint. It is a sketch: "linear refinement depth" needs a uniform
  bound on the rules per generator, which holds when each generator is a fraction of finite forests.

### A2. Complexity-carrying labels (cloning systems, wreath products over V-orbits) — killed as simple hosts

- **Idea.** Put the complexity into the stabilizers of (I3) directly: take a cloning system with
  `G_k = K^k ⋊ Σ_k` for a finitely presented `K` with hard word problem, or a permutational wreath
  product `K wr_Ω V` over a V-orbit `Ω`.
  - Witzel–Zaremsky Proposition 5.9 transfers finite presentation from the `G_k` once the descending
    links are connected.
  - de Cornulier's criterion transfers it from `K` when V's stabilizers on `Ω` are finitely generated
    and there are finitely many orbits on `Ω^2`. High transitivity of V on an orbit gives the orbit
    condition; finite generation of the stabilizer of a rational point was not checked.
  - Either way, the host's word problem is at least as hard as `K`'s, so the complexity wall does not apply.
- **Kill test (hand).** Forgetting the labels is a homomorphism onto the unlabelled Thompson group, and
  its kernel is normal. In a wreath product that kernel is the base `⊕_Ω K`. So such a group is simple
  only if the label part is trivial. Every simple quotient kills `K`.
  - Not verified in the Witzel–Zaremsky text: that their `T(G_*)` always maps onto the Thompson group of
    the permutation data. Their cloning systems come with morphisms `G_n -> Σ_n`, per the search summary.
- **Verdict.** Killed as a source of simple hosts. **Constraint:** complexity cannot sit in labels that
  the dynamics does not mix. It has to enter through germs of a minimal action, which leads to A3–A5.

### A3. Purely infinite product `G̃ = G_2 × (Λ ⋉ X)`, naive partition complex — killed (circular)

- **Idea.** Here `Λ` is a finitely presented overgroup of the input acting on a free minimal subshift `X`.
  - `H_*(G_2) = 0` (Li, as recorded in the homology artifact). Proietti–Yamashita's Künneth formula
    then gives `H_*(G̃) = 0`, so the Li-filtration obstruction (artifact, Corollary 2) is silent.
  - If clopen equivalence were classified by `H_0`, as Matui's Theorem 6.4 does for SFT groupoids, every
    nonempty clopen set would be equivalent. The poset of clopen partitions would then have one orbit
    per height, which is (I1) with no finite-state input.
- **Kill test.**
  1. **The equivalence step.** Theorem 6.4 is proved only for SFT groupoids. Lemma 5.3 realizes every
     `H_0` class by a clopen set but does not classify equivalence. So "one orbit per height" is
     unverified for `G̃`.
  2. **Stabilizers (hand computation).** The stabilizer of an unordered partition into clopen sets
     `P_1..P_n` contains `∏_i [[G̃|_{P_i}]]`. Whenever `P_i` is equivalent to the unit space, a bisection
     conjugates `[[G̃|_{P_i}]]` onto `[[G̃]]`. Brown's criterion would need `[[G̃]]` finitely presented in
     order to prove `[[G̃]]` finitely presented. This matches the circularity of the naive Brown complex.
- **Verdict.** Killed as a method. **Record:** products with `G_2` remove the homological obstruction,
  and conditionally the vertex-type count, but not the stabilizer requirement.

### A4. Mixed-coordinate complex (expansions only along the `G_2` coordinate) — killed as a method; one question left open

- **Idea.**
  - **Vertices.** Partitions of `C × X` into pieces `C_w × Y_w`, identified with `C × Y_w` only in the
    Cantor coordinate.
  - **Expansions.** Split `C_w` into `C_{w0}` and `C_{w1}`.
  - **Aim.** The `G_2` direction supplies (I2) and (I4); the `X` direction is carried as coefficients.
- **Kill test (hand, plus source).**
  - **Directedness.** A group element acts on `C_w × Y` through a Λ-cocycle that is constant only on
    small clopen `Y`. So vertices have to allow every clopen `Y_w`.
  - **Stabilizers.** They contain `∏_w [[(Λ ⋉ X)|_{Y_w}]]` up to a finite group.
  - **Where it lands.** Brown's criterion turns finite presentation of `[[G̃]]` into finite presentation
    of full groups of reductions of `Λ ⋉ X`, plus connectivity of descending links.
  - **Case `Λ = Z`.** These commutator subgroups are infinitely presented for every minimal subshift
    (Grigorchuk–Medynets 1105.0719, abstract), so the method certifies nothing.
  - **Non-amenable finitely presented `Λ`.** Finite presentation of `D([[Λ ⋉ X]])` is unknown.
- **Verdict.** Killed as a proof method: it reduces the product to the unproducted groupoid.
- **Not killed:** can `[[G_2 × H]]` or `D([[G_2 × H]])` be finitely presented while `D([[H]])` is
  infinitely presented? de Cornulier's wreath criterion, which requires the fibre `W` to be finitely
  presented, suggests not by analogy. But the full group of a product groupoid is not a wreath product,
  so the analogy proves nothing.

### A5. Finite germ extensions: residue-affine mixed relations don't scale — survives as a constraint (sketch)

- **The only non-finite-state criterion found.** Belk–Hyde–Matucci Theorem 2.1 (fetch summary). It
  moves finite presentation from `B` to a finite germ extension `G` through finitely many `B`-orbits
  on singular tuples and finite presentation of the `SingFix` groups.
  - It does not apply to `G̃` above, whose elements are singular on open sets.
  - It is exactly the regime of the shell route on main (`shell-cantor-embeddings-are-finite-germ-extensions`).
- **Idea.**
  - **The requirement.** The free-shift obstruction says a finitely presented shell envelope needs a
    mixed near relation.
  - **Where one comes from.** Residue-affine enumerations supply one
    (`arithmetic-near-shift-actions-have-mixed-relations`); the `A_5 * A_5` benchmark passes.
  - **Sketch.** A group generated by finitely many eventually residue-affine permutations of `N` has a
    uniformly bounded word problem modulo finitary permutations. Composing `n` generators gives modulus at
    most `M^n`, at most `M^n` residue pieces, and coefficients of size exponential in `n`. Checking
    eventual agreement is a finite residue comparison in time `2^{O(n)}`.
  - **Faithfulness.** The shell node makes every nonidentity input element a nonidentity germ, so an input
    whose regular action is residue-affine embeds in that bounded class.
  - **The wall.** By `complexity-bounded-host-classes-are-not-universal`, some decidable inputs have
    no residue-affine enumeration.
- **What it would prove.** Arithmetic benchmarks cannot scale to hard inputs. The mixed near relation for
  a universal shell envelope must come from a near action whose own germ complexity grows with the input.
- **Kill test.** Is anything already recorded on main? `arithmetic-near-shift-actions-have-mixed-relations`
  proves the relation and says nothing about scaling. The germ-limits artifact excludes rational hosts, not
  residue-affine near actions of the input. No duplicate found in the nodes read.
- **Verdict.** Survives as a constraint (sketch). Missing: a written bound for eventual equality of
  residue-affine words, and a check that "modulo finitary permutations" matches the germ group used by the
  shell stabilizers.

## 3. Summary for triage

| # | Approach | Verdict |
|---|---|---|
| A1 | finite stabilizers + finite rules ⇒ bounded word problem | constraint (sketch) |
| A2 | cloning systems / wreath products carrying complexity in labels | killed as simple hosts |
| A3 | purely infinite product, naive partition complex | killed (circular) |
| A4 | mixed-coordinate complex over `G_2 × (Λ ⋉ X)` | killed as a method; product question open |
| A5 | finite germ extensions with residue-affine mixed relations | constraint (sketch) |

**Surviving shape.** The only finite-presentation mechanism found that is not finite-state is the
finite-germ-extension theorem. So a universal host has to carry the input's complexity in the `SingFix`
groups at finitely many singular orbits. Those groups must satisfy a mixed near relation, and that relation
cannot come from residue-affine or other bounded-complexity near actions. For product groupoids no
criterion is known, and every complex tried either repeats finite-state structure (A1) or reduces to the
factor groupoid (A3, A4).

**Next tests.**
1. Write out A1's refinement-depth bound for Matui's poset. Check whether finiteness of stabilizers is
   really needed, or whether bounded stabilizer complexity already suffices.
2. Settle A4's open question on a model case, for instance whether
   `D([[G_2 × (Z ⋉ X)]])` is finitely generated but infinitely presented for a Sturmian `X`, through a
   relator-shift / LEF argument.
3. Write the residue-affine word-problem bound for A5.
