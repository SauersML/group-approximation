# KL-violating equation over Thompson's V: swarm pass, 2026-09-16

Target: `kl-violating-equation-over-thompson-v`. The goal is a nonsingular
`w in V * <t>` whose coefficient map `V -> V_w = (V * <t>)/<<w>>` is not
injective.

**Outcome: partial progress, no violation found.**
- A general form of the relative weight test is landed as a lemma with a direct
  curvature proof.
- The census frontier of `kl-thompson-v-short-generator-words-certified-injective`
  was run through an exact weight-test certifier, with an independent verifier.
  This certifies more classes (numbers in section 3) and shrinks the frontier.
- Seven other lines of attack are recorded in section 4, with the exact point
  where each one dies.

## 1. Setup and what a violation must look like

`V` is Thompson's group with the Bleak--Quick generators `a = (00 01)`,
`b = (01 10 11)`, `c = (1 00)`, and `B = b^(-1)`. Properties used below:
- finitely presented, infinite, simple;
- integrally acyclic (Szymik--Wahl, as recorded in the graph);
- a-T-menable;
- no nontrivial finite-dimensional unitary representation, since it is simple
  and not residually finite;
- hyperlinearity of `V` is open.

Consequences for a violating `w` of degree `m = deg_t(w) != 0`:

1. **Everything dies.** The kernel of `V -> V_w` is normal and nontrivial, so it
   is all of `V`, because `V` is simple. Hence `V_w = <t | t^m> = C_m`
   (`kl-simple-failure-leaves-only-the-cyclic-quotient`). A violation is
   therefore the same thing as a word `w` whose normal closure in `V * <t>` is
   `N_m = ker(V * <t> -> C_m)`. The census collapse test already looked for
   this directly: Todd--Coxeter over `<t>` on all 113144 kept census words,
   with every enumeration overflowing at 200000 cosets. That run certifies
   nothing either way.
2. **Degree one would refute Kervaire.** For `|m| = 1`, `V_w` is trivial, so
   `V * Z` has weight one. That would be a counterexample to the Kervaire
   conjecture. Kawauchi, arXiv:2303.13728v4, claims a proof of that conjecture.
   The paper was not examined. Even if correct, it would only exclude
   `|m| = 1`, not injectivity for other degrees.
3. **The coefficient subgroup must be non-hyperlinear.** By
   `kl-failure-localizes-to-the-coefficient-subgroup`, a failure over `V` is
   already a failure over `A_w = <g_0, ..., g_(n-1)>`. By
   `kervaire-laudenbach-holds-for-hyperlinear`, `A_w` is not hyperlinear.
   - So `A_w` is not amenable, not residually finite, not linear and not LEF.
   - In the census, every class whose coefficients lie in `<a,b>` (order 24),
     `<a,c>` (order 6) or `<b,c>` (order 60) injects. The remaining frontier
     words all use `a`, `c` and one of `b`, `B`.
   - A violation over `V` would in particular exhibit a non-hyperlinear group.
     No non-hyperlinear group is known.
4. **A simplicity certificate.** Any nontrivial homomorphism `phi : V -> H`
   together with `t_0 in H` satisfying `w^phi(t_0) = 1` certifies injectivity.
   This is what the census RETRACT certificates use, with `H = V`.

## 2. Literature gate (arXiv, checked 2026-09-16)

These queries were run against the arXiv API on 2026-09-16:
- `all:Kervaire AND all:Laudenbach`
- `all:Kervaire AND all:conjecture`
- `abs:"equations over groups"`

The earlier gate in this session also covered Thompson-group equations. The
relevant hits:
- **L. Chen, arXiv:2302.09811v5**, *The Kervaire conjecture and the minimal
  complexity of surfaces*. Checked at abstract level. It gives a new proof of
  Klyachko's torsion-free theorem, and it generalizes the Klyachko--Lurye
  theorem to HNN extensions. That theorem says that `G -> (G * Z)/<<w^k>>` is
  injective for any group `G` and any proper power `w^k` with `w` of degree
  one.
  - It covers only proper powers of degree-one words.
  - The census frontier has no proper powers.
  - The Klyachko--Lurye paper itself was not fetched (unverified).
- **A. Kawauchi, arXiv:2303.13728v4**. Claims the Kervaire (weight) conjecture.
  Not examined, and its acceptance status is not known here. It is about weight
  only, so it does not decide KL-injectivity over `V`.
- **S. P. Fisher, Y. Lodha, arXiv:2608.25988v1** (2026-08-26). They disprove
  the Osin--Thom conjecture bounding `beta_1^(2)` by normal rank minus one. That
  conjecture would have implied the torsion-free Kervaire conjecture. The
  counterexamples are torsion-free, locally free and not finitely generated,
  so nothing follows for `V`, which has torsion.
- **V. Bagayoko, arXiv:2409.14854v2**, *Equations over valued groups*.
  Irrelevant here (valued groups).

Nothing found states KL, or its failure, over `V`, over any other finitely
presented simple group with torsion, or for any group not known to be
hyperlinear. The target remains open in the literature as far as this gate
reaches.

## 3. Main computation: exact weight-test certificates on the census frontier

SECTION-3-PLACEHOLDER

## 4. Approaches and exactly where each dies

### 4a. Solvability inside `V` is the wrong test: `t^2 = A` has no solution in `V`, yet injects

Let `A in F <= V` be `00x -> 0x`, `01x -> 10x`, `1x -> 11x` (domain cones
`00, 01, 1`, range cones `0, 10, 11`).

**Claim: `A` has no square root in `V`.**
- `Fix(A) = {0^inf, 1^inf}`:
  - on the cone `01`, `A` maps into `10`, so it has no fixed point there;
  - on `00`, `00x = 0x` forces `x = 0^inf`;
  - on `1`, `1x = 11x` forces `x = 1^inf`.
- The slopes (local dyadic derivatives) are `A'(0^inf) = 2` and
  `A'(1^inf) = 1/2`.
- If `B^2 = A` with `B in V`, then `B` commutes with `A`, so it permutes
  `Fix(A)`. Since `A = B A B^(-1)`, it preserves the slope of `A` at fixed
  points. The slopes differ, so `B` fixes `0^inf`, and `B'(0^inf)^2 = 2`.
- Every slope of an element of `V` is a power of `2`, and `2` is not the
  square of one. So `B` does not exist.

**Yet** `V -> (V * <t>)/<<t^2 A^(-1)>> = V *_(A = t^2) <t>` is injective, since
it is an amalgam over `<A> = Z`. And after the doubling
`delta_2(x) = x (+) x`, the element `A (+) A` has the square root
`0x -> 1 A(x)`, `1x -> 0x`.

**Where it dies.** Nonexistence of solutions in `V` (or in a ball of `V`) is
not evidence of a violation. The same example shows that RETRACT certificates,
which need `t_0 in V`, can never be complete: an injective word need not
retract to `V` itself. A natural extension, **not run**, is a retraction after an
injective endomorphism: `t_0 in V` with `w^(delta_2)(t_0) = 1`. Writing
`t_0 = sigma (u (+) v)` turns this into a 2x2 system over `V` (see 4c).

### 4b. The index-m core is a system, not one equation

With `N_m = ker(V * <t> -> C_m)` and transversal `1, t, ..., t^(m-1)`,
Reidemeister--Schreier gives

```text
N_m = V_0 * ... * V_(m-1) * <s>,    s = t^m,    V_i = t^i V t^(-i).
```

Here `<<w>>` is the normal closure in `N_m` of the `m` rewrites
`w_i = t^i w t^(-i)`, each of degree one in `s`.
- `V -> V_w` is injective iff `V_0 -> N_m/<<w_0, ..., w_(m-1)>>` is.
- That is `m` equations in the single unknown `s` over `V^(*m)`.

**Where it dies.** No KL-type theorem applies to more equations than unknowns,
and localization does not merge them. There is no reduction of the degree-`m`
problem to a degree-one problem over a bigger coefficient group along this
path.

### 4c. Wreath-product solutions reduce to systems over `V`

To solve `w` in an overgroup, the Gerstenhaber--Rothaus pattern uses
`H = V wr C_m = V^m ⋊ C_m`, with `V` embedded diagonally and
`t = (f_0, ..., f_(m-1)) sigma`.
- The `C_m` component of `w(t)` is `sigma^m = 1`.
- The `V^m` component unfolds into `m` equations in the `m` unknowns `f_j`
  over `V`.
- A solution certifies injectivity, because the diagonal map is injective.

**Where it dies.** It trades one equation for a square system over `V` itself.
- Gerstenhaber--Rothaus solve such systems in compact connected Lie groups by
  degree theory.
- `V` has no nontrivial map to any `U(n)`, and no topology or degree theory
  to replace it.
- The only available search is in balls of `V`. That is the RETRACT search
  with more unknowns, and it has no completeness guarantee.

### 4d. Normalized vertex group (0 finite out of 1801)

`vertexgroup.py` normalizes one same-sign corner label to `1` by `t -> s u`,
and closes the subgroup `L` generated by the rewritten labels, with a bound of
2000 elements. If `L` is finite, the word injects (localization plus
hyperlinear KL).

- **Run:** the first 1801 of the 6842 length-six census survivors.
- **Result:** `L` exceeded 2000 elements for every word (0 of 1801 finite).

**Where it dies.** The rewritten labels are products of `u^(+-1)` with
generators. Every frontier word involves `a`, `c` and `b` (section 1), and in
every tested case the labels generate more than 2000 elements. That is
consistent with `L` being infinite, but it is not a proof. Either way no
finiteness certificate appears, and the method has nothing to say when `L` is
infinite.

### 4e. Homology is blind

`V` is perfect and integrally acyclic. So `H_1(V_w) = Z/m` whether or not `V`
injects, and every Schur-multiplier or relative-homology obstruction in the
graph has nothing to detect. Examples are `aspherical-adjunction-has-zero-schur-kernel`
and the deficiency-zero Whitehead route.

**Where it dies.** At the first step: there is no homology class to track.

### 4f. Analytic and approximation approaches

KL is known over hyperlinear groups (Pestov; Nitsche--Thom) and over compact
Lie groups (Gerstenhaber--Rothaus). Both need maps from `V` to compact groups
with approximate multiplicativity.
- `V` has no nontrivial finite-dimensional unitary representation.
- Hyperlinear approximations of `V` are not known.

**Where it dies.** There is nothing to feed into the topological argument.
Conversely, a violation over `V` would prove `V` non-hyperlinear (section 1,
item 3).

### 4g. The weight test has a ceiling on the frontier

A floating-point LP profile gives the necessary condition that some
`theta >= 0` satisfies (WT1) and (WT2) restricted to admissible cycles of
length at most `L`:

| sample | `L` | possible | impossible |
|---|---|---|---|
| 1500 random frontier classes | 4 | 748 | 752 |
| first 300 of that sample | 4 | 146 | 154 |
| first 300 of that sample | 6 | 116 | 184 |

The exact yields on the same 1500 sample were:
- 215 classes certified with all weights at least `1/4`;
- 53 more with exactly one zero-weight non-loop edge.

On the first 2600 frontier lines, the full search (both modes) gave 168
positive certificates and no one-zero ones.

**Where it dies.**
- In the samples, about half of the frontier words (752 of 1500 at `L = 4`,
  184 of 300 at `L = 6`) fail the weight test for every `theta`, because a
  short admissible cycle system is already infeasible. This is floating-point
  LP evidence, not landed as a claim.
- Words that would need several zero-weight edges carry infinite families of
  cycles of bounded weight. The exact DFS certifier cannot enumerate them, so
  they need an argument about label families, which was not implemented.

## 5. What remains

The target is untouched in substance: no violation, and no argument that one
exists. Concrete next steps, in order of expected yield:

1. **Retraction after an injective endomorphism (not run).** Any nontrivial
   `phi : V -> V` is injective, because `V` is simple. A solution `t_0 in V` of
   `w^phi(t_0) = 1` gives a homomorphism `V_w -> V` extending `phi`, so it
   certifies injectivity (section 1, item 4).
   - Natural choices are `phi(x) = x (+) 1`, which acts on the cone `0` and
     fixes the cone `1`, and the doublings `phi = delta_k`.
   - The example of 4a is certified by `delta_2` but by no plain retraction.
   - This is the cheapest extension of the census RETRACT search.
2. **Zero-weight mode on the remaining frontier.** The one-zero mode of
   `weighttest.py` certified 53 extra classes out of 1500 in the sample, but it
   is about ten times slower. Run on the remaining frontier, it should certify
   a few percent more.
3. **Multi-zero weight families.** With two or more zero-weight edges, a
   zero-weight closed path has label `u`, and (WT2) needs every `u^k != 1`,
   together with families mixing `u^k` with short positive paths.
   - Infinite order in `V` can be decided from a revealing pair, which exhibits
     attractors and repellers. This is Brin's theory, not re-checked at source.
   - A certifier would need to cover whole families `u^k v`. It was not
     implemented.
4. **The infeasible half.** In the samples, about half of the frontier admits
   no weight at all (4g). If a violation over `V` exists among short words, it
   is there. Nothing computed here suggests that it does.
   - Any proof of a violation must exhibit a non-hyperlinear subgroup of `V`
     (section 1, item 3).
   - All homological and analytic tools are blind (4e, 4f).
   - So the only visible route to a violation is a combinatorial collapse proof
     that `<<w>> = N_m`, and Todd--Coxeter over `<t>` did not finish.

What would change the picture:
- a proof that `V` is hyperlinear, which would settle the target negatively
  through `kervaire-laudenbach-holds-for-hyperlinear`;
- or a structural theorem such as KL over groups acting on the Cantor set with
  dyadic germs. No such theorem was found in the literature gate.

## 6. Files

Research nodes (validated with the swarm `check.sh`):
- `research/kl-relative-weight-test-gives-injectivity.md` (claim)
- `research/kl-relative-weight-test-gives-injectivity-curvature-proof.md`
  (route, `requires: []`)
- `research/kl-thompson-v-frontier-weight-test-certificates.md` (claim)
- `research/kl-thompson-v-frontier-weight-test-certificates-proof.md` (route,
  requires the weight lemma)
- `research/artifacts/kl-thompson-v-census-weight-test-2026-09-16.md`

Experiments, in `experiments/kl-violating-equation-over-thompson-v-2026-09-16/`:
- `weighttest.py`: search and LP profile
- `verify_weight.py`: the independent verifier
- `summarize.py`: extraction and tables
- `vertexgroup.py`: 4d
- `weight_certificates.txt`: the certificates
- `run_log.txt`: chunk times, summary and verifier output

Not landed (scratch only): the rebuilt frontier list (reproducible, section 1
of the artifact), the per-chunk outputs, the 1500-word sample and its profile
outputs, and the arXiv query results.
