# Idea lane: non-hyperlinear group, Kervaire--Laudenbach, hyperlinear versus sofic (2026-09-13)

Lane `ideas-nonhyperlinear`. The directive was ideation first: at least twelve
genuinely new approaches, a quick-kill pass on each, then deep execution of
the best one that survives.

**Novelty check.** Before scoring, each idea was grepped on `origin/main`,
tip 123b99e6e and then 58467f62d. Hit counts, as file counts under `research/`:

| Key | Files |
| --- | --- |
| linear sofic / rank metric | 545 |
| Gordeev--Kunyavskii--Plotkin / word maps with constants | 0 |
| Kervaire near linear sofic or rank metric | 0 |
| characteristic-p Gerstenhaber--Rothaus | 0 |
| signed permutation / monomial models | 398 |
| strong convergence | 106 |
| Aldous--Lyons / permutation strategies | 32 |
| hypertrace / amenable trace | 112 |
| Lang--Steinberg | 0 |
| determinant conjecture | 102 |
| de la Harpe--Skandalis | 1 |
| weight test | 28 |
| Aut(X, mu) | 51 |

**Labels:** *dead* means an immediate obstruction or already covered on main;
*alive* means no obstruction found in the quick pass; *promising* means alive
with a concrete decisive test available.

## The ideas

1. **Rank-metric Gerstenhaber--Rothaus.** *Promising, executed below.*
   - *Idea.* Pestov's argument solves an equation coordinatewise in `U(n)`
     and passes to the unitary ultraproduct. Do the same in the rank-metric
     ultraproduct of `GL_n` over an algebraically closed field.
   - *What it needs.* Topology is replaced by algebra: every nonsingular
     equation with matrix constants should have an approximate root after
     amplification. That would give Kervaire--Laudenbach for every linear
     sofic group, a class between sofic and weakly sofic that is not known to
     sit inside the hyperlinear class.
   - *Novelty.* Main has linear sofic machinery (545 files) and radical
     statements for KL (`nonsingular-adjunction-preserves-approximation-radicals`,
     `schur-kernel-lies-in-char-p-linear-sofic-radical`), but no KL transfer
     through rank ultraproducts and no algebraic root premise.
   - *Test.* Exact Groebner-basis tests on small constants.
   - *Kill criterion.* A constant tuple with no approximate root at any
     amplification.
2. **Signed-permutation corners.** *Dead, covered.*
   - *Idea.* For `Gamma` with a central involution `J`, a permutation model
     restricted to the `J = -1` eigenspace is a signed monomial model of the
     corner. So a separation needs a Connes-embeddable corner with no signed
     monomial microstates.
   - *Already on main:* `monomially-hyperlinear-groups-are-sofic` and the
     hyperoctahedral signed-type nodes. The corner refinement is incremental.
3. **Trace-weighted curvature tests for KL.** *Dead, covered.* Weight tests
   with angles read off coefficient spectra are in
   `research/artifacts/kl-curvature-redistribution-2026-09-12.md`.
4. **Strong-convergence rigidity.** *Dead, covered.* The idea was that
   operator-norm strong convergence of random models forces near-exact
   representations for Kazhdan groups. It appears in 106 files on main,
   including the affine `SL_2(Z)` matricial-field nodes.
5. **Permutation MIP* versus unitary MIP* (Bowen--Chapman--Lubotzky--Vidick-type compilers).** *Dead, covered.* `sofic-recognition-under-hyperlinear-promise-dichotomy`
   already reduces the separation to a promise-hardness statement.
6. **Tracial Positivstellensatz certificates.** *Dead.* SDP and moment
   hierarchies certify bounds valid for every tracial state, including the
   non-Connes-embeddable ones. They cannot separate Connes-embeddable traces
   from the rest, and by MIP* = RE no finite hierarchy level decides the
   question.
7. **Kazhdan projection versus hypertraces.** *Dead.*
   - *Idea.* Non-hyperlinearity is failure of amenability of `tau_reg` on
     `C*(G)`, so look for an obstruction there.
   - *Why it dies.* A Kazhdan projection has `tau(p) = 0`, which is compatible
     with every central extension state, so no contradiction mechanism. On
     main: 112 hypertrace files.
8. **Lang--Steinberg twisted roots.** *Dead as a KL route, merged into 1.*
   - *Idea.* In `G(F_p-bar)` every element is `t^{-1} F(t)` for the Frobenius
     `F`.
   - *Why it dies.* Frobenius is not a group word with constants, so this only
     supplies tooling for idea 1.
9. **Fixed-point monotonicity as a sofic axiom.** *Dead, covered.*
   - *Idea.* Permutation characters satisfy `chi(g^k) >= chi(g)`; unitary
     characters need not.
   - *Why it dies.* Near `tau_reg` all almost-characters of nontrivial elements
     are close to 0, so the violations vanish in the limit. A separation needs
     correlations, which is the conic face route
     `hyperlinear-implies-sofic-via-cpsd-face-collapse`.
10. **`Aut(X, mu)` internal closure for KL.** *Dead, restatement.* A root for
    a given measure-preserving action exists iff that action extends to
    `G_w`. The freedom to re-embed through co-induction makes this exactly KL,
    which is the principle of c2b5fa2b0.
11. **Cost / L2 of the adjunction relation.** *Dead.* The Osin--Thom torsion
    groups already break L2 normal-rank bounds, per Attempt 8 of
    `kervaire-laudenbach-nonsingular-conjecture`.
12. **Determinant degree in II_1 factors.** *Dead.*
    - *Idea.* The de la Harpe--Skandalis determinant multiplies by `m` under
      `t |-> w(t)`.
    - *Why it dies.* `U(M)` is contractible, and the constraint
      `Delta(t)^m Delta(consts) = 1` is always satisfiable. It is a necessary
      condition, not an existence theorem.
13. **Small cancellation over hyperbolic coefficient groups.** *Alive, as a filter only.* If `w` is `C'(1/6)`
    over hyperbolic `G`, then `G` embeds in `G_w`. So counterexample searches
    must use short special words; generic words are excluded.
14. **Determinant conjecture separation.** *Dead, covered.* Sofic groups
    satisfy Lueck's determinant conjecture (Elek--Szabo), so a hyperlinear
    violator would be nonsofic. On main: 102 determinant files, including the
    algebraic Atiyah tester nodes.
15. **Quantum automorphism groups of graphs as hosts.** *Dead for groups.*
    Non-Connes-embeddable quantum isomorphism traces live on compact quantum
    groups. The group-level shadow is the solution-group compiler already on
    main.
16. **J-killing equations over solution groups.** *Dead, circular.*
    - *Idea.* A KL counterexample kills an element of
      `Rad_MF intersect Rad_hyp`, and central `J` in the solution group of a
      tracially satisfiable non-R^U linear system is the canonical such
      element.
    - *Why it dies.* Producing that system is the Paddock--Slofstra form of
      the root itself.

**Survivors:** 1 (promising), 13 (filter only).

## Deep execution: idea 1

### Sources pinned at source (TeX fetched on MSI)

- **Arzhantseva--Paunescu, arXiv:1212.6780.**
  - Definition `universallinearsofic`, l.282--287: "We denote by
    $\Pi_{k\to\omega} GL_{n_k}(F)/d_\omega$ the metric ultraproduct obtained
    by taking the quotient of the Cartesian product $\Pi GL_{n_k}(F)$ by
    $\nr_\omega=\{(a_k)_k\in\Pi GL_{n_k}(F):\lim_{k\to\omega}d_{rk}(a_k,Id)=0\}$."
  - Definition `def:lsofic`, l.402--405: "A countable group $G$ is
    \emph{linear sofic} if there exist an injective morphism
    $\Theta:G\to\Pi_{k\to\omega} GL_{n_k}(\cz)/d_\omega$."
  - l.178--181: "Sofic groups are linear sofic, while linear sofic groups are
    weakly sofic."
- **Gordeev--Kunyavskii--Plotkin, arXiv:1801.00379.**
  - l.189--190: "We present results on the images of such maps, in
    particular, we prove a theorem on the dominance of “general” word maps with
    constants".
  - l.476--478: "there are words with constants $w_\Sigma$ such that
    $\Imm \w_\Sigma = 1$ (so-called identities with constants".

### Landed nodes

- **`linear-sofic-kl-from-amplified-algebraic-roots`**, with route
  `linear-sofic-kl-from-amplified-roots-ultraproduct-proof`. The theorem: if
  `ARR(L)` holds over an extension field `L` of `F`, then every countable
  `F`-linear sofic group satisfies Kervaire--Laudenbach.
  - *Proof in brief.* Push the representation to `L`, which preserves rank.
    Amplify coordinatewise, which preserves normalized rank. The approximate
    roots become an exact root in the ultraproduct.
  - *Why no window condition.* The root is exact in the ultraproduct group
    itself, so the Attempt 5 window issue of the KL root does not arise.
- **`amplified-algebraic-roots-for-nonsingular-equations`** (OPEN). The matrix
  premise `ARR(L)` for every algebraically closed `L`.
- **`kervaire-laudenbach-holds-for-linear-sofic-groups`** (OPEN), with route
  `kl-for-linear-sofic-via-amplified-algebraic-roots`.
- **`char-two-jordan-square-root-needs-amplification`**, with route
  `char-two-jordan-square-root-amplification-proof`. In characteristic 2,
  `t^2 = J_2` has no root in `GL_2` but has one after doubling. So exact roots
  can need amplification.

### Exact Groebner tests (MSI job 746283, Sage 10.7)

Each test sets up the ideal generated by `TU - 1` and `w(T; consts) - 1` in
the polynomial ring on the entries of `T, U`, and asks whether `1` lies in the
Groebner basis. By the Nullstellensatz, `1 in ideal` means no root exists over
the algebraic closure at that amplification; otherwise a root exists.

| test | field | N | verdict |
| --- | --- | --- | --- |
| `t^2 = J_2`, r=1 | F_2 | 2 | NO ROOT |
| `t^2 = J_2 (x) 1_2`, r=2 | F_2 | 4 | root exists |
| `x a x a x^{-1} b`, a=(01), b=(02), r=1 | F_2 | 3 | root exists |
| same | F_3 | 3 | NO ROOT |
| same | Q | 3 | root exists |
| three exponent-sum-1 words, constant `J_2` | F_2, F_3, Q | 2 | root exists (all) |

**Two findings.**
- The char-2 Jordan pair confirms `char-two-jordan-square-root-needs-amplification`
  both ways: no root at `r = 1`, a root at `r = 2`.
- The symmetric word `x a x a x^{-1} b` has no exact root at `r = 1` over the
  algebraic closure of `F_3`, although it does over `Q` and over `F_2`. So
  amplification, or characteristic change, is genuinely needed for exact roots
  even for a permutation-module constant tuple. This is exactly the phenomenon
  the amplified premise `ARR` is built to absorb, and it shows `ARR` at `r = 1`
  is false, so the amplification in the transfer theorem is not removable.

## Exact gap

Decide `ARR(L)` for algebraically closed `L`. In module form: every
finite-dimensional representation of a finitely generated group should extend,
after amplification and up to a rank-small defect, to every nonsingular
adjunction.
- *Where it holds:* over `C` for unitary tuples, with `r = 1` and exact roots.
- *Where it is open:* non-unitarizable constants over `C`, and everything in
  positive characteristic.
