# Idea lane nh-undecidable-J (target `non-hyperlinear-group`)

Lens: exact value-1 reductions to linear-system games, and a central mark `J`
whose triviality under approximation cannot be decided. This file contains ideas only. It claims nothing as solved and edits no Cairn node.

## What the sources actually say (checked 2026-09-13)

- **Taller–Vidick arXiv:2507.22444.**
  - Abstract: `LIN*_{1-eps,s} = RE` for some `1/2 < s < 1` and every small `eps > 0`. "Achieving the same result with eps=0 would imply the existence of a non-hyperlinear group."
  - Source l.180–197: imperfect completeness comes from the noise in the linearity test. They cite two further barriers:
    - an efficient reduction with classically perfect completeness would give P = NP;
    - the Paddock–Slofstra algebraic obstruction.
- **Paddock–Slofstra arXiv:2310.07901.**
  - l.1249–1280 (Proposition): a linear system that is tracially satisfiable but not `R^U`-satisfiable exists iff a non-hyperlinear finitely presented group exists.
  - l.1286–1296 (Cor. `cor:nofun`): for systems over LIN, tracial and algebraic satisfiability coincide.
  - l.196–200: consequently not every BCS algebra embeds in an LCS algebra.
  - l.1323–1334: a successful `B -> B'` construction "would have to use some particular feature of B, such as the fact that it is tracially satisfiable".
  - l.1399–1412: MNY show `SAT_{R^U}(BCS)` is `Pi^0_2`-complete. "Proving that SAT_{R^U}(LIN) is Pi^0_2-complete (or even just that it contains RE) would imply the existence of a non-hyperlinear group."
- **Mousavi–Nezhadi–Yuen arXiv:2110.04651 (abstract).**
  - Commuting-operator value exactly 1 is `Pi_1`-complete (via Slofstra).
  - Quantum value exactly 1 is `Pi_2`-complete for two-player games.
  - Their gapless compression theorem holds for both the q and co models.
- **Slofstra arXiv:1606.03140 (abstract).** Every finitely presented group embeds in a solution group, so deciding perfect co-strategies for LCS games is undecidable.

**The logic this lens uses.** If every group is hyperlinear, then for (finite or r.e.) linear systems `R^U`-satisfiability equals tracial satisfiability, which is "`J != 1` in the solution group", a `Pi_1` set. So any RE-hardness of `SAT_{R^U}(LIN)` forces a non-hyperlinear group.

**Repo nodes already covering the obvious routes (read, not repeated).**
- `re-oriented-lcs-compiler-gives-nonhyperlinear-group` (finite RE-oriented compiler ⇒ explicit group).
- `contextual-fano-cap-compiler-is-equivalent-to-perfect-lcs`.
- `boolean-relations-have-affine-complete-rstar-pp-gadgets`.
- `fano-cap-range-sections-cannot-encode-nonaffine-relations`.
- `binary-affine-safe-perfect-support-forces-classical-satisfaction`.
- `central-pinning-forbids-nonlinear-predicates`.
- `dfnqxy-answer-reduction-does-not-preserve-affine-safe-support`.
- `affine-halt-support-and-pcpp-section-close-nonhyperlinear-chain`.
- `relabelable-coset-systems-are-solution-group-corners`.
- `exact-label-coset-refinements-are-affine`.
- the note `notes/FALSE_PERFECT_COMPLETENESS_MASK_NO_GO.md`.

## Approach 1: carry read-out over `Z_{2^k}` to escape the F_2-affine firewall

**Idea.**
- The repo firewalls are F_2 statements: affine supports, Fano caps, and central pinning of involutions.
- Over `Z_4`, the subgroup `{(a,b,a+b)}` read out in binary bits is **not** F_2-affine, because the high bit carries `x AND y`.
- So compile the nonaffine verifier predicates into `Z_4`-linear systems with bit read-out. The solution group of a `Z_4`-system is still a group with a central mark of order 4.

**Would prove.** An exact BCS → (abelian coset system) compiler; with `relabelable-coset-systems-are-solution-group-corners` that gives an exact LCS-type compiler, hence a non-hyperlinear group.

**Kill test (hand computation, run).**
- Writing `a = x + 2u` and `b = y + 2v`, the high bit of `a+b` is `xy ⊕ u ⊕ v`. The carry only appears mixed with the free high bits `u, v`.
- To isolate `AND(x,y)` you must pin `u ⊕ v = 0`. But `{(a,b) : high(a) = high(b)}` is not a coset: `(0,1) + (0,1) = (0,2)` leaves it.
- More generally, every coset relation is closed under the Maltsev term `a - b + c` over `Z_4`, so clean-input Boolean gates are never pp-definable.
- On the quantum side, abelian coset syntax is already absorbed by `relabelable-coset-systems-are-solution-group-corners`. When the shared blocks are the source Boolean fibres, `exact-label-coset-refinements-are-affine` forces affinity.

**Verdict.** KILLED as a generic gadget. Only a model-dependent (support-specific) version survives, and that is the repo's affine-halt-support program.

## Approach 2: planted or structured masks in the Taller–Vidick test, using non-efficient reductions

**Idea.**
- The P = NP barrier concerns *efficient* reductions, but an RE-hardness reduction only has to be computable.
- So choose masks `mu` from a structured family (e.g. vanishing on a planted code) that is exactly 1 on every honest answer, while keeping the Fourier damping that soundness needs.

**Would prove.** `LIN*_{1,s} = RE`, hence a non-hyperlinear group.

**Kill test (repo note, run).** `FALSE_PERFECT_COMPLETENESS_MASK_NO_GO.md`:
- §2: full-support honest strategies force degenerate noise.
- §4: the random-guessing floor closes the tailored-noise repair.
- §5: exposing the mask as an answer restores every character, because homogeneous XOR constraints are closed under products.
The obstruction is algebraic (characters versus dictators), not a matter of running time, so dropping efficiency changes nothing.

**Verdict.** KILLED (a duplicate of the no-go note).

## Approach 3: RE-hardness of matrix satisfiability for LIN (Paddock–Slofstra conjecture, part (a)) as the route

**Idea.** Prove `SAT_matrix(LIN)` is RE-complete, the natural analogue of MIP* = RE, and derive a non-hyperlinear group from it.

**Kill test (logic, run).** Suppose every group is hyperlinear.
- `SAT_matrix(LIN)` (a finite-dimensional representation with `J = -1`) still differs from tracial satisfiability.
- It is RE by search, and nothing collapses it to the `Pi_1` set `J != 1`.
- So RE-hardness of matrix satisfiability is consistent with every group being hyperlinear. Only `R^U`-satisfiability works, as PS l.1412 says.

**Verdict.** KILLED as a route. It stays a separate, weaker target.

## Approach 4: exact quantifier layers (AND by disjoint union, OR by product sign, ∀ through r.e. presentations)

**Idea.**
- The disjoint union of linear systems sharing `J` has solution group the amalgam over `<J>`. It is exact both ways:
  - a tracial model with `J = -1` in each factor glues to the tracial amalgamated free product over `C<J>`;
  - an `R^U` model of the union restricts to each factor.
- Combined with `finite-lcs-product-sign-is-exact-or`, this gives exact finite monotone formulas.
- Infinite conjunctions are r.e. systems, and Higman makes them finitely presented at the end, since hyperlinearity passes to subgroups.
- So the universal quantifier layer of a `Pi_2` source is free.

**Would prove.** It would reduce `Pi_2`-hardness of `SAT_{R^U}(LIN)` to per-instance RE-hardness.

**Kill test (logic plus repo, run).**
- Finite AND/OR does not raise the arithmetical level.
- The existential layer is exactly the RE-oriented compiler (`re-oriented-lcs-compiler-gives-nonhyperlinear-group`).
- The r.e.-to-fp finish is already in `canonical-profile-kleene-higman`.
- The AND gadget is standard (disjoint union of systems).

**Verdict.** KILLED as a hardness amplifier. It is a correct, known utility: the whole difficulty sits in the Sigma_1 layer.

## Approach 5: move the central character off the roots of unity (irrational-twist relaxation)

**Idea.** Let `Gamma` be finitely presented with an integral central 2-cocycle `c`, and put `sigma^theta = exp(2 pi i theta c)`. Define `E(Gamma,c) = { theta in R/Z : the canonical trace of L_{sigma^theta}(Gamma) is R^U-embeddable }`.
- **(i) `E` is closed** (hand proof).
  - Canonical twisted traces vanish off the identity for every `theta`.
  - A microstate at `theta_n` satisfies the relations `u_g u_h = sigma^theta(g,h) u_{gh}` up to an error `2 pi |theta_n - theta| |c(g,h)|` on each fixed finite word set.
  - So microstates pass to the limit.
- **(ii) Rational twists.** For `theta = p/q`, the algebra is the corner `p_omega C[Gamma~_q]` of the finite central extension by `Z/q` (finitely presented). If all groups are hyperlinear, then `E` contains `Q/Z`, hence `E = R/Z`.
- **Contrapositive.** A single non-embeddable twist at *any* `theta` gives a non-hyperlinear finitely presented group (some `Gamma~_q`).

For this lens, exact completeness can then be sought at an *irrational* central character. The finite-group pinning theorem `central-pinning-forbids-nonlinear-predicates` and the order-2 firewalls do not apply there, and the phases `e^{2 pi i/d}` of Weyl–Heisenberg honest strategies (MIP* = RE with growing `d`) are the natural source.

**Would prove.** It turns the needed separation into a continuous-parameter statement: one non-CE twisted group factor of a finitely presented group at any twist.

**Kill test (run).**
- Hand proof of (i) and (ii) above.
- Repo: `sp4-finite-index-scalar-data-iff-hyperlinear-covers` states the Sp4(Z) finite-index case of this twist-torus picture. This file only records the general, group-independent form.
- Novelty against the literature is unchecked: the arXiv API returned "Rate exceeded".

**Verdict.** SURVIVES as a reformulation, with no construction yet.

**Next test.** Does the honest perfect model of the Culf–Mastel / DFNQXY protocol factor through `L_{sigma^theta}(Gamma)` for one fixed finitely presented `Gamma` and a fixed phase, with NONHALT soundness surviving the change of phase?
