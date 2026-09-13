# Idea lane nh-positivstellensatz (2026-09-13)

Target: `non-hyperlinear-group`. Lens: noncommutative real algebraic geometry
and trace positivity. This is an idea file. Nothing here is established, and
no Cairn node was edited.

## 0. Which separator form is correct

Γ is hyperlinear exactly when the canonical trace τ_Γ is a weak* limit of
normalized traces of approximate matricial models: finite sets F ⊂ Γ,
maps U: F → U(n) with small normalized-HS relator defect, and
|tr U(g)| small for g ≠ e. Finite-word Hahn–Banach duality (recorded in the
repo artifact `research/artifacts/atlas-matricial-trace-separator.md`) turns
this into a separator statement:

- Γ is non-hyperlinear iff there are a finite F, an ε > 0 and a self-adjoint
  h ∈ C[Γ] supported in F with τ_Γ(h) < 0, while Re tr h(U) ≥ 0 for every
  ε-approximate matricial model U on F.

In continuous-logic language, some universal sentence true in all matrix
algebras, and hence in R^ω, fails in L(Γ) at the generators.

"Trace-positive on matrices, negative on the group trace" is therefore the
correct form, and the relators are allowed to hold only approximately. The
directive's two phrasings are the same statement.

The binding constraint is the ESTABLISHED repo node
`global-tracial-positivity-cannot-separate-group-trace`: no certificate that
is sound in every tracial von Neumann algebra with exact relators can prove
such an h ≥ 0. A separator must be matricial-only.

## A. Universal SOS / tracial moment certificates

- **Idea.** Search R[Γ] or trace polynomials for h with τ_Γ(h) < 0 together
  with a sums-of-hermitian-squares-plus-commutators certificate
  (Klep–Schweighofer, arXiv:math/0607615, corrected by
  Burgdorf–Dykema–Klep–Schweighofer arXiv:1303.3711; the free group version
  with quadratic unitary polynomials is Juschenko–Popovych arXiv:1306.2163).
  Alternatively, get an SDP upper bound from the tracial moment hierarchy.
- **Would prove.** An explicit non-hyperlinear group with an SDP-checkable
  certificate.
- **Kill test.** Soundness of the certificate class.
  - SOS plus commutators is sound in every tracial von Neumann algebra that
    satisfies the relators, including L(Γ).
  - Klep–Magron–Volčič, "Optimization over trace polynomials"
    (Ann. Henri Poincaré, 2022; abstract read), give a hierarchy converging
    to the optimum under tracial constraints, not to the matricial optimum.
    They extract finite-dimensional optimizers only under flatness.
  - Repo artifact
    `research/artifacts/leavitt-tracial-moment-relaxation-no-go-2026-09-08.md`
    records the same wall for the moment relaxation.
- **Verdict: killed** (the fence node above). Calibration: explicit
  matricial-only separating polynomials exist on synchronous game algebras
  after MIP* = RE (synchronous approximate values via traces:
  Kim–Paulsen–Schafhauser arXiv:1707.01016, abstract read). What is missing
  there is realizing the winning trace as a group trace, which is the
  group-realization question for games, not this lens.

## B. Horn inequalities for sums of two group-algebra elements

- **Idea.** For self-adjoint a, b ∈ C[Γ], the τ_Γ-moments of a, b and a+b
  are computable from the word problem, so rigorous Chebyshev–Markov bounds
  pin down their spectral distributions. Look for a violated II_1 Horn
  inequality; those were first known in R^ω-embeddable factors.
- **Would prove.** Non-embeddability of L(Γ), with a finite numerical
  certificate.
- **Kill test.** Literature: are the II_1 Horn inequalities universal?
  Bercovici–Collins–Dykema–Li–Timotin, "Intersections of Schubert varieties
  and eigenvalue inequalities in an arbitrary finite factor"
  (arXiv:0805.4817, J. Funct. Anal. 258 (2010); abstract read), prove that
  the Horn-type inequalities for a+b+c=0 hold in an arbitrary finite factor.
- **Verdict: killed.** Horn inequalities are universal tracial facts, which
  is exactly what the fence node forbids as a separator.

## C. Collins–Dykema matrix-coefficient pencils as computable witnesses

- **Idea.**
  - Collins–Dykema, "A linearization of Connes' embedding problem"
    (arXiv:0706.3918, New York J. Math. 14 (2008); abstract and summary
    read), show that the embedding problem is equivalent to a statement about
    distributions of sums of self-adjoint operators with matrix coefficients.
  - For a candidate Γ with solvable word problem, take a pencil
    `T = A_0 ⊗ 1 + Σ_i A_i ⊗ (u_i + u_i*)` with small integer matrices A_i
    and group elements u_i. The τ_Γ-moments of T are exact word counts, so
    the spectral distribution of T gets rigorous interval bounds.
  - If that distribution provably lies outside the closure of distributions
    of the same pencil over matricial models, Γ is non-hyperlinear.
  - Because BCDLT covers only two-summand sums with scalar coefficients, the
    matrix-coefficient pencils are the natural place where a matricial-only
    spectral constraint might live.
- **Would prove.** A non-hyperlinear group with a finite, checkable spectral
  certificate: the pencil, a moment count and an interval bound.
- **Kill test run.** Is any explicit description of the matricial closure of
  pencil distributions known beyond the Horn case? Web searches (Collins–
  Dykema, BCDLT, recent "limiting Horn inequalities" work) found none. For
  two summands the cone is Horn and is universal (approach B). The
  computation side is easy; the certificate side has no candidate inequality.
- **Verdict: unclear, best survivor of this lens.**
  - **Next test.** Classify which spectral constraints on 2 × 2
    matrix-coefficient pencils in three unitaries hold uniformly in all M_n,
    e.g. through second-order freeness bounds of the kind Collins–Dykema use.
    Then decide whether BCDLT's Schubert-variety method already proves them
    in arbitrary finite factors. If it does, the lens is fully fenced for
    pencils too.
  - **Needed.** One pencil inequality that is matricial-only.

## D. Ozawa (T) certificate plus a central element

- **Idea.**
  - Take a Kazhdan central extension Γ̃ with infinite-order central z,
    Deligne-type.
  - Ozawa's criterion (arXiv:1312.5431, abstract read): Γ has (T) iff
    Δ² − κΔ is a finite sum of hermitian squares in R[Γ]. Such certificates
    are computer-searchable by semidefinite optimization (Netzer–Thom,
    arXiv:1411.2488, abstract read).
  - Evaluate the certificate at an ε-approximate model U and at Ad U on HS
    space, with errors bounded by the certificate's coefficient mass times ε.
    That gives explicit dimension-free constants placing W = U(z) near the
    approximate fixed space of Ad U.
  - Then split W into almost-scalar blocks. Keeping z far from 1 would force
    approximate λ-projective models of Γ̃/⟨z⟩ with λ far from ±1.
- **Would prove.** It reduces hyperlinearity of the extension to explicit
  quantitative projective-representation statements.
- **Kill test.** Hand check plus literature.
  - The certificate holds in every unitary representation, so it only gives
    near-invariance.
  - "Near the approximate kernel of Δ(Ad U)" is not "near a sum of scalar
    blocks". That step needs rounding almost-invariant subspaces in HS norm,
    i.e. Hilbert–Schmidt stability.
  - Becker–Lubotzky (arXiv:1809.00632, abstract read) show infinite
    hyperlinear (T) groups are not HS-stable. A later paper (arXiv:2307.13155,
    summary read) gives the same for local HS stability.
- **Verdict: unclear, leaning killed.** The explicit constants are real; the
  missing step is a matricial-only rounding, which is the HS-stability route
  rather than this lens.

## E. Dimension-sensitive corrections

- **Idea.** Use functionals that really do see the matrix size:
  - normalized swap expectations on C^n ⊗ C^n;
  - O(1/n²) Weingarten corrections;
  - integrality of projection traces in (1/n)Z;
  - determinant or index integrality.
- **Would prove.** A matricial-only inequality that fails at τ_Γ.
- **Kill test.** Hand computation.
  - After normalization each correction is O(1/n), or the integrality set
    (1/n)Z becomes dense, so all of them vanish in the normalized limit that
    defines hyperlinearity.
  - Voiculescu-type almost-commuting rotation matrices show integrality
    separators do not survive approximation. The rotation/Heisenberg setting
    is amenable, hence hyperlinear.
- **Verdict: killed.** Only uniform-in-n sentences survive the limit, which
  pushes every separator back to the universal theory of R^ω (approach C), not
  to finite-dimensional corrections.

## Summary

| # | Approach | Verdict |
|---|---|---|
| A | universal SOS / tracial moment certificates | killed (fence node; KMV hierarchy targets the tracial optimum) |
| B | Horn inequalities for a+b | killed (BCDLT: true in arbitrary finite factors) |
| C | Collins–Dykema matrix-coefficient pencils | unclear, best survivor: easy computation side, no known matricial-only pencil inequality |
| D | Ozawa (T) certificate + central element | unclear, leaning killed: needs HS rounding (Becker–Lubotzky) |
| E | dimension-sensitive corrections | killed (1/n decay, density, rotation matrices) |

The lens reduces to one precise question: exhibit one spectral inequality for
matrix-coefficient pencils that holds in all M_n uniformly but is not provable
in an arbitrary finite factor. MIP* = RE says such sentences exist
non-constructively on game algebras; none is known in pencil form.

Sources checked (abstract or summary level unless noted):
- Klep–Schweighofer, arXiv:math/0607615; Burgdorf–Dykema–Klep–Schweighofer, arXiv:1303.3711
- Juschenko–Popovych, arXiv:1306.2163
- Ozawa, arXiv:1312.5431; Netzer–Thom, arXiv:1411.2488
- Klep–Magron–Volčič, Optimization over trace polynomials, Ann. Henri Poincaré (2022)
- Kim–Paulsen–Schafhauser, arXiv:1707.01016
- Bercovici–Collins–Dykema–Li–Timotin, arXiv:0805.4817
- Collins–Dykema, arXiv:0706.3918
- Becker–Lubotzky, arXiv:1809.00632; local Hilbert–Schmidt stability, arXiv:2307.13155
- Repo: `global-tracial-positivity-cannot-separate-group-trace`,
  `research/artifacts/atlas-matricial-trace-separator.md`,
  `research/artifacts/leavitt-tracial-moment-relaxation-no-go-2026-09-08.md`,
  `affine-leavitt-tracial-square-function-firewall`
