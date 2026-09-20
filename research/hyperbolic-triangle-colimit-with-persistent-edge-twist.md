---
rg: 2
id: hyperbolic-triangle-colimit-with-persistent-edge-twist
kind: claim
title: A hyperbolic triangle colimit whose moment space survives every finite cover
distinct_from:
  persistent-degree-two-class-on-hyperbolic-group: that asks for any persistent class on a residually finite hyperbolic group; this asks for the explicit edge-twist classes of a triangle colimit, certified through the moment spaces of edge-twist-extensions-of-triangle-colimits-moment-test, and assumes no residual finiteness
  hyperbolic-triangle-of-finite-groups-not-virtually-torsion-free: that asks for torsion invisible in every finite quotient; this asks for a degree-two class on a triangle colimit that never dies in a finite cover, which kills residual finiteness of a central extension even when the colimit itself is virtually torsion-free
---

Exhibit a hyperbolic, virtually torsion-free colimit `Λ` of a triangle of finite groups
with trivial face group, and a prime `p`, such that the moment space `I_∞ <= F_p^3` of
`edge-twist-extensions-of-triangle-colimits-moment-test` is nonzero. Equivalently, some
2-cycle moment `c_12 μ_12 + c_23 μ_23 - c_13 μ_13` is nonzero on the 2-cycles of every
finite torsion-free normal cover. By (M6) of that node, some hyperbolic group is then not
residually finite.

**OPEN.**

## Attempts

- **Prime-to-`p` covers preserve moments** (M5). Transfer shows that covers of index prime
  to `p` do not change `I_N`. This does not reduce persistence to the ordinary
  pro-`p` completion of one torsion-free `N`: such a cover can create new
  mod-`p` first cohomology and enable a later `p`-tower. The reviewed theorem
  [[hrf-alt-persistence-needs-sylow-detours]] shows that every finite-cover
  vanishing test factors through a prime-to-`p` subgroup detour followed
  by normal index-`p` descents.
- **Where persistent classes must live.** The class must lie outside the image of
  continuous cohomology of the profinite completion
  (`finite-central-extension-rf-iff-virtually-splits`). So `N` must fail degree-2
  goodness at this class, and every hyperbolic virtually special group is good
  (`every-hyperbolic-group-is-good`, Attempts). Candidates therefore need (T) or some
  other obstruction to cubulation.
- **Cup products die.** If on some `N` the twist class is a cup product `h ∪ φ`, or a
  Bockstein `β(h)`, with `h in H^1(N;F_p)`, then pulling back to the `p`-cover defined by
  `h` kills it. This is the standard vanishing mechanism, recorded here as a heuristic:
  the Gysin-sequence argument was not written out. A persistent moment needs `N` whose
  classes in `H^2(N;F_p)` reached by twists are not profinitely visible, which is
  consistent with `H^1(N';F_p) = 0` along many covers.
- **Computation.** The test for one `N` is linear algebra of size `|Q| × 3|Q|/p` over
  `F_p`.
- **First-level data (2026-09-13, GAP 4.14 on MSI).** Scripts and raw outputs are in
  `experiments/edge-twist-moments/` (`moments.g`, `run1.g`, `run2.g`, `run1.out`,
  `run2.out`; `run1.out` predates the extra columns).
  - *Method.* Take random triples `x_12, x_13, x_23` of elements of prime order `p` in
    `Q = PSL(2,q)`. Form the coset triangle with vertex groups `<x_12,x_13>`,
    `<x_12,x_23>`, `<x_13,x_23>` and keep the hyperbolic ones (half-girths with
    `Σ 1/m_v < 1`). For `N = ker(Λ -> <x_12,x_13,x_23>)` compute:
    - `dim Z_N = |G| - rank(B)`, where `B` is the incidence matrix of right cosets
      against elements;
    - `dim I_N = rank([B; μ]) - rank(B)`;
    - `b_1(N;F_p)` from `χ(N\X) = 1 - b_1 + b_2`. It is printed only in `run2.out`;
      for `p = 3` the `run1.out` triples give `dim Z_N` and `dim I_N` only.
  - *Sanity check.* The Euler characteristic count gives an integer `b_1 >= 0` in every
    case.

  | `Q` | `p` | girths | `dim Z_N` | `b_1(N;F_p)` | `dim I_N` |
  |---|---|---|---|---|---|
  | `PSL(2,19)` (5 triples) | 5 | (6,8,8), (6,8,6), (6,6,8), (8,6,8), (6,8,6) | 1370 | 0 | 3 |
  | `PSL(2,29)` (2) | 7 | (8,8,8), (8,6,6) | 6962 | 0 | 3 |
  | `PSL(2,29)` (2) | 5 | (8,6,6) | 4874 | 0 | 3 |
  | `PSL(2,31)` | 5 | (6,10,10) | 5954 | 0 | 3 |
  | `PSL(2,27)` | 7 | (6,6,8) | 5618 | 0 | 3 |
  | `PSL(2,23)` (5 triples) | 3 | e.g. (16,14,8), (4,14,14) | 178–584 | 44–176 | 1–2 |

  In every hyperbolic coset triangle with `p >= 5`, all three vertex groups equal `Q`,
  `N` has no `F_p`-homology in degree 1, and no nonzero edge twist splits at the first
  level. So the cheap vanishing mechanism (cup products and Bocksteins from
  `H^1(N;F_p)`) is unavailable there. With `p = 3` there is plenty of `H^1`, and the
  moment space is already smaller.
- **Cartan–Leray filter (standard; not re-derived at chain level).** Let `N'' <= N` be
  normal in `Λ`, with `R = N/N''`. Pushing forward `H_2(N'';F_p) -> H_2(N;F_p)` is the
  edge map of `E^2_{s,t} = H_s(R; H_t(N'';F_p))`. Its cokernel is filtered by
  subquotients of `H_1(R; H_1(N'';F_p))` and `H_2(R;F_p)`. So `I_{N''} = I_N` unless `N`
  has a finite quotient `R` with `p`-torsion in `H_2(R;Z)`, or with
  `H_1(R; H_1(N'';F_p)) != 0`.

  For the `p >= 5` examples above, a persistence proof would therefore need exactly
  this: no finite quotient of `N` carries such `p`-local second homology along the
  tower. That is the concrete shape of the open problem for these explicit groups.
- **Kazhdan colimits with a first level (2026-09-13, lane ex2-triangle-persistence).** The goodness
  bullet above asks for (T) or another obstruction to cubulation.
  - *The groups.* `kazhdan-hyperbolic-sl2-root-triangles` supplies hyperbolic Kazhdan triangle colimits
    with vertex groups `SL_2(q), SL_2(q), SL_2(q^2)` and edge groups `(Z/2)^f`, for `q = 2^f >= 8`. The
    untwisted member `Λ_0` has the torsion-free first level `N = ker(Λ_0 -> SL_2(q^2))`
    (`sl2-root-kazhdan-triangle-untwisted-member-maps-onto-sl2`).
  - *Twists.* Here `p = 2`, and the twist space is `⊕_e Hom(E_e, F_2) = F_2^{3f}`.
  - *All of H^2 is twists.* The vertex groups are perfect, and for `q >= 8` their Schur multipliers are
    trivial (standard, not re-read). So the hypothesis of the Remark in
    `edge-twist-extensions-of-triangle-colimits-moment-test` holds.
  - *The test for these edges.* The moment test for elementary abelian edge groups is
    `edge-twist-moment-test-elementary-abelian-edges`.
  - *First-level data* (`sl2-root-kazhdan-untwisted-first-level-moments`, computed). For `q = 8`, the
    level `N = ker(Λ_0 -> SL_2(64))` has `b_1(N;F_2) = 18` and `b_2(N;F_2) = 164,858`. The moment space is
    `I_N = F_2^9`, so no nonzero twist splits there.
  - *Where it could die.* Unlike the `p >= 5` examples above, `N` has mod-2 first homology. Its dimension
    `18 = dim_{F_2} sl_2(F_64)` suggests an adjoint congruence 2-cover. Elementary abelian quotients of rank
    at least 2 have 2-torsion in `H_2`, so that cover is where the Cartan–Leray filter first allows a
    moment to die.
- **Finite central detector test and first-level audit (2026-09-20).**
  [[hrf-alt-edge-twist-finite-detector-spectrum]] gives a reviewed,
  explicit criterion when the vertices are perfect with
  `H^2(A_v;F_p)=0`: lift the vertices uniquely into a central extension
  of a finite quotient and compute their edge discrepancies. A twist
  has a finite central detector exactly when it occurs as such a
  discrepancy for some finite quotient. In the `p>=5` table, the recorded
  vanishing `H^1(N;F_p)=0`, together with `H^2(PSL_2(q);F_p)=0`, already
  forces full first-level moment rank. That rank is a consistency check,
  not independent evidence for persistence. The finite-quotient spectrum
  remains uncontrolled; these theorems do not establish this open claim.
  The additional independently reviewed obstruction
  [[hrf-alt-psl2-detectors-need-new-composition-factors]] excludes detector
  quotients assembled solely from arbitrary `PSL_2(q)` simple groups and
  cyclic composition factors of prime order different from `p`, for
  every prime `p>=5`.
- **Pinned integral first kernel and an actual second quotient (2026-09-20).**
  [[wave2-detector-psl19-perfect-first-kernel]] specifies three matrices
  in `PSL_2(19)` with link girths `(6,8,6)` and computes
  `H_1(N;Z)=0` by exact integral boundary reduction. The computation and
  its topological interpretation were independently reproduced and
  reviewed. [[wave2-detector-psl19-no-solvable-refinements]] consequently
  rules out every solvable-kernel refinement of that canonical quotient,
  including for each nonzero central five-twist. The limitation is
  concrete: [[wave2-detector-psl19-has-second-simple-quotient]] constructs
  a surjection onto `PSL_2(19)^2`, so `N` itself has a nontrivial simple
  quotient. That calculation does not determine the product kernel's
  first homology, and these results do not establish persistence.
- **Specified square-cover retention (2026-09-20).**
  [[wave3-detector-psl19-square-kernel-retains-five-twists]] proves that
  all three twist directions survive the particular `PSL_2(19)^2`
  cover just constructed. Prime-to-five transfer reduces the test to
  a400-point Borel-square permutation module, and three explicit
  orbit-moment cycles certify the result. The written proof and plain
  integer checker were independently reviewed and replayed. This does
  not compute the deeper kernel's first homology or control further
  covers, so the all-covers persistence target remains open.

- **Full mod-five homology of the square kernel (2026-09-20).**
  [[wave4-detector-psl19-square-kernel-mod-five-acyclicity]] proves
  `H_1(M;F_5)=0` for the specified square kernel, using a verified
  projective generator and64 exact tensor computations. The complete
  proof and computations were independently reviewed and replayed.
  Each nonzero twisted preimage also has zero first mod-five homology.
  Thus further five-group refinements over this quotient are excluded.
  Integral perfectness, mixed-prime solvable refinements, and additional
  nonsolvable quotients remain uncontrolled; this does not establish
  persistence through every finite cover.
- **Mixed three-and-five refinements excluded (2026-09-20).**
  [[wave5-detector-psl19-square-kernel-mod-three-acyclicity]] proves
  `H_1(M;F_3)=0` for the same specified square kernel. Its complete
  projective-generator calculation covers all coefficient-three
  components, including those missed by a smaller normalizer module.
  Combining this with mod-five vanishing excludes every refinement
  kernel whose prime divisors lie in `{3,5}`, using Burnside's
  two-prime solvability theorem. The same holds for nonzero twisted
  preimages. The proof and exact computation were independently
  reviewed, with the full generator and largest tensor replayed.
  Other-prime and arbitrary nonsolvable refinements remain open.
