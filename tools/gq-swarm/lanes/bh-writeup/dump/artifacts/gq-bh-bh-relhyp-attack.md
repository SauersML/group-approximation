# bh-relhyp: Boone--Higman for relatively hyperbolic groups (lane report, 2026-09-18)

Lane `bh-relhyp` of the BH swarm. Target: prove that a finitely generated
relatively hyperbolic group with solvable word problem and Boone--Higman peripheral
subgroups satisfies Boone--Higman, or locate the exact step that needs more.

## Outcome

Not proved. Three nodes landed:
- `rel-hyperbolic-groups-embed-with-fp-simple-peripherals` (ESTABLISHED, lane proof): any
  relatively hyperbolic `G` embeds in a relatively hyperbolic group whose peripheral
  subgroups are prescribed finitely generated overgroups of the old ones (Dahmani,
  Geom. Topol. 7 (2003), Theorem 0.1(2), read at source). With finitely presented
  simple overgroups the result is finitely presented when `G` is finitely presented
  relative to its peripherals.
- `rel-hyperbolic-bh-permanence-implies-free-product-closure` (ESTABLISHED, lane proof,
  elementary): the permanence statement implies free-product closure of the
  Boone--Higman class, which is equivalent on main to joint embedding plus
  `U * Z ∈ 𝓑` and is OPEN.
- `rel-hyperbolic-groups-with-bh-peripherals-satisfy-bh` (OPEN): the permanence
  statement, with known cases, the two reductions, and Attempt 1 stating the
  missing input (RB).

## Sources consulted

- Belk--Bleak--Matucci--Zaremsky, arXiv:2309.06224 (arXiv HTML): Theorems A, B, C, E;
  Proposition 5.5 (germ groups of contracting RSGs are virtually cyclic); Lemma 4.19
  (contracting lemma, where hyperbolicity is used); §1.3 open questions.
- Belk--Bleak--Matucci--Zaremsky, arXiv:2306.16356v3 (arXiv HTML): Theorem 5.1 list
  (items (5) limit groups and (8) finite-volume hyperbolic 3-manifolds), Problem 5.3
  items (1)--(13). Relatively hyperbolic groups are not mentioned.
- Dahmani, arXiv:math/0203258 (PDF): Theorem 0.1(1)--(3').
- Belk--Hyde--Matucci, arXiv:2407.03149 (TeX in the swarm source folder):
  `thm:MainFinitenessTheorem`, `cor:MainFinitenessCorollary`, `thm:Simplicity`,
  `thm:Abelianization`, and the Röver--Nekrashevych application.
- arXiv searches for "Boone-Higman" (17 results) and for "finitely presented simple"
  together with "relatively hyperbolic" (no results). No paper claiming this
  statement was found. No MathSciNet search.
- Belk--Fournier-Facio--Hyde--Zaremsky, arXiv:2503.21882 (abstract only):
  permutational Boone--Higman is closed under free products.

## Named consequences checked

- Limit groups: already BBMZ survey Theorem 5.1(5); also finitely generated linear.
- Finite-volume hyperbolic manifold groups: finitely generated linear, so
  `finitely-generated-linear-groups-satisfy-boone-higman`; dimension 3 is survey
  Theorem 5.1(8).
- Relatively hyperbolic 3-manifold groups: left to lane bh-3manifold, which owns
  compact 3-manifold groups.

## The precise open gate

(RB) in `rel-hyperbolic-groups-with-bh-peripherals-satisfy-bh`: a relative analogue of
BBMZ Theorem 4.1, realizing a group hyperbolic relative to finitely presented simple
groups inside a finite germ extension of a full contracting rational similarity
group, with the parabolic points as the singular set and germ groups `(B)_p × S_i`,
satisfying the Belk--Hyde--Matucci finiteness and simplicity hypotheses. Any such
construction for `S * T` would already give free-product closure.
