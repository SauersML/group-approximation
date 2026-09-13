# Idea lane nh-rigid-lattices (target `non-hyperlinear-group`)

Lens: rigid Kazhdan hosts. Candidates are Ã₂ and C̃₂ building lattices, Radu's lattices, the
non-residually-finite central extensions of p-adic lattices of de Chiffre–Glebsky–Lubotzky–Thom
(dCGLT), and Popa-type rigidity of their von Neumann algebras. The question: which rigidity input
could force every tracial approximation to kill a nontrivial element that the group keeps?

Nothing here is established, and no Cairn node was edited. Every verdict below comes from a kill
test that was actually run: a hand computation, an abstract or source check, or a repo node read at
origin/main `cb71b181f`.

## What the repo already has (read first, not repeated)

- `non-rf-kazhdan-weak-ucp-iff-non-hyperlinear` (THEOREM). For a non-residually-finite Kazhdan group,
  weak ucp-stability, flexible correction along hyperlinear approximations and non-hyperlinearity are
  equivalent.
- `hs-stability-plus-fd-residual-forces-nonhyperlinearity`: uniform flexible HS stability plus one
  word killed by every finite-dimensional unitary representation gives non-hyperlinearity.
- `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity` (ESTABLISHED, via Dogon–Vigdorovich
  arXiv:2506.20843) and its screen `classwide-hyperbolic-kazhdan-hs-stability-covers-fp-kazhdan`.
- `bdl-deligne-type-two-norm-inapproximability` (Bachner–Dogon–Lubotzky, arXiv:2508.17392). Stability
  in a small unitarily invariant norm forbids approximation in a larger one for Deligne-type groups.
  Their Conjecture 1.8: H²(Γ,V)=0 for all unitary V implies operator-HS-stable.
- `character-rigidity-equals-hyperfinite-hs-stability` (Dogon–Vigdorovich Thm 1.6, higher-rank Lie
  lattices only).
- The Titz Mite–Witzel family: `titz-witzel-simple-kazhdan-cat0-lattices-exist`, the kernel routes
  toward the positive roots, and `vcd-two-groups-contain-no-kazhdan-commuting-pairs`.
- The Deligne sector-floor nodes, e.g. `deligne-cover-sector-floor-below-exponent-one-half`.

## Approach 1: two-dimensional hosts can never be 2-Kazhdan

**Idea.** dCGLT (arXiv:1711.10238, Theorem 1.2, as quoted in `agent-bcl-two-kazhdan-literature-audit`)
turn finite presentation plus degree-two vanishing with unitary coefficients into Frobenius stability.
BDL's Conjecture 1.8 uses the same hypothesis for operator-HS stability. For any group acting properly
and cocompactly on a two-dimensional contractible building with property (T):
- b₀⁽²⁾ = 0 and b₁⁽²⁾ = 0, so the orbifold Euler characteristic equals b₂⁽²⁾ (Atiyah's formula);
- if χ > 0, nonzero harmonic L² 2-cochains exist, and they are not coboundaries, so H²(Γ, ℓ²Γ) ≠ 0.

**What it would prove.** A screen. Ã₂ and C̃₂ lattices, including the Titz Mite–Witzel lattices and
anything built around Radu's BMW groups, can never enter a stability proof through degree-two
unitary vanishing. Any stability route for them has to be non-cohomological. The repo node
`titz-witzel-simple-kazhdan-cat0-lattices-exist` already records H²(Γ, ZΓ) = H²_c(X) ≠ 0 for these
lattices, which fits.

**Kill test, run.** Hand count of χ per vertex for a vertex-regular thickness-(q+1) Ã₂ building, where
each vertex link is the incidence graph of a projective plane of order q:
- a vertex has 2(q²+q+1) neighbours, so (q²+q+1) edges per vertex;
- a vertex lies in (q+1)(q²+q+1) triangles, so (q+1)(q²+q+1)/3 triangles per vertex;
- χ per vertex = 1 − (q²+q+1) + (q+1)(q²+q+1)/3 = 1 + (q²+q+1)(q−2)/3, which is > 0 for every q ≥ 2.

With nontrivial stabilizers the orbifold χ is a positive multiple of the same density. The C̃₂ count
(generalized-quadrangle links) was not written out. The sign is expected positive by the same
computation, but that is unchecked.

**Verdict.** Killed as a route through degree-two vanishing for two-dimensional hosts; survives as a
screen. Whether b₂⁽²⁾ > 0 also obstructs *asymptotic* defect diminishing along approximations that
weakly contain ℓ²Γ is open. It is not automatic, since nonvanishing doesn't imply instability.

## Approach 2: exotic non-residually-finite hosts in dimension ≥ 3

**Idea.** Garland's method gives degree-two vanishing on thick buildings of dimension ≥ 3. If some
irreducible Euclidean building of dimension ≥ 3 carried a non-residually-finite cocompact lattice with
no finite quotients, dCGLT would make it Frobenius stable. That is a lattice, not a central extension,
with a word killed in every finite quotient.

**What it would prove.** A Frobenius-stable, minimally almost periodic Kazhdan lattice: a new host
for the BDL two-norm mechanism, with no Deligne cover needed.

**Kill test, run (standard facts, not re-read in this lane).**
- Tits' classification: thick irreducible Euclidean buildings of dimension ≥ 3 are Bruhat–Tits
  buildings of algebraic groups over local fields.
- Margulis arithmeticity: lattices in those automorphism groups (rank ≥ 2) are arithmetic, hence
  finitely generated linear, hence residually finite (Malcev).

So non-residually-finite lattices on irreducible buildings exist only in dimension 2. This matches
arXiv:2509.05054, whose examples are the first on any irreducible building and are C̃₂. There they
cannot be 2-Kazhdan, by Approach 1.

**Verdict.** Killed. In dimension ≥ 3, the only 2-Kazhdan non-residually-finite hosts are non-lattice
objects: central extensions of arithmetic lattices. That is the existing dCGLT / Deligne lane.

## Approach 3: robust spectral gap from Ozawa certificates on the Titz Mite–Witzel lattices

**Idea.** Titz Mite–Witzel prove property (T) for Γ₁² with Ozawa's semidefinite method, computer
assisted (arXiv:2509.05054, §4.6, "Property (T) using Ozawa's method"; seen through the HTML page).
- A certificate Δ² − κΔ = Σ ξᵢ*ξᵢ in ℝ[Γ] involves finitely many words.
- So it holds up to O(defect) in normalized HS for any almost representation.
- That gives a *robust* spectral gap on the trivial isotypic part of every almost representation.
Γ₁² has no finite-index subgroups (Titz Mite–Witzel), so its finite-dimensional representations are
trivial. The hope is that a robust gap plus no fd representations forces approximations to collapse.

**What it would prove.** Non-hyperlinearity of Γ₁², which is finitely presented, simple and Kazhdan.

**Kill test, run.** Ozawa (arXiv:1312.5431, abstract): a finitely generated Γ has property (T) iff
Δ² − κΔ = Σ ξᵢ*ξᵢ in ℝ[Γ] for some κ > 0. So *every* Kazhdan group has such a certificate and the same
robust trivial-isotypic gap. But `infinite-simple-kazhdan-hyperlinear-group` (answered on main) gives
EL₃(LC(X,F_q) ⋊ Z)/Z: infinite, simple, Kazhdan and LEF, hence hyperlinear. As an infinite simple
group whose fd images would be residually finite, it has no nontrivial fd representations.
Certificates therefore coexist with hyperlinearity and no fd representations.

**Verdict.** Killed as a non-hyperlinearity mechanism. It survives as a screen: a mechanism must
control the *nontrivial* isotypic parts of approximations (stability), not only the invariant part
(spectral gap).

## Approach 4: generic rigidity (simplicity, non-residual-finiteness, charmenability, Popa rigidity)

**Idea.** For a simple, non-residually-finite Kazhdan lattice, combine:
- Popa-type rigidity of L(Γ) inside R^ω (e.g. that rigid subalgebras of ultraproducts are close to
  finite-dimensional pieces);
- or a Dogon–Vigdorovich-type equivalence between character rigidity, hyperfinite HS stability and
  (T;FD)_rob;
so that hyperlinear approximations are forced toward fd representations, which don't exist.

**What it would prove.** Non-hyperlinearity for Γ₁², or for the Caprace–Rémy lattices.

**Kill test, run.**
- The same witness as Approach 3 is simple, Kazhdan, with no fd representations, and hyperlinear. So no
  argument from simplicity + (T) + "no fd reps" can work. Non-residual-finiteness adds only the NK1
  equivalence already on main.
- Dogon–Vigdorovich Thm 1.6 is stated only for irreducible lattices in real-rank ≥ 2 Lie groups
  (repo quote). Its conclusions concern hyperfinite HS stability and character rigidity, never
  hyperlinearity. For Γ₁², item 4 of that theorem (characters are limits of fd-representation traces)
  is false for the character δ_e whenever fd representations are trivial. So an extension of that
  equivalence to exotic lattices would only show Γ₁² is not character rigid and not hyperfinitely
  stable. That says nothing about hyperlinearity.

**Verdict.** Killed as a route. Any working mechanism must use geometry the hyperlinear witness lacks.

## Approach 5: numerical least-defect profile for Γ₁², mixing sector

**Idea.** Γ₁² has an explicit finite presentation, and Titz Mite–Witzel have a group-algebra
implementation on GitHub; check the relator count against the repo presentation. Its only fd
representation is trivial. So a hyperlinear approximation must be a unitary tuple with small relator
defect *and* small traces on short nontrivial words. Numerically minimize the normalized-HS relator
defect under the constraint |τ(w)| ≤ η for all words w of length ≤ L, in dimensions d ≤ 64, and record
the least-defect profile σ_η,L(d). A profile bounded below in d would be evidence for a sector-floor
statement like `deligne-cover-sector-floor-below-exponent-one-half`, but for a lattice with no fd
representations and no central extension. Decay would suggest approximations and redirect the lane
toward the positive `titz-witzel-kernel-sofic` routes.

**What it would prove.** Nothing rigorous. It would give a calibrated target: either a conjectural
dimension-free floor to attack with Approach 1-type geometric input, or evidence against this host.

**Kill test, run (by reading only).**
- `deligne-cover-sector-floor-below-exponent-one-half` shows these profiles are essentially
  non-increasing under tensoring and padding. So small d can only give upper bounds on σ, and a lower
  bound seen at small d says nothing about large d.
- Local optimization over U(d)^15 at d ≤ 64 is light. It would still need the msi wrapper, and this
  lane did not run it.

**Verdict.** Unclear. Its value is only as a filter for choosing hosts. Next test, a tiny MSI job: an
alternating-projection search for small-defect, small-trace tuples on the Prop 4.3 presentation at
d ∈ {8, 16, 32, 64}.

## Constraints this lane leaves for any rigid-lattice attack

1. Two-dimensional hosts need a non-cohomological stability input (Approach 1).
2. Non-residually-finite 2-Kazhdan hosts in dimension ≥ 3 are central extensions, not lattices
   (Approach 2).
3. Spectral-gap certificates are blind to hyperlinearity; the mechanism must act on nontrivial
   isotypic parts (Approach 3).
4. Simplicity, (T), non-residual-finiteness and character-rigidity equivalences don't suffice; host
   geometry must enter (Approach 4).

## Out-of-scope observation (unverified)

The HTML summary of arXiv:2509.05054 reported involution relators (g₁², g₂², g₄²) in the Prop 4.3
presentation. `titz-witzel-simple-kazhdan-cat0-lattices-exist` states the residual is torsion-free of
type F. These may refer to different groups: an ambient lattice versus its residual, or a
complex-of-groups presentation. It came from a tool summary, not source text, so a verifier should
check it against the paper.

## Sources checked in this lane

- arXiv:2509.05054 (abstract, and the HTML intro via summary): Titz Mite–Witzel, non-residually finite
  C̃₂-lattices; Theorem A, Corollary B, §4.6.
- arXiv:2605.06163 (abstract): Lécureux–Witzel, the normal subgroup property for proper cocompact
  actions on two-dimensional Euclidean buildings.
- arXiv:1312.5431 (abstract): Ozawa, the SOS characterization of property (T).
- arXiv:1711.10238 (abstract): dCGLT, Frobenius stability from cohomology vanishing and
  non-approximable groups.
- Repo nodes as listed above, read at origin/main `cb71b181f`.
