# Rounding on dCGLT building stabilizers (solve lane solve-nh-dcglt, 2026-09-13)

Target: `non-hyperlinear-group`, through the non-residually-finite central
extensions of p-adic building lattices of de Chiffre--Glebsky--Lubotzky--Thom
(dCGLT, arXiv:1711.10238). The idea under test was approach 5 of
`research/artifacts/ideas-2026-09-13/nh/nh-hs-stability.md`:
- round an almost representation on each finite building stabilizer with
  Gowers--Hatami;
- solve the resulting finite twisted intertwiner system;
- look for a dimension-independent defect floor.

**Verdict: route refuted as a solve route. One established transfer lemma is
landed** (`dcglt-stabilizer-rounding-is-vacuous-at-torsion-free-index`).
- **Why the route fails.** Passing to a torsion-free finite-index subcover
  keeps the normalized sector profile up to constants, and there every
  stabilizer is the central group. So stabilizer rounding carries no
  information of its own.
- **What remains.** The problem is the raw sector problem for a central
  extension of `pi_1` of a finite simplicial complex. It meets the recorded
  operator-norm wall of the Deligne ladder.
- **What the lemma also gives.** The explicit sector floor `delta d^(-1/2)`
  for the dCGLT covers, the p-adic analogue of the established floor for the
  real Deligne covers.

## 1. The construction, pinned against the source

Source: arXiv e-print 1711.10238, file "180214_asymptotic_stability_incl_alt_proof_.tex",
fetched on MSI. Line numbers refer to that file.

- **Theorem `main2` (line 182), verbatim:** "Let $\Gamma$ be a finitely presented group such that
  $H^2(\Gamma,\mathcal H_\pi)=\{0\}$ for every unitary representation $\pi$ ... Then, any asymptotic
  homomorphism $\ph_n \colon \Gamma \to {\rm U}(n)$ w.r.t. the Frobenius norm is asymptotically close
  to a sequence of homomorphisms, i.e. $\Gamma$ is Frobenius-stable."
- **Definitions (lines 300--318, 334).** `defect(phi) = max_(r in R) d(phi(r), 1)`,
  `homdist(phi) = inf_(pi in Hom) max_(s in S) d(phi(s), pi(s))`, and stability means
  `homdist(phi_n) -> 0` whenever `defect(phi_n) -> 0`.
- **Theorem `higherkazhdan` (line 937).** For `r >= 2` there is `q_0(r)` such that uniform
  lattices in a simple `K`-group of `K`-rank `r` over a local field with residue field of size
  `q >= q_0(r)` are strongly `(r-1)`-Kazhdan. Line 935: for torsion-free uniform `Gamma`,
  "$X:= \Gamma \backslash \mathcal B$ is a finite $r$-dimensional simplicial complex and
  $\Gamma= \pi_1(X)$". Line 943: "such $\Gamma$ contains a finite-index torsion free group $\Lambda$".
- **Proposition `kazhext` (line 919).** An extension of an `n`-Kazhdan group by a strongly
  `n`-Kazhdan (e.g. finite) group is `n`-Kazhdan.
- **Corollary `corka` (line 1012).** A finitely presented 2-Kazhdan group is residually finite or
  not Frobenius-approximated.
- **The examples (lines 1038--1094).**
  - `G = SU(n, D, h)` for the standard quaternion order `D`, of type `C_n`, with `G(R) = Sp(n)`
    compact and `G(Q_p) = Sp(2n, Q_p)` for `p >= 3` (line 1053).
  - `Gamma = G(Z[1/p])`, identified in the source with `U(2n) cap Sp(2n, Z[i,1/p])`, a cocompact
    lattice in `G(Q_p)`.
  - The congruence subgroup property holds (Rapinchuk, Tomanov, Prasad--Rapinchuk).
  - `Gamma~` is the preimage of `Gamma` in the universal central extension of `G(Q_p)` by `C(p)`,
    the roots of unity of `Q_p`, which is cyclic of order `p-1`.
  - The source Proposition: "Every finite index subgroup of $\widetilde{\Gamma}$ contains the unique
    subgroup of index $2$ in $C(p)$. In particular, if $p \geq 5$, $\widetilde{\Gamma}$ is not
    residually finite."

So the groups do act on a Bruhat--Tits building of dimension `n >= 3`
(`Sp(2n, Q_p)`, type `C_n`), with finite stabilizers and finite quotient, as the
idea file assumed. For `n >= 3` the building dimension is at least three, so
the two-dimensional screen of `nh-rigid-lattices` (b₂⁽²⁾ ≠ 0 for Ã₂) does not
apply.

## 2. The finite twisted intertwiner system for `Gamma~`

Write `Gamma~_sigma` for the preimages of the cell stabilizers: finite groups
containing `C(p)` centrally. A sector-`zeta` almost representation `phi` of
`Gamma~` restricts to each `Gamma~_sigma`. Every product in a finite group is a
bounded word, so the all-pairs defect there is at most a constant times the
relator defect. `gowers-hatami-finite-group-hs-stability` then gives genuine
representations `rho_sigma` on flexible enlargements, in sector `zeta` up to
`O(epsilon)` mass. Along inclusions, compressions are HS-close. For a finite
group, two genuine representations HS-close on the whole group are, after
deleting `O(epsilon)` normalized mass, conjugate by a unitary HS-close to the
identity. So the data become:
- vertex multiplicity vectors;
- edge unitaries on multiplicity spaces;
- a holonomy condition around 2-cells that carries `zeta`.

Exact data would give a genuine sector representation of `Gamma~`, which the
source Proposition and Malcev forbid for `zeta^2 != 1`.

## 3. Why this reduces nothing

`dcglt-stabilizer-rounding-is-vacuous-at-torsion-free-index`, `(TF1)`--`(TF3)`:
- `Gamma` has a torsion-free normal subgroup `Lambda` of finite index `k`.
- Its preimage `Lambda~` acts on the building through `Lambda`, with every cell
  stabilizer equal to `C(p)`.
- The sector profiles compare in both directions: restriction gives
  `sigma_(Lambda~)(d) <= N sigma_(Gamma~)(d)`, and induction of sector tuples
  (block permutation matrices with unitary blocks, exact on the coset action)
  gives `sigma_(Gamma~)(kd) <= N' sigma_(Lambda~)(d)`.

A floor for the finite system of `Gamma~` is therefore a floor for `Lambda~`,
whose system has no nontrivial local group. The local rigidity of the finite
stabilizers can't contribute. The problem is the approximate projective
representation problem for `pi_1(Y)`, `Y = Lambda\B` finite, with the central
extension class of `Lambda~`: edge unitaries whose 2-cell holonomies are close to
the scalars prescribed by the class. That is an instance of
`non-ce-twisted-group-factor-exists`, and `twisted-factor-existence-is-equivalent-to-nonhyperlinearity`
records that it is equivalent to the root.

## 4. Stabilizer densities cannot separate either

In any sector-`zeta` ultralimit, the restriction densities of the limit trace to
the finite stabilizers are consistent. The central-regular trace `tau_zeta`
(equal to `zeta^j` on `z^j`, and `0` off `C(p)`) is a positive-definite central
trace, being the vector state of `Ind_(C(p))^(Gamma~) zeta` at the unit coset.
Its restriction to a finite `F >= C(p)` has multiplicity density
`chi(1)^2/[F : C(p)]` on each `chi in Irr(F | zeta)`. So character-density
constraints on stabilizers are always satisfiable, and any floor must come from
the unitary holonomy data. This is in the spirit of
`central-regular-edge-constituents-are-fell-pure` and
`deligne-maslov-sector-traces-are-central-regular`; no separate node is landed
for it.

## 5. The wall

On the free complex `Y` the linearized correction problem is `H^2(Lambda, M_d)`
with the conjugation action and the normalized trace inner product. Garland and
Ballmann--Swiatkowski solve it with constants independent of `d`, because the
Hilbert module is arbitrary. The nonlinear correction `phi e^(ib)` needs
`||b||_op` control. The Garland solution is a Laplacian inverse on the
orthogonal complement of the harmonic cochains, bounded in HS but not uniformly
in operator norm. This is the recorded wall of section 2 of
`research/artifacts/deligne-hs-metric-ladder-2026-09-13.md`, and the Attempts of
`deligne-cover-sector-floor-below-exponent-one-half` ("first rung: bounded-rank
defects"). Exact local representations don't help: the obstructing discrepancy
is a small-rank, operator-size-one error on non-invariant subspaces, and
`kazhdan-unitary-corners-require-finite-dimensional-mass` forbids cutting it away.

So the dCGLT p-adic covers stand exactly where the real Deligne covers stand at
`g >= 3`:
- Frobenius collapse and the `delta d^(-1/2)` sector floor are established
  (`(TF4)` here; `(SG1)` there);
- the dimension-independent normalized floor, which is non-hyperlinearity in
  the sector, is open.

## 6. What would close the gap

- **A dimension-independent floor in some nontrivial sector.** For
  `Lambda~ = pi_1(Y)`-cover, an estimate that turns HS-small relator defect into
  operator-controlled corrections on all but `o(d)` dimensions, with a rounding of
  the remainder that respects the building's local links. Nothing recorded
  supplies this.
- **The other direction.** An explicit family of sector-`zeta` tuples for
  `Lambda~` with normalized defect tending to `0`. No construction is known,
  since finite quotients all kill `z^2`.

Landed nodes:
- `research/dcglt-stabilizer-rounding-is-vacuous-at-torsion-free-index.md`;
- `research/dcglt-stabilizer-rounding-vacuous-proof.md`.
