# High-impact literature roots: status and closure audit (2026-08-31)

## Scope and outcome

The audit checked six headline roots against their Cairn decompositions and
current primary literature.  None has a complete proof or counterexample
chain.  All six therefore remain **OPEN**:

| Root | Status | Exact live frontier |
|---|---|---|
| `boone-higman-conjecture` | OPEN | finite presentation of a simple envelope, represented most sharply by finite normal generation of a maximal kernel or either explicit compiler input |
| `hyperbolic-groups-virtually-torsion-free` | OPEN | whether the finite residual of every hyperbolic group is torsion-free |
| `non-residually-finite-hyperbolic-group` | OPEN | five live constructions; the shortest explicit one still needs a missing prime in the periodic-Higman spectrum |
| `kervaire-laudenbach-nonsingular-conjecture` | OPEN | nontriviality of the forced perfect cyclic-orbit quotient outside the hyperlinear/torsion-free cases |
| `strong-atiyah-torsion-free` | OPEN | division closure is a skew field for every torsion-free group |
| `whitehead-vanishing-torsion-free` | OPEN | vanishing for finitely presented torsion-free groups, now equivalent to the unrestricted conjecture |

No absence of a claimed resolution was turned into a theorem.  The statuses
below are literature checks; the only new established mathematical result of
this pass is the prime-spectrum reduction in the final section.

## Primary-source status checks

- **Boone--Higman.** Belk--Bleak--Matucci--Zaremsky,
  *Progress around the Boone--Higman Conjecture*, arXiv:2306.16356, state the
  general conjecture and survey classwise progress.  Belk--Fournier-Facio--
  Hyde--Zaremsky, arXiv:2503.21882, add `Aut(F_n)` and related classes, not a
  universal construction.
- **Hyperbolic residual finiteness and virtual torsion-freeness.** The former
  remains an explicitly open conjecture in Cui--Wan, arXiv:2604.04007,
  Section 1.2.  The latter is still Lueck's Problem 11.1(i); Cairn's exact
  finite-torsion-carrier criterion shows it is strictly weaker and leaves the
  finite-residual torsion question open.
- **Kervaire--Laudenbach.** Nitsche--Thom, arXiv:1811.07737, prove the
  hyperlinear case; Chen, arXiv:2302.09811v5, recovers the torsion-free case.
  Ramirez-Cote--Wise, *Math. Z.* (2025), DOI
  `10.1007/s00209-025-03753-3`, add right-angled Artin groups and subgroups,
  while explicitly retaining the general conjecture.
- **Strong Atiyah.** Fisher--Ng, arXiv:2606.19606 (17 June 2026), prove new
  finite-index torsion-free outer-automorphism-group cases.  Their
  introduction continues to state the unrestricted Strong Atiyah Conjecture
  as open.
- **Whitehead vanishing.** Lueck, *Survey on the Farrell--Jones Conjecture*,
  arXiv:2507.11337, Conjecture 3.6, states `Wh(G)=0` for torsion-free `G` as a
  conjecture.  The Cairn Waldhausen--Higman rope gives a genuine concentration
  theorem but no global vanishing theorem.

## New exact reduction on the periodic-Higman route

Suppose a prime `ell` lies in the period spectrum.  Starting with a finite
certificate `(H,alpha,h_i)`, quotient by a maximal proper `alpha`-invariant
normal subgroup.  The quotient `Q` is nontrivial, perfect, and
`beta`-simple.  Its induced automorphism has order exactly `ell`: its order
divides `ell`, and order one would give a finite quotient of the ordinary
Higman group, hence the trivial group.

A minimal normal subgroup and its `beta`-orbit then decompose `Q` as `S^m`
for one nonabelian finite simple `S`.  Automorphism-simplicity makes `beta`
transitive on the factors.  Since `beta` has prime order, `m` is `1` or
`ell`.  This proves
`periodic-higman-prime-spectrum-semisimple-reduction`.

The reduction is useful but deliberately not overclaimed.  A large-prime gap
still requires excluding both the simple case `S` and the cyclic-factor case
`S^ell` for at least one prime above the filling threshold.  Small-group
computational probes were not promoted: failure to find a certificate in a
bounded search is not a nonexistence proof.

