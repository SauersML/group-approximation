# Ideas round 2: Kaplansky units, zero divisors, Strong Atiyah (lane ideas-kaplansky-atiyah-2, 2026-09-14)

**Targets.**
- `integral-unit-conjecture-torsion-free` and `rational-unit-conjecture-torsion-free`, which are equivalent on the Promislow group `P`;
- `kaplansky-zero-divisor-conjecture`;
- `strong-atiyah-torsion-free`.

**Verdict: partial, unreviewed.** One structural theorem landed: `promislow-twisted-integral-rings-carry-gardam-units`.

- Twisted integral group rings `Z^c[P]` are classified by `H^2(P; Z/2) = (Z/2)^2`.
- The zero class is Higman's conjecture on `P`.
- The three nonzero classes carry nontrivial units with coefficients `+-1` and support 21. For one class this is Gardam's complex unit read over `Z`; the other two follow by an automorphism.

No unit conjecture was decided.

## 0. State read before ideating

- Units exist over `Z[zeta_8]` (Gardam). Over `Q` and `Z` the conjecture on `P` is open.
- Radius-4 residues do not lift (Tabei).
- All 52 radius-4 census pairs need `zeta_8`.
- Definite line shadows force monomial images mod `I_A`, `I_B`, `I_C`.
- Case A units lie in `+-1 + (I_A cap I_B cap I_C)`.
- The spectral capacity bound needs `||u||, ||u^-1|| > 2`.
- Char-`p` shadow-monomial units exist at `p = 2, 3, 5, 7`, so no mod-`p` shadow argument closes Case A.
- Barrier recorded on main: a proof must use `Z^x = {+-1}`; reductions alone prove a statement false for `Z[zeta_8]`.

## 1. Ideas, mechanism, kill test, verdict

1. **Twisted-class reformulation (EXECUTED, landed).**
   - *Mechanism:* grade `R[P]` by `rho: P -> (Z/4)^2`. The degree-zero subring is `Z^c[P]` with `[c] = beta(rho_1 + rho_2)`.
   - *Kill test:* exact multiplication in `Z^c[P]` (script, log lines (1)–(2)), plus a hand proof that the class is nonzero.
   - *Survives.* The integral problem on `P` sits at one class, and the other three classes fail over `Z` itself. This sharpens the recorded barrier: an argument that applies verbatim to all `Z^c[P]` proves a false statement **over the integers**, not only over `Z[zeta_8]`.
2. **Class-sensitive definite shadows (best survivor, not executed).**
   - *Mechanism:* the shadow argument of `promislow-integral-units-have-monomial-definite-line-shadows` proves monomiality for class 0. The twisted unit `abar` of a nonzero class has non-monomial shadows (7, 10 and 10 terms after the `zeta_8` gauge). So at least one shadow must turn indefinite or split for `[c] != 0`.
   - The restriction `c|_L` to `L = <x, y, z>` is a coboundary: `psi|_L` lifts because `L` is free abelian. The twist lives on the `K4` extension.
   - *Kill test:* compute the three shadows of `Z^c[P]` for the Gardam class. If one of them stays definite, the shadow argument applies to `abar` and something in main's shadow proof is wrong; if they all split, find the invariant that separates class 0.
   - *Survives.* This is the one existing input known to be class-sensitive.
3. **A class-sensitive Case A invariant.** Case A units are `1` on all three shadows.
   - *Mechanism:* look for a quotient or completion of `Z[P]` where class 0 has a positive-definite norm but nonzero classes do not. Candidates are the higher dihedral quotients `P -> C_2 * C_2` with twisted parameters, and the rank-2 quotient by `x + 1`.
   - *Kill test:* the ring `Z[P]/(x+1)` is a degree-4 crossed product over `Z[y^+-1, z^+-1]` with a quartic reduced norm, not a quadratic definite form. Check whether its norm has a sum-of-squares constant term.
   - *Survives weakly.* Merged into idea 2 as its second step.
4. **Archimedean capacity is class-blind (KILLED as a closing route).**
   - `integral-group-ring-units-have-arithmetically-large-spectra` uses integral coefficients, the positive faithful trace `sum u_g^2` and a domain complex algebra.
   - The twisted algebra `C^c[P]` is a crossed product `C*P` over a torsion-free elementary amenable group, so it is a domain by Kropholler–Linnell–Moody for crossed products (as usually quoted; not pinned here).
   - `Z^c[P]` has the trace and integrality. The capacity inequalities therefore hold for `abar` and cannot force triviality without a class-sensitive input. *Remark, not a claim.*
5. **Oliver's integral logarithm on `P/2^k L` (deferred).**
   - The kernel is torsion in `K_1`, including `SK_1`.
   - Twisted rings reduce to twisted group rings of the same finite groups, so this is class-blind unless `SK_1` data separates them.
   - *Low rank.*
6. **Case A certificate at radius 4 (computational; high value, low feasibility).**
   - *Goal:* "every unit of `Z[P]` supported in `B(4)` is trivial", which is Tabei's open Case A.
   - *Mechanism:* the scheme `A_(B(4), box155)` is finite over `Z` (`support-pair-unit-scheme-is-finite-over-z`). Compare `F_p`-lengths at the trivial points with char-0 multiplicities.
   - *Kill test:* about 200 unknowns with bilinear equations; a generic Groebner basis is infeasible.
   - *Survives* only with a structural reduction first (Craven–Pappas syllable symmetry, `rho`-grading).
7. **Bieberbach twisted census for class-0 units (counterexample hunt).**
   - Among 3-dimensional Bieberbach groups only `P` fails unique products (recalled; not pinned), so dimension 3 gives nothing new.
   - *Mechanism:* in dimension 4, non-unique-product Bieberbach groups (Carter's examples; not pinned) have their own `H^2(G; Z/2)`. SAT-search `+-1`-coefficient units of `Z^c[G]` at small supports for every Bockstein class. A class-0 hit is a Higman counterexample.
   - *Kill test:* pin Carter's list and compute `H^1(G; Z/4) -> H^2(G; Z/2)`. If every nonzero class is reached by `Z[zeta_8]`-type gauges only, the census is cheap on MSI.
   - *Survives.*
8. **Galois descent of `zeta_8` units combined with character twists (KILLED).** Over `Q(zeta_8)` the 16 `mu_4`-twists and `Gal = (Z/2)^2` act. A `Q`-point is a Galois fixed point up to gauge, which is the same as a class-0 twisted unit. Pure reformulation, subsumed by idea 1.
9. **Strong Atiyah for torsion-free finite extensions of congruence kernels (KILLED).** Already Farkas–Linnell, Theorem 1.1 (`p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah`).
10. **Zero divisors for Rips–Segev groups via special marked limits (KILLED as duplicate).** Owned by `rips-segev-groups-satisfy-kaplansky-zero-divisor` and lane hl-rips-segev-limits (B(8) wallspace gap).
11. **Atiyah counterexample from twisted units (KILLED).** The central `Z/2`-extension `Ptilde` is virtually abelian, and `Z^c[P] = Z[Ptilde]/(zeta+1)`. It has no fractional atoms beyond the `(1/2)Z` lattice, which torsion already explains.
12. **Zero divisors over `F_l` for Kazhdan congruence hosts via Iwasawa algebras (KILLED).** The closure of `Gamma(3)` in `SL_3(Z_l)`, `l != 3`, is all of `SL_3(Z_l)` by strong approximation, which has torsion. So Neumann-type domain results for torsion-free compact analytic groups do not apply.
13. **Units conjecture implies zero-divisor conjecture, used backwards (KILLED).** Only one direction is known; no mechanism.
14. **Twisted zero-divisor conjecture as a stress test (deferred).** Does `k^c[G]` stay a domain for torsion-free `G` and every class `c`? For `P`, Kropholler–Linnell–Moody covers crossed products. A twisted zero divisor on a non-unique-product group would show the untwisted proof must be class-sensitive, as idea 1 shows for units. *Kill test:* literature status of the crossed-product zero-divisor conjecture (not pinned).
15. **Positive-definite torus matrices with determinant 1 (KILLED).** `W(theta) = U U*` with `U = [[1, t], [0, 1]]` is positive definite with integer coefficients and determinant 1, yet not monomial. Only the `K4`-equivariance encodes the group ring, and that is the reduced-norm criterion already on main.

## 2. Ranked survivors

1. Idea 2+3: class-sensitive shadows and norms. The only known inputs that see `[c]`.
2. Idea 7: Bieberbach twisted census for class-0 units, a counterexample hunt on MSI.
3. Idea 6: radius-4 Case A certificate, after a `rho`-grading reduction.
4. Idea 14: twisted zero-divisor conjecture as a diagnostic.
5. Idea 5: Oliver log.

**Single best next deep lane.** Compute the definite shadows of `Z^c[P]` for the three nonzero classes. Show they split, and isolate the invariant that is definite only at class 0. Then test whether that invariant constrains Case A units beyond `+-1 + (I_A cap I_B cap I_C)`.

## 3. Checks

- Exact check on MSI: `ideas-kaplansky-atiyah-2-2026-09-14/twisted_integral_unit_check.py`, log `twisted_integral_unit_check-run.log`.
- Ownership: new ids only. No existing node was edited.
- Cairn: see the lane report for the `why` run on MSI.
