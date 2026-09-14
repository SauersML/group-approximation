# Idea lane ideas-kaplansky (2026-09-13)

Cluster: Kaplansky unit, zero-divisor and idempotent conjectures, strong Atiyah, Gottschalk
surjunctivity. First ideation, then quick kills against main and sources, then one deep execution.
Nothing here is independently reviewed.

## 1. Ideas, with status

Each idea lists: what it is, why it isn't already on main, the smallest decisive test, and the
kill criterion.

1. **Local transfer of the domain property.**
   - *Idea:* a zero divisor is a finite configuration, so it survives any partial homomorphism
     that is injective on its support products.
   - *Why new:* main has closure theorems for approximation properties (`local-approximation-properties-are-marked-closed`), not for the domain property.
   - *Test:* write the elementary proof.
   - *Kill:* already on main.
   - **PROMISING → executed** (`group-ring-domains-pass-to-local-embeddings`).
2. **Steenbock's question via special marked limits.**
   - *Idea:* main's Fisher--Sanchez-Peralta import makes group rings of torsion-free virtually compact special groups domains in every characteristic. So Rips--Segev groups would satisfy the conjecture if they were limits of special quotients, with no cubulation of the group itself.
   - *Why new:* main records the question in `cyclic-centralizer-groups-have-no-support-three-zero-divisors` but has no route.
   - *Test:* the route map plus the barrier for Kazhdan hosts.
   - *Kill:* the whole generalized family has property (T).
   - **PROMISING → executed.** See §2: alive for the original presentations, dead for Kazhdan ones.
3. **Kazhdan barrier for special approximation.**
   - *Idea:* Niblo--Reeves fixed points force every map from a (T) group to a torsion-free special group to be trivial, so finitely presented Kazhdan hosts are not special limits.
   - *Test:* source-check Theorem B.
   - **Executed** (`kazhdan-groups-map-trivially-to-torsion-free-special-groups`).
4. **Definite shadows on planes, not lines.**
   - *Idea:* send only one of `x, y, z` to `-1` and hope for a positive-definite norm form in two variables. Main's `promislow-integral-units-have-monomial-definite-line-shadows` uses lines where two go to `-1`.
   - *Quick kill:* the quotient `P/<x>` still has `(Z/2)^2` acting on `Z^2`, so the twisted algebra is a degree-4 crossed product, not quaternionic. Its reduced norm is quartic and its constant term is not a sum of squares.
   - **DEAD.**
5. **Real Positivstellensatz certificates for units of `R[P]`.**
   - *Idea:* real positivity kills complex solutions such as Gardam's `Z[zeta_8]` units.
   - *Quick kill:* main's census already shows the radius-4 nontrivial supports need `zeta_8`, which is not real. The definite-shadow proof uses only sums of squares, so it works over any formally real field. Little is added.
   - **DEAD as a new direction.**
6. **Oliver's integral p-adic logarithm on completed group rings.**
   - *Idea:* `tau(log v)` is a homomorphism on congruence units, since the trace kills Baker--Campbell--Hausdorff commutators. Integrality of `v` constrains 2-adic traces. Main has no Iwasawa or completed-group-ring nodes (`git grep iwasawa`: 0 files).
   - *Test:* compute `tau(log v)` on Case-A congruence subgroups of `Z_2[[P^_2]]`.
   - *Kill:* completed algebras have abundant units, so finite support must enter through growth, which is not visible yet.
   - **ALIVE, deep, not started.**
7. **Kronecker/Lehmer for matrix Laurent polynomials.**
   - *Idea:* an integral unit gives `M in GL_4(Z[t^+-])` with twisted symmetry and `|det M| = 1` on `T^3`.
   - *Quick kill:* elementary matrices already give non-monomial examples of that shape without the symmetry. The symmetry is what matters, and Gardam's `Z[zeta_8]` unit passes all non-positivity tests (Tabei §6.1, recorded on main).
   - **DEAD without positivity.**
8. **Fuglede--Kadison determinant equality case.**
   - *Idea:* for a unit, `det_FK(v) = 1` and `tau(v v*) >= 1`, and AM--GM is strict unless `v v*` is scalar.
   - *Quick kill:* no contradiction. The gap only measures spectral spread.
   - **DEAD.**
9. **Minimal fields of definition of nontrivial units of `Qbar[P]`.**
   - *Idea:* ask which number fields `K` carry nontrivial units in `K[P]`. Main shows fields containing `zeta_8` do. `bounded-support-char-p-units-force-qbar-units` gives the transfer.
   - *Test:* the census over `Q(i)` and `Q(sqrt(-2))` on supports outside the 16 `zeta_8`-forced ones.
   - *Kill:* every component is defined exactly over `Q(zeta_8)`.
   - **ALIVE, computational.**
10. **Shadow-sieved unit census at radius 5.**
    - *Idea:* impose monomial definite shadows as linear constraints before Groebner elimination, to push "no nontrivial units of `Q[P]` supported in `B(r)`" past `r = 4`.
    - *Kill:* the candidate supports at radius 5 aren't enumerable without a Tabei-type census.
    - **ALIVE, computational.**
11. **Hensel-lifted idempotents with Zalesskii traces in characteristic p.**
    - *Quick kill:* lifted idempotents have infinite support and no positivity. Main already has `char-zero-liftable-idempotents-are-never-inverse-defects`.
    - **DEAD / covered.**
12. **Garden-of-Eden linear-CA view of zero divisors.**
    - *Idea:* a zero divisor is a non-pre-injective linear cellular automaton.
    - *Quick kill:* main has 77 Garden-of-Eden files and 776 surjunctivity files. It adds nothing beyond soficity / amenability.
    - **DEAD / covered.**
13. **Finite extensions via Farrell--Jones K₀ induction for Rips--Segev groups.**
    - *Idea:* hyperbolic groups satisfy Farrell--Jones, so strong Atiyah passes from a finite-index subgroup with strong Atiyah.
    - *Kill:* it needs a finite-index subgroup satisfying strong Atiyah. Residual finiteness of hyperbolic groups is open (Delzant's finite-index unique-product subgroups need it), and unique products do not imply strong Atiyah.
    - **ALIVE but blocked on residual finiteness.**
14. **Surjunctivity through the K₀ state of the ternary Leavitt summand.**
    - **Covered:** by `hl-gottschalk-k0` (81c587b57, torsion shortcut refuted).

## 2. Deep execution: the zero-divisor question for Rips--Segev groups

**Landed claims** (Cairn should compute the first four ESTABLISHED; unreviewed):
- `group-ring-domains-pass-to-local-embeddings` (elementary);
- `marked-limits-of-special-groups-have-domain-group-rings` (+ Fisher--Sanchez-Peralta);
- `niblo-reeves-kazhdan-groups-fix-points-on-cube-complexes` (citation, PDF read);
- `kazhdan-groups-map-trivially-to-torsion-free-special-groups` (proof uses Niblo--Reeves);
- `rips-segev-groups-are-hyperbolic` (citation, TeX read);
- OPEN: `rips-segev-groups-satisfy-kaplansky-zero-divisor` (Steenbock's question, pinned verbatim), `rips-segev-groups-are-cocompactly-cubulated` (Martin--Steenbock open problem, pinned verbatim), `rips-segev-groups-are-marked-limits-of-special-groups`;
- routes `rips-segev-zero-divisor-via-cubulation` and `rips-segev-zero-divisor-via-special-marked-limits`.

**Where it stands.**
- Both routes need a special structure the literature doesn't have.
- For the Kazhdan generalized examples (Arzhantseva--Steenbock, arXiv:1407.2441, Cor `C: T`), both routes are provably closed:
  - cubulation, by their own observation;
  - special approximation, by the new barrier.
  So those groups need a mechanism that is neither geometric nor approximative. That makes them the sharpest candidate hosts for a counterexample in characteristic `p`, where strong Atiyah gives nothing.

**Sources read.**
- arXiv:1307.0981 (TeX): introduction, theorem `gh`, the question.
- arXiv:1407.2441 (TeX): Theorem `main`, Cor `C: T`, the problems section.
- arXiv:1409.3678 (TeX): the cubulation theorem statement, the Kaplansky corollary, the open problem.
- Niblo--Reeves, G&T 1 (1997): Theorem B (PDF).
