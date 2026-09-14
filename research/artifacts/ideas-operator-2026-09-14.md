# Ideas operator, round 2 (2026-09-14)

Targets:
- `non-hyperlinear-group` (NH), with `some-countable-group-factor-is-locally-universal` (LU);
- the free group factor problem `L(F_2) = L(F_3)` (FGF);
- the strong Atiyah conjecture for torsion-free groups (SAC).

Base pin `174130833`.  Status of everything below: **landed, unreviewed.**

## Walls already on main (not re-proposed)

| Topic | Commits |
|---|---|
| Compilers | 3199a166d, 05787d432, e6421c3f6, 3b9b6582f |
| Stability | 4d6a8c736 → a0d51ab02 → 37354d619 → c5202d522 / 776aaf5b6 |
| Deligne | c5f8be311, 3341ad609 |
| Hyperlinear vs sofic | 480832739 / 3f347c3df |
| Locally universal factor | 38e8e74f9 (`hl-nh-locally-universal-2026-09-13`) |
| KL bridges | 3d31757e8, 66adf4dea, d92e493cb |
| Free group factors | 3a3ab40aa (`hl-free-group-factors-2026-09-13`) |
| Atiyah | 6e5392c53 |

Novelty checks are `git grep` at `174130833`.  "Existentially closed" hits only:
- surjunctivity, item (e) of `surjunctivity-is-axiomatized-by-rectangle-clauses`;
- Boone–Higman artifacts;
- the dead `kl-via-existentially-closed-overgroup`.

Nothing on main covers table-defined approximation properties or group factors.

## Ideas and quick-kill verdicts

1. **EC-HOST (NH).**
   - *Idea:* existentially closed (e.c.) groups as universal test objects for
     every table-defined approximation property.
   - *Not on main:* see the grep above.
   - *Test:* realize a finite table, with inequations, in an e.c. `H` through
     `H * G`.
   - *Kill:* the table system is not existential.
   - **PROMISING → executed** (T1, T2 below).
2. **EC-FACTOR HOST (LU).**
   - *Idea:* take `U` = any countable e.c. group as the canonical candidate.
   - *Not on main:* `hl-nh-locally-universal-2026-09-13` examined dense unitary
     subgroups, free products/HNN and Higman groups, but not e.c. groups.
   - *Test:* `L(Gamma) -> L(H)^omega` via table sequences.
   - *Kill:* moment transfer needs norm control that tables do not give.
   - **PROMISING → executed** (T3).
3. **CENTRAL-SEQUENCE UNIVERSALITY (LU).**
   - *Idea:* add commutation with growing finite subsets of `H`, solved in `H x Gamma`.
   - *Test:* `L(Gamma) <= L(H)' ∩ L(H)^omega`?
   - *Kill:* commutation is incompatible with separation.
   - **ALIVE → executed.** `L(H)` is a II_1 factor with a noncommutative central
     sequence algebra containing every countable group factor.
4. **E.C. TRACIAL ALGEBRA (LU).**
   - *Idea:* is `L(H)` existentially closed among tracial von Neumann algebras?
     E.c. tracial algebras are locally universal: embed `N` in the free product
     with `N`.
   - *Kill:* that is strictly stronger than LU.
   - **DEAD** (harder than the target).
5. **GENERIC GROUPS / FORCING (NH).**
   - *Idea:* let Robinson-forcing generic groups decide hyperlinearity.
   - *Kill:* generic groups are e.c., and by T2 all e.c. groups agree, so forcing
     returns the root's truth value and nothing more.
   - **DEAD** (collapses to T2).
6. **COMPUTABILITY FILTER (LU).**
   - *Idea:* `U` must be noncomputable
     (`computable-groups-have-no-locally-universal-group-factor`, conditional on
     Arulseelan–Manzoor).
   - *Test:* are e.c. groups noncomputable?
   - *Result:* yes, unconditionally, by the Novikov–Boone argument on route
     `ec-groups-decide-local-approximation-properties-proof`.
   - **PASSED**, not decisive.
7. **NON-RU TABLE IN ONE HOST (LU).**
   - *Idea:* the recorded gap of `hl-nh-locally-universal-2026-09-13` is to realize
     the non-RU Boolean moment table of `mipstar-bcs-tracial-nonru-exists` by
     triviality-pattern polynomials.  By T3 the host can be fixed once and for
     all to `L(H)`.
   - *Test:* approximate that moment table by contractions in `C[H]`.
   - *Kill:* equivalent to the ultrapower form of
     `non-ru-bcs-is-satisfiable-in-a-group-factor`.
   - **ALIVE**, no weaker than the recorded gap.
8. **SOFIC TO HYPERLINEAR ON E.C. GROUPS (NH).**
   - *Result:* every e.c. group is nonsofic (landed).  The hyperlinear analog is
     the root (T2).
   - *Kill:* the Leavitt obstruction is Hamming-specific (wall 480832739).
   - **Corollary landed**; the root is unchanged.
9. **TENSOR ABSORPTION (LU).**
   - *Idea:* `L(H) ⊗ L(Gamma) -> L(H)^omega` through the relative commutant.
   - *Kill:* `GF` is already closed under tensor products through direct products
     of groups.
   - **DEAD** (nothing new).
10. **FGF: L²-BETTI NUMEROLOGY.**
    - *Idea:* in known identifications `L(Gamma) = L(F_t)`, `t - 1 = beta_1^(2)(Gamma)`.
      Two cases:
      - surface groups, `L(pi_1 Sigma_g) = L(F_(2g-1))` (Shlyakhtenko preprint, pinned in
        3a3ab40aa), where `beta_1 = 2g-2`;
      - `Z/2 * Z/3`, with free dimension `1/2 + 2/3` and `beta_1 = 1/6` (Dykema's free
        dimension formula; not source-checked here).

      Dykema's compression formula `(t-1)/gamma^2` has the scaling of a first
      L²-Betti number.
    - *Not on main:* no node mentions Connes–Shlyakhtenko (0 grep hits).
    - *Test:* find `Gamma` with `L(Gamma) = L(F_r)` and `beta_1^(2)(Gamma) != r-1`.
    - *Kill:* invariance of `beta_1^(2)` among such `Gamma` would give
      `L(F_2) != L(F_3)`, and that invariance is the classical open step.
    - **ALIVE but classical.**
11. **FGF THEORIES INSIDE ONE HOST.**
    - *Idea:* compare the `L(F_n)` inside `L(H)^omega`.
    - *Kill:* a host sees only embeddings, i.e. universal theories, and these
      agree for `n in {2, ..., infinity}` (`F_infinity <= F_2 <= F_infinity`).
    - **DEAD.**
12. **FGF UNIFORM STRUCTURE.**
    - *Idea:* HJKE theorems and 1-bounded entropy.
    - *Kill:* uniform in `t`; already on main (3a3ab40aa).
    - **DEAD.**
13. **SAC-EC (Atiyah).**
    - *Idea:* torsion-free e.c. groups as test objects for strong Atiyah.
    - *Test:* is integrality of `dim ker A` a table predicate?
    - *Kill:* `dim ker A = mu_(A*A)({0})` is a limit of moments over growing balls,
      so no single finite table determines it and there is no model predicate.
      - Only the trivial transfer survives: SAC for all torsion-free groups iff SAC
        for all countable torsion-free e.c. groups (embedding plus induction).
      - No single host exists: a countable group has countably many finitely
        generated subgroups, while there are continuum many finitely generated
        groups.
    - **DEAD.**  Exact barrier: the spectral mass at 0 is non-local.
14. **SAC ARITHMETIC COMPLEXITY.**
    - *Idea:* `tau((1 - A*A/c)^k)` decreases to `dim ker A`, for `c >= ||A*A||`.
      So `dim ker A < q` is Sigma_1 relative to the word problem, and
      non-integrality is Sigma_2.
    - *Kill:* no finite certificate can bound `dim ker A` from below, so a
      certificate search for a counterexample can never terminate.
    - **DEAD** as a search, useful as a filter on 6e5392c53-style tests.
15. **STABILITY ON E.C. HOSTS (NH).**
    - *Kill:* the stability walls concern finitely presented groups; e.c. groups
      are not finitely presented, and stability does not pass to overgroups.
    - **DEAD.**
16. **QUANTUM SYMMETRY / SELF-TESTING (NH).**
    - *Kill:* already on main (`ex-nh-mipstar-quantum-symmetry-rung-2026-09-12`,
      `ideas-2026-09-13/nh/nh-self-testing`).
    - **DEAD.**

## Deep execution: existentially closed hosts

Landed claims (each with a route):
- `countable-groups-embed-in-countable-existentially-closed-groups` (T0):
  countable (torsion-free) e.c. overgroups exist, by union of chains.
- `existentially-closed-groups-contain-every-finite-table` (T1): every finite
  table of every group embeds isomorphically in every e.c. group.
- `local-approximation-properties-are-decided-by-ec-groups` (T2): for every
  model predicate, all groups have `P_M` iff some e.c. group does, iff every
  e.c. group does.  No e.c. group is computable.
- `existentially-closed-groups-are-nonsofic`: unconditional.
- `ec-group-factors-are-locally-universal-for-gf` (T3), for a countable e.c. `H`:
  - every countable group factor embeds in `L(H)' ∩ L(H)^omega`;
  - `L(H)` is a II_1 factor with property Gamma;
  - every algebra in `GF` embeds in `L(H)^omega`;
  - a locally universal group factor exists iff `L(H)` is locally universal,
    for one or for every such `H`.

**Exact barrier.**
- T1–T3 are equivalences.  An obstruction on `H` is a finite table of some
  group, hence of a finitely presented group
  (`local-approximation-properties-are-marked-closed`), and conversely.
- So e.c. hosts move the root into one canonical group without constraining
  which table is the obstruction.
- NH still needs one finite table with no Hilbert–Schmidt unitary model.
- LU still needs the non-RU moment table realized in `C[H]` (idea 7).
