# Ideas, round 2: Boone–Higman after the groupoid refutation — 2026-09-14

Lane `ideas-bh-round2`. The task was to find novel routes to the Boone–Higman
conjecture, kill weak ones quickly, and execute the best survivor.

**Executed:** idea 1. It is landed as `pbh-class-closed-under-graph-products`,
which answers BFFHZ Question 3.1, via `pbh-graph-product-closure-proof`.

**Credit and literature.** Literature claims marked *unpinned* were not read at
source here.

**How ideas were screened.**
- **Duplicates.** Candidates were grepped against the ~590 Boone–Higman-related
  nodes on main at `d902ba34d`.
- **Walls.** Every idea was screened against:
  - `complexity-bounded-host-classes-are-not-universal`;
  - `self-similar-hosts-contain-only-residually-finite-groups`;
  - `input-encoded-sft-groupoid-hosts-are-not-universal` (Haagerup);
  - `kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`;
  - `deligne-lattice-embeds-in-no-rover-nekrashevych-group`.

**Sources read on MSI** (`/scratch.global/sauer354/bh-reviewer/`):
- BFFHZ arXiv:2503.21882v2, l.140–215 and 498–532 (Theorems C and E,
  Corollary F, Remark 2.5), l.660–730 (proof of Corollary F, Questions 3.1–3.4)
  and l.860–896;
- FFWZ arXiv:2603.24687, l.640–680, 1318–1352 and 1540–1562.

## 1. Ideas

**1. Retract amalgams inside Aut_H(H∗F_2) give graph products. EXECUTED, PROVED.**
- **Mechanism.**
  - Let `H` be a finitely presented simple MIF envelope of `K × X`.
  - Transvections `x ↦ xa` of one letter realize `H∗⟨y⟩`.
  - The twisted conjugation `γ_c: x ↦ xc, y ↦ c⁻¹yc` fixes `ρ_k` for `k` commuting
    with `c`, and conjugates `ρ_(yly⁻¹)` by `c` inside the constant.
  - This realizes `X ∗_C (C×K) ≅ (K∗L) ⋊ C` for a retract `C` of `X`.
- **Why it passes the walls.** It is permanence rather than a fixed host: the
  host `Aut_H(H∗F_2)` rises with the inputs.
- **Payoff.** Graph products of groups in `B_A` are in `B_A` (BFFHZ Q3.1: yes).
  The first new graph is `P_4`: for instance the `P_4` graph product of four
  copies of `V`.

**2. Boundary full groups of higher-rank lattices as Kazhdan hosts. ALIVE, HARD, top unexecuted.**
- **Mechanism.** Take `Γ` a cocompact lattice on a thick Ã_2 building `X`
  (exotic, so non-linear), and `∂_F X` the Cantor space of chambers at infinity.
  The candidate host is `D([[Γ ⋉ ∂_F X]])`. It is simple when the groupoid is
  minimal and effective (Nekrashevych/Matui, *unpinned*).
- **Why it passes the walls.**
  - The host contains `Γ`, so it is not Haagerup.
  - It is not Röver–Nekrashevych, and it is not an amenable-orbit full group: the
    orbits are Γ-orbits, and no invariant measure exists.
  - The groupoid is topologically amenable, which does not obstruct Kazhdan
    subgroups.
- **Kill test.** Finite presentation, calibrated on an arithmetic Ã_2 lattice
  (Boone–Higman already known).
- **Obstruction.** Z²-flats act on shadows by translations with unbounded
  sections, so there is no finite nucleus, and the rational similarity group and
  Belk–Hyde–Matucci presentations do not apply.
- **Targets.** Survey item 5.3(10); `exotic-a2-lattices-satisfy-boone-higman`.

**3. Rigidity barrier for Neretin-type hosts of buildings. BARRIER CANDIDATE, unpinned.**
- **Mechanism.** For thick irreducible locally finite Euclidean buildings of rank
  ≥ 2, an isometry between complements of bounded sets induces an automorphism of
  the Tits boundary. Boundary rigidity (Tits, Leeb; *unpinned*) should force it to
  agree with an automorphism off a compact set.
- **Consequence.** There is no rich almost-automorphism group, hence no
  rigid-permutation / Stein–Farley / oligomorphic vertex action of the
  Bux–Llosa Isenrich–Wu kind.
- **What it would explain.** Why tree methods are void for Kazhdan building
  lattices (`cat0-groups-satisfy-boone-higman`, Attempt 1).
- **Kill test.** Pin Leeb 2000 and the extension of Tits-boundary automorphisms.

**4. Fraïssé Thompson groups. ALIVE, beautiful, no finite-presentation mechanism.**
- **The pattern.** F, V and T are finitely presented dense subgroups of the
  automorphism groups of the ω-categorical structures (Q,<), the atomless Boolean
  algebra and the circular order. Each acts with finitely many orbits on pairs
  and finitely generated point stabilizers, which is type (A).
- **Proposal.** Build the same for the Rado graph, the random poset or the random
  tournament. Every countable group embeds in Aut(Rado) (*unpinned*).
- **Kill test.** Any finitely presented oligomorphic subgroup of Aut(Rado) with
  finitely generated stabilizers.
- **Why it could matter.** A new type (A) family not built on Cantor space.
- **Why it's fragile.** The Rado graph has no tree or Boolean chart for prefix
  replacements.

**5. Out(F_n) via `Aut_G(G∗F_n)/⟨⟨Inn F_n⟩⟩`. DEAD by computation.**
- **What works.**
  - `c_(x_2) ρ_g c_(x_2)⁻¹ = ρ_(x_2⁻¹ g x_2)`, so the normal closure K of
    `Inn(F_n)` contains `ρ_(x_2⁻¹ g x_2 g⁻¹)`.
  - Killing `G` gives a retraction `Aut_G(G∗F_n) → Aut(F_n)`, which shows
    `Aut(F_n) ∩ K = Inn(F_n)`. So Out(F_n) embeds in a finitely presented
    quotient.
- **Why it's dead.**
  - For simple `G`, K moves each coordinate of `Hom_G(G∗F_n, G) ≅ G^n`
    transitively, so the quotient has no inherited type (A) action.
  - K plausibly contains every transvection, so the quotient collapses to
    Out(F_n).
- **Consistency.** Matches BFFHZ l.883–892 and `out-free-groups-satisfy-boone-higman`,
  Attempt 2.

**6. Relative PBH for Out(F_n) through non-faithful type [A_2] actions (FFWZ). DEAD, same collapse as 5.**
Any action on which `Inn(F_n)` acts trivially is an action of `Ω/K`.

**7. Olshanskii–Sapir finitely presented torsion-by-cyclic non-amenable groups as test inputs. ALIVE as a test only.**
- **Coverage.** Zero hits on main.
- **Why they're a good test.** Hosts must contain bounded-exponent torsion
  extended by Z with no free subgroup. Residually finite, linear and self-similar
  hosts are excluded by Zelmanov (*unpinned*).
- **Status.** No mechanism and no barrier.

**8. Free Burnside groups B(m,n), survey 5.3(6). ALIVE as a test.**
- **Reduction.** To `B(2,n)` via Širvanjan's embedding (*unpinned*).
- **Dead hosts.** Residually finite, self-similar and linear hosts.
- **No mechanism yet.** Twisted Brin–Thompson hosts need a finitely presented
  type (A) actor containing `B(2,n)`.

**9. Gromov monsters with decidable graphical C′(1/6) presentations. WEAK BARRIER.**
- **Barrier.** Hosts must be non-exact.
- **Why it's weak.** It needs exactness of the known finitely presented simple
  families; exactness of V is *unpinned*.

**10. Relative hyperbolicity permanence via Bowditch-boundary germ extensions. ALIVE, overlaps shells.**
- **Idea.** Parabolic points become singular points with germ group `P`, fed to
  Belk–Hyde–Matucci Theorem 2.1.
- **Overlap.** Free products are the case Corollary F already does. The general
  case needs the germ hypotheses that
  `shell-isotropy-germs-fail-bhm-germ-hypothesis` records as failing for
  non-virtually-cyclic isotropy.

**11. Space-time virtual endomorphisms for Birget's cap.**
- **Status.** ADJACENT TO MAIN. Main's KMS affine lane (`solve-kms-self-similar-affine-2026-09-13`)
  already covers the nearest version.
- **Idea.** A finitely presented `G` with a trivial-core virtual endomorphism
  whose sections at depth n run a clocked machine for n steps.
- **Why it's attractive.** Finite presentation is inherited from `G`, not built.
- **Coverage.** This is Attempt 3 of
  `fp-self-similar-groups-with-arbitrarily-hard-word-problem`; the KMS operator
  algebra is non-commutative there. Not executed.

**12. (Centerless N)-by-B_A with Aut(N) ∈ B_A. LOW IMPACT.**
- **Mechanism.** `g ↦ (c_g|_N, gN)` embeds `G` in `Aut(N) × G/N`.
- **Payoff.** Free-by-B_A groups, and surface-by-B_A groups via punctured-surface
  MCGs; for example surface bundles over surfaces.
- **Why low impact.** It is the Bux–Llosa Isenrich–Wu / B̃_n trick already on
  main.

**13. Simple directed unions from ascending HNN extensions. DEAD.**
The kernel of `P → Z` is a simple directed union, but it is not finitely
generated and `P` is not simple.

**14. Input-dependent lattices in products of trees. DEAD by the wall.**
CAT(0) lattices have quadratic Dehn functions, so their word problem is in NP
(BORS; *unpinned* at l.235 of BORS as quoted in
`np-word-problem-groups-embed-in-fp-simple-polynomial-dehn-groups`). That is one
recursive bound for the whole family.

**15. Double-coset barrier for type (A) point stabilizers. LOW NOVELTY.**
- **Statement.** If `K \ Γ / K` is finite, the distances `d(x, gx)` take finitely
  many values in any Γ-space where `K` fixes `x`. So `K` fixes no point of any
  Γ-action with unbounded orbits.
- **Abelian quotients.** `K` has finite-index image in every abelian quotient.
- **Coverage.** Hand remarks for trees are on main (`higman-group-satisfies-boone-higman`).

## 2. Ranked survivors

1. Idea 1 — done.
2. Idea 2 — highest famous-root impact.
3. Idea 4.
4. Idea 10.
5. Idea 3, as a barrier to land after pinning.

## 3. Single best next deep lane

**Idea 2.** Decide whether `D([[Γ ⋉ ∂_F X]])` is finitely presented for a
cocompact Ã_2 lattice, calibrating on an arithmetic one.
- **Positive answer.** Boone–Higman for exotic Ã_2 lattices, the first Kazhdan
  non-linear CAT(0) inputs.
- **Negative answer.** A sharp barrier for boundary hosts of higher rank.
