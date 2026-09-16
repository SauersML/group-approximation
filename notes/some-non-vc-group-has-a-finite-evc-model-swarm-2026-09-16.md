# Swarm lane: some-non-vc-group-has-a-finite-evc-model (2026-09-16)

- **Target and hole worked:** `some-non-vc-group-has-a-finite-evc-model`, the counterexample
  side of Juan-Pineda–Leary, Zaremsky Problem 1.7(A). Locked by
  `swarm-some-non-vc-group-has-a-finite`.
- **Outcome:** partial progress. The lane found new necessary conditions and a characterization
  of finite `E_VC` models through commensurators. No witness was found and no refutation was
  proved.

## Setup

A witness is a group `G`, not virtually cyclic, with a finite `G`-CW model `X` for `E_VC G`.
Already recorded constraints: von Puttkamer–Wu 1607.03790, Proposition 1.1, and the candidate
table `research/artifacts/zp-vc-counterexample-candidates-2026-09-13.md`.

Every published proof of Juan-Pineda–Leary for a class goes through BVC. This lane asked what
more a finite model gives, beyond BVC and the Proposition 1.1 finiteness of `G` and of Weyl
groups of finite subgroups. It looked in the Lück–Weiermann decomposition along
commensurability classes of infinite virtually cyclic subgroups.

## What was proved

Full proofs are in `research/artifacts/finite-evc-commensurator-restriction-2026-09-16.md`.

1. **`finite-evc-model-restricts-to-commensurators`** (direct proof).
   - For infinite virtually cyclic `C`, `Y_C = {x : G_x ∩ C infinite}` is a finite
     `N_G[C]`-model for the Lück–Weiermann family `G[C]`.
   - Hence `N_G[C]` has type `F_infinity`, has a finite `E_FIN` model, and surjects onto `Z`
     whenever the modular homomorphism `Δ_C` is nontrivial.
   - The only nontrivial step is contractibility of `Y_C^H` for finite `H`: it is a directed
     union of the `X^D`, and the union is nonempty because `D = H·∩_h hC_0h^{-1}` qualifies.
2. **`finite-evc-iff-finite-efin-and-commensurator-models`** (route from 1). A group has a finite
   `E_VC` model iff:
   - (a) it has a finite `E_FIN` model;
   - (b) it has finitely many conjugacy orbits of commensurability classes;
   - (c) every commensurator has a finite `G[C]` model.

   The reverse direction is Lück–Weiermann Theorem 2.3 with Remark 2.5 and Proposition 5.1(ii),
   plus finiteness bookkeeping.
3. **`finite-evc-unimodular-weyl-groups-have-finite-efin`** (route from 1). If `Δ_C ≡ 1`, then:
   - `X^C` is a finite `E_FIN(N_G(C)/C)`;
   - `N_G(C)` has type `F_infinity`;
   - for `C = <c>`, `Z_G(c)` has type `F_infinity`.

   Key step: the cells of `X^C` in the orbit `N τ_j` correspond injectively to `W_j`-classes of
   subgroups `n^{-1}Cn <= W_j` of index `i(W_j,C)Δ_C(n)`. That index is constant exactly when
   `Δ_C` is trivial on the relevant set.
4. **`finite-evc-positive-length-centralizers-have-finite-efin`** (route from 1 and 3). The
   hypothesis is `ℓ(g) > 0` for a homogeneous conjugation-invariant length: `|φ|` for
   `φ: G -> R`, a homogeneous quasimorphism, or a stable translation length. Then:
   - `N_G[<g>]` is unimodular and equals `N_G(<g^M>)`;
   - all `Z_G(g^k)` have type `F_infinity`, with finite `E_FIN` quotients by `<g^k>`.

   Corollaries:
   - `Q × Z` with a finite `E_VC` model forces every `Z_Q(q)` to have type `F_infinity` and a
     finite `E_FIN` model.
   - In an ascending HNN extension of `H` by `θ` with a finite `E_VC` model, every
     `Fix(ι_h∘θ)` has type `F_infinity` with a finite `E_FIN` model, and
     `Per(θ) = Fix(θ^M)` for one `M`.

## Approaches and where each dies

- **Non-unimodular commensurator, to contradiction.** The hope was that a finite model forces
  `Δ_C ≡ 1`. This dies on Lück–Weiermann Example 2.6: in `Z[1/p] ⋊_p Z` with `C = <1>`, the
  Bass–Serre tree is a finite model for `E_{G[C]}(G)` while `Δ_C(t) = 1/p`. So the pair
  `(N_G[C], Y_C)` alone carries no obstruction. The Schlichting-completion view says the same
  thing: totally disconnected locally compact groups can be non-unimodular and still act
  properly and cocompactly. Any proof must use several commensurability classes at once, as the
  BVC failure of `BS(1,p)` does. Recorded as the open question in Section 6 of the artifact:
  are commensurators in finite-`E_VC` groups always unimodular? Juan-Pineda–Leary implies yes.
  Not promoted to a hole, since it has no route into a root yet.
- **Target (T1), torsion-free groups with finitely many conjugacy classes.** Pigeonhole on
  `c, c^2, ...` gives `yc^ay^{-1} = c^b` with `a < b`, so every cyclic commensurator is
  non-unimodular. Theorems 3 and 4 do not apply. Theorem 1 only adds that each `N_G[<c>]` has
  type `F_infinity`, a finite `E_FIN` model, and a surjection onto `Z`. There is no
  contradiction: `G` has property FA, but its commensurator subgroups may map onto `Z`.
- **Central elements.** If `z` is central of infinite order, then `N_G[<z>] = G`, `Δ ≡ 1`, and
  `X^{<z>}` is a finite `E_FIN(G/<z>)`. Central extensions of groups with finite `E_FIN`
  models, such as Heisenberg over `Z^2`, satisfy this. So there is no contradiction, only the
  constraint.
- **Euler characteristic of the pushout.** Along an inclusion, the finite Lück–Weiermann pushout
  gives an additive identity among orbit-space Euler characteristics:
  `χ(G\E_VC) = χ(G\E_FIN) + Σ_[C] (χ(N\Y) − χ(N\E_FIN N))`. It carries no sign or integrality
  constraint that forces virtual cyclicity. Dead.
- **Target (T2), ascending HNN extensions.** Corollary 6 gives new necessary conditions
  (finiteness of twisted fixed subgroups, bounded periods), but no candidate `(H, θ)` was found
  that is killed only by these. For free `H` the case was already dead (vPW Theorem 2.11).

## Literature gate (checked 2026-09-16)

- **arXiv API**, `export.arxiv.org`, sorted by submission date, run 2026-09-16:
  - `all:"virtually cyclic subgroups" AND all:"classifying space"`: newest hit 2311.10257
    (2023); nothing from 2024–2026 on finite `E_VC` models.
  - `all:"Juan-Pineda"`: 2509.02195 (2025, K-theory of braid groups of the projective plane,
    not about this conjecture) and 2303.16961 (2023, commensurators of abelian subgroups, used
    for dimension).
  - `abs:"finite model" AND abs:"virtually cyclic"`: only 1807.10095, 1704.05304, 1607.03790.
  - `abs:"bounded virtually cyclic"` and `abs:BVC AND abs:"virtually cyclic"`: no hits.
  - Result: no 2024–2026 preprint found that settles the conjecture or states Theorems 1–4.
- **Read from PDF text this session:**
  - Lück–Weiermann math/0702646: Definition 2.2, Theorem 2.3, Remark 2.5, Example 2.6,
    Proposition 5.1, Corollary 5.4.
  - von Puttkamer–Wu 1607.03790v2 and 1807.10095.
  - Kochloukova–Martínez-Pérez–Nucinkis 0903.4079v2: abstract and introduction, where
    centralizers of type `FP_infinity` are an extra hypothesis.
  - Degrijse–Petrosyan 1108.6279: commensurators used for dimension only.
- **Via the root node (not re-read):** vPW 1704.05304 (linear groups) and
  Barnea–Camina–Ershov–Lewis 2210.15746 (residually finite groups). 1611.00567: abstract only.
- **Not accessible, unverified:** Juan-Pineda–Leary, Contemp. Math. 407 (2006); Groves–Wilson,
  Bull. LMS 2013 (soluble groups).
- **Recalled, not re-fetched:** Brown, J. Pure Appl. Algebra 44 (1987), Proposition 1.1.
- **Novelty assessment:** Theorems 1, 3, 4 and the forward half of 2 were not found in the
  sources read. They are elementary, so possibly folklore.

## Files

- `research/artifacts/finite-evc-commensurator-restriction-2026-09-16.md`
- `research/finite-evc-model-restricts-to-commensurators.md`, and its `-proof` route
- `research/finite-evc-iff-finite-efin-and-commensurator-models.md`, and
  `research/finite-evc-iff-finite-efin-commensurator-models-proof.md`
- `research/finite-evc-unimodular-weyl-groups-have-finite-efin.md`, and its `-proof` route
- `research/finite-evc-positive-length-centralizers-have-finite-efin.md`, and
  `research/finite-evc-positive-length-centralizers-proof.md`

## Referee (2026-09-16)

- **Verdict:** sound, landed with fixes. The target claim `some-non-vc-group-has-a-finite-evc-model` is still open. This round adds necessary conditions, not a construction or an obstruction.
- **Checked step by step:**
  - **Theorem 1 (restriction to `N_G[C]`):**
    - `Y_C` is a subcomplex.
    - It is `N`-invariant, with at most one `N`-orbit per `G`-orbit of cells.
    - Its fixed sets are empty or contractible, including the directed-union argument for finite `H` and the nonemptiness witness `D = H·∩_h hC_0h^{-1}`.
    - `Δ_C` is a homomorphism with free abelian image.
  - **Theorem 2:** the forward direction is Lück–Weiermann (LW) Corollary 5.4(ii). The reverse direction is the LW Theorem 2.3 pushout with the mapping cylinder of Remark 2.5, and the orbit counts are finite.
  - **Theorem 3:**
    - The map from double cosets `N_G(C)\T_j/W_j` to `W_j`-classes of `n^{-1}Cn` is well defined and injective.
    - `[W_j : n^{-1}Cn] = i(W_j,C)·Δ_C(n)`.
    - The BS(1,p) example is sharp: `Δ_C(t) = 1/p`, and `T^C` has infinitely many `N_G(C)`-orbits.
  - **Theorem 4 and its corollaries:**
    - `ℓ(g) > 0` forces `|a| = |b|` whenever `y g^a y^{-1} = g^b`.
    - `N_G[<g>] = N_G(<g^M>)` by finite generation.
    - `Z_G(g)/<g> ≅ Z_Q(q)` for `Q × Z`.
    - `Fix(ι_h∘θ)` is the corresponding centralizer quotient.
    - `Per(θ) = Fix(θ^M)` has index `M` in `Z_G(t^M)/<t^M>`.
- **Citations checked against arXiv TeX sources:**
  - LW math/0702646: Definition 2.2, Theorem 2.3, Remark 2.5, Proposition 5.1(ii) including the "finite type" sentence, and Corollary 5.4(ii). All numbering is correct.
  - von Puttkamer–Wu 1607.03790: Propositions 1.1 and 1.12. Correct.
  - Kochloukova–Martínez-Pérez–Nucinkis (KMN) 0903.4079: abstract matches.
  - Degrijse–Petrosyan 1108.6279: matches its use.
- **Fixed in place:**
  - Two `requires: []`-style proof steps appealed to Brown's criterion, J. Pure Appl. Algebra 44 (1987), "Proposition 1.1". That numbering was recalled, not fetched; ScienceDirect returned 403 and the search budget was exhausted.
    - The steps are in the route `finite-evc-model-restricts-to-commensurators-proof`, step 5, and the route `finite-evc-unimodular-weyl-groups-have-finite-efin-proof`, step 4.
    - Both now derive `F_infinity` from the verified LW Proposition 5.1(ii) in its finite-type form, via the new artifact item (F1'): `TR ⊆ FIN` with the bar construction gives finite-type `EV` for virtually cyclic `V`, then `TR ⊆ 𝒢` on the finite `E_𝒢` model.
    - The artifact's Theorem 1 and Theorem 3 steps were rerouted the same way.
    - Brown's paper is kept only as a recalled, non-load-bearing reference.
  - "new constraints on target (T2)" is softened to "constrain ...", with a sentence noting the constraints were not found in the sources read and may be folklore.
- **Duplicates:** `cairn search --similar` found no graph duplicates, and the `distinct_from` entries are accurate.
- **Remains open:**
  - whether some non-virtually-cyclic group has a finite `E_VC` model;
  - whether every cyclic commensurator in such a group must be unimodular.
    - Theorem 4 gives unimodularity for elements of positive homogeneous length.
    - The torsion-free, finitely-many-conjugacy-classes case (T1) is untouched.
