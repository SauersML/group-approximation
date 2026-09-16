# Swarm lane on `rigid-sft-elementary-group-mod-centre-is-fp` (2026-09-16)

Agent: `swarm-rigid-sft-elementary-group-mod`. The target was locked for 180m and unlocked at the end.
Nothing was committed.

## Setup

- `Ω` is a free minimal `Z^2`-SFT, `A = LC(Ω, F_q)` and `R = A ⋊ Z^2`, assumed finitely presented
  (equivalently `Ω` quantum rigid, `sft-crossed-product-fp-iff-quantum-rigid`).
- The target asks that `EL_n(R)/Z` be finitely presented for some `n >= 4`.

**Gate (b) is exactly a statement about one kernel.**
- `projective-elementary-fp-kernel-criterion` (R finitely presented, `n >= 4`) says `EL_n(R)/Z` is
  finitely presented iff `K_2(n,R) = ker(St_n(R) -> E_n(R))` is finitely normally generated and
  `Z(E_n(R))` is finitely generated.
- The centre lies in `F_q^x 1_n` (`free-minimal-subshift-elementary-groups-are-simple-kazhdan`).
- So the target is equivalent to: `K_2(n,R)` is finitely normally generated in `St_n(R)` for some
  `n >= 4`. Finite generation of `K_2(n,R)` as a group suffices.

## What was proven

**New claim `z2-crossed-product-steinberg-kernel-is-nonzero`**, with route `-proof` requiring only
`steinberg-group-homology-gives-k2-and-k3` (ii). Proof in
`research/artifacts/z2-crossed-product-steinberg-kernel-nonzero-2026-09-16.md`.

Let `A` be any commutative ring with any `Z^2`-action and `R = A ⋊ Z^2`. Then
`c_n = [h_12(u_1), h_13(u_2)]` is a nontrivial element of `K_2(n,R)` for every `n >= 3`. Its order is
infinite or a multiple of the additive order of `1_A`, and it survives to `K_2(R)`.

**Mechanism.**
- **Hochschild chains.** `[g|h] -> tr((gh)^(-1)⊗g⊗h)` maps group chains of `GL_n(R)` to Hochschild
  chains of `R`.
- **Coefficients.** The total-degree-0 part maps to bar chains of `Z^2` with coefficients in `A`,
  via `x_0⊗x_1⊗x_2 -> (x_0x_1x_2)[deg x_1|deg x_2]`. Commutativity of `A` is used here.
- **Cocycle.** `N(g,h) = P_1(h_1) t_2^(h_2) P_2(g_2)`, a cup product of quantum-integer 1-cocycles, is
  a `Z[Z^2]`-valued 2-cocycle. Acting on `A`, it gives an `A`-valued Hochschild 2-cocycle `tau` with
  no invariant-measure requirement.
- **The torus pair.** The group 2-cocycle `f = tau∘tr∘Phi` satisfies `f(D_1,D_2) - f(D_2,D_1) = -1`.
- **Lifting.** Pull back to `St_n(R)`. The extension splits for `n >= 5` (Weibel III Prop. 5.5.1),
  and the splitting gives a conjugation-invariant homomorphism `sigma: K_2(n,R) -> A` with
  `sigma(c_n) = -1`.
- **Other ranks.** Ranks 3 and 4 follow by stabilization.

**Machine check.** `experiments/z2-crossed-product-steinberg-kernel-2026-09-16/verify_cocycle.py`
runs exact `F_5` arithmetic on `A = F_5^((Z/3)^2)` with translations. It checks the `N`-cocycle
identity, `tau∘b = 0`, the group cocycle identity on random words in `GL_3(R)`, and the value `-1`.
All pass (`output.txt`). `negative_control.py` shows the `tau∘b` test fails for the naive
non-invariant cocycle, so it is not vacuous.

**Consequence.** Gate (b) cannot be closed by `St_n(R) = E_n(R)`, as is done for polynomial rings.
A proof must finitely normally generate a nonzero kernel.

## Reduction recorded

Route `rigid-sft-quotient-fp-from-stable-k2-and-stability` requires the criterion, the finite-centre
claim, and two new holes:
- `sft-crossed-product-stable-k2-is-finitely-generated`: `K_2(R)` is finitely generated;
- `sft-crossed-product-unstable-k2-injects-stably`: `K_2(n,R) -> K_2(R)` is injective for some `n >= 4`.

The implication is elementary: a subgroup of a finitely generated abelian group is finitely generated.

## Approaches and exactly where each dies

1. **Vanishing of `K_2(n,R)`.** Dead in every rank, by the new claim.
2. **Stable `K_2(R)` via iterated ABC Theorem 3.6 (heuristic, unverified).**
   - Over `F_2`: `K_*(A) = (C(Ω,Z), 0, 0)`, so `K_2(R) ≅ Z` modulo twisted Nil terms of
     `B = A ⋊ Z`. The `Z` is the symbol class, consistent with the new claim.
   - It dies at Nil vanishing for `B`: ABC Lemma 7.2 needs regular supercoherence, known for `A` but
     not for the noncommutative `B`.
   - Over `F_q` with `q > 2` there is the extra term `H_1(Z^2; C(Ω, F_q^x))`. Its finiteness is a
     tiling-cohomology question with coefficients `Z/(q-1)`, not known for general minimal SFTs.
3. **Injective stability.**
   - Van der Kallen and Suslin--Tulenbaev need a Bass stable rank bound. `sr(LC(Ω,F_q) ⋊ Z^2)` is
     unknown, and even the `Z` case is open in the graph.
   - It dies there.
4. **Centrality of `K_2(n,R)` via Voronetsky.**
   - arXiv:2004.08551 and arXiv:2410.14039 need local stable rank conditions over the centre.
   - `Z(R) = F_q`, so localization is vacuous. It dies there.
5. **Using `sigma` as an obstruction to gate (b).**
   - `sigma` is conjugation invariant, so finite normal generation of `K_2(n,R)` would force
     `sigma(K_2(n,R))` to be finite.
   - Heuristically `sigma` factors through `H_2(Z^2; A) ≅ A^(Z^2) = F_q` for a minimal action, so its
     image is finite and it gives no obstruction.
   - An obstruction would need infinitely many independent `K_2` classes invisible to Hochschild
     homology in degree 0. Nothing found.
6. **Rank one (`d = 1`) does not transfer.** For `LC(X, F_2) ⋊ Z`, `K_2 = 0`
   (`binary-cantor-ring-stable-steinberg-group-centrally-closed`). The torus class needs two
   commuting translations.
7. **A possible negative direction (not pursued, heuristic).** Three things together would refute the
   target in all large ranks:
   - `K_2(n,R)` central in `St_n(R)` for `n >= n_0`, so normal generation is ordinary generation;
   - `K_2(n,R) -> K_2(R)` surjective for `n >= n_0`;
   - `K_2(R)` not finitely generated, for example if `q > 2` and `H^1(Z^2; C(Ω, Z/(q-1)))` is infinite
     for some rigid `Ω`.

   Ranks `4, ..., n_0 - 1` would still need separate treatment. All three inputs are open here.

## Literature (checked 2026-09-16, earlier in this lane; web search budget exhausted at the end)

- **Ara--Brustenga--Cortiñas**, arXiv:0903.0056v2: Theorem 3.6 and Lemma 7.2, via the graph claim
  `abc-twisted-laurent-k-theory-fibration`.
- **S. Voronetsky**, "Centrality of K_2-functor revisited", arXiv:2004.08551 (2020); and "Locally
  isotropic Steinberg groups I", arXiv:2410.14039 (v1 17 Oct 2024, v2 22 Nov 2024). Both are about
  centrality under local stable rank conditions, and neither applies to a ring with centre `F_q`.
- **Van der Kallen**, "Injective stability for K_2", LNM 551 (1976), and **Suslin--Tulenbaev**, Zap.
  Nauchn. Sem. LOMI 64 (1976). Known by listing only, unverified at theorem level.
- **C. Weibel**, *The K-book*, III Theorem 5.5 and Proposition 5.5.1, as quoted verbatim in
  `steinberg-group-homology-gives-k2-and-k3-citation`.
- **arXiv:1505.00725** (C*-stable rank of crossed products, not algebraic) and **arXiv:2511.20132**
  (C*-algebraic, seen in search results only). Not relevant to algebraic `K_2`.
- **Search outcome.** No 2024--2026 primary source was found on `K_2`, stable rank or finite
  presentation of `E_n` for algebraic `Z^2` Cantor crossed products. The target is not resolved in
  the literature as far as this lane could see.
- **Folklore, from memory, unverified.** The detection in the artifact is a hands-on form of the
  Dennis trace `K_2 -> HH_2` applied to the symbol of commuting units. It is not cited as a source
  and the artifact does not depend on it.

## Referee (2026-09-16)

**What was checked.**
- **The artifact, by hand, line by line.**
  - (1a) and (1b): `Phi` and the trace `T` are chain maps.
  - (2a): the degree-0 map `psi`, including the last face, where commutativity of `A` gives
    `a alpha_g(y) = alpha_g(y alpha_(-g)(a))`.
  - (3a)–(3d): the expansion of `delta c` cancels term by term, and
    `N(h,k) - N(g+h,k) + N(g,h+k) - t^k N(g,h) = -(delta c)(k,h,g)`.
  - (4a)–(4c): normalization via `P_2(0) = 0`, and the six diagonal terms, giving `f(D_1,D_2) = 0` and
    `f(D_2,D_1) = 1`.
  - (5a)–(5e): the extension, the formula `sigma(c) = f(D_1,D_2) - f(D_2,D_1)` for lifts of commuting
    elements, additivity and conjugation invariance on the kernel, and stabilization.
  - No slip found. The only import is Weibel III Prop. 5.5.1, which is quoted verbatim in
    `steinberg-group-homology-gives-k2-and-k3-citation` for every associative unital ring.
- **Consistency.**
  - It does not conflict with `binary-cantor-ring-stable-steinberg-group-centrally-closed`, which is
    `d = 1` only.
  - For the trivial action it agrees with `K_2(F_q[x^(±1),y^(±1)]) ⊇ Z{x,y}`.
  - The target's own Attempts already predicted the symbol class heuristically.
- **Machine check.** `verify_cocycle.py` and `negative_control.py` were re-run from a scratch copy.
  They took 13 s, and the output was identical to the committed output.
- **Reduction route.** It is logically correct.
  - `projective-elementary-fp-kernel-criterion` (3)⟹(1) holds, with the centre finite by
    `free-minimal-subshift-elementary-groups-are-simple-kazhdan` (all `n >= 3`, all `Z^d`).
  - A subgroup of a finitely generated abelian group is finitely generated.
- **Citations.** The abstracts of arXiv:2004.08551 and arXiv:2410.14039 were fetched. The titles,
  author and dates match.
- **Duplicates.** `bin/cairn search --similar` found no duplicate of the three new claims.

**What was changed.**
- `sft-crossed-product-stable-k2-is-finitely-generated`: corrected the over-`F_2` heuristic. Given ABC
  for `A`, `K_1(B) = C(Ω,Z)^(sigma_1)` and `K_2(B) = 0` exactly, and the Nil groups enter only at the
  second step. The earlier text attached Nil terms to `B` itself.
- `sft-crossed-product-unstable-k2-injects-stably`: restated the Voronetsky results to match their
  abstracts, and marked the theorem statements as not re-read.
- `z2-crossed-product-steinberg-kernel-is-nonzero`: added a Scope paragraph. The method is the
  classical Dennis trace, no broader novelty is claimed, and infinite order over `F_q` is not proved.
- Removed a stray `__pycache__` directory from the experiment folder.

**Verdict.** Landed with small fixes.
- The nonvanishing theorem is sound and correctly labelled as a route requiring only the Weibel import.
- The reduction is an honest route to two open holes, each with Attempts.
- The target remains OPEN.
