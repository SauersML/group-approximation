# sl3-z-weakly-ucp-stable: swarm attack, 2026-09-16

Agent: `swarm-sl3-z-weakly-ucp-stable`. Hole locked: `sl3-z-weakly-ucp-stable` itself.
Outcome: **obstruction.** The target stays open.

## Setup

- **Target.** `SL_3(Z)` is weakly ucp-stable. By Dogon (arXiv:2211.10492v3) this is equivalent,
  for a hyperlinear Kazhdan group, to flexible HS-stability. `SL_3(Z)` is residually finite,
  hence hyperlinear, and has (T).
- **Why central extensions.** The graph's working instability template for Kazhdan groups is the
  *visible central extension*:
  - take a Kazhdan central `Z`-cover `K~ -> K` whose centre survives at unbounded orders in
    finite quotients;
  - cut regular representations of the finite quotients down to the eigenspace where `z` acts by
    `e^(2πi/k)`;
  - the pulled-back maps are exact projective models with scalar defect `O(1/k)` and no fixed
    vectors of the kernel.
  - This is how `rf-kazhdan-group-not-flexibly-hs-stable` (`Z^(2g) ⋊ Sp_(2g)(Z)`) works, and it
    is the open premise at `GHB_2(7)` (`ghb7-finite-index-z-extension-center-survives`) and at
    `SL_3(F_q[t])` (`sl3-polynomial-finite-index-z-extension-center-survives`).
  - Dogon's Theorem 3.1 mechanism is also scalar-cocycle based.
- **The question attacked.** Does this template have an instance at `SL_3(Z)` or at any of its
  finite-index subgroups? Its finite-index subgroups matter because instability is usually
  produced there and transported.
- **Answer.** No.

## Literature gate (dated)

No resolution of weak ucp-stability or flexible HS-stability of `SL_3(Z)` was found as of
2026-09-16.
- Dogon, arXiv:2211.10492v3: the definitions, Theorem 3.1 (scalar-cocycle mechanism), Theorem
  1.3 and Theorem 1.10. Does not decide `SL_3(Z)`.
- arXiv:2506.20843v2 (listing dated 2026-06-23): no `SL_3(Z)` resolution found.
- Fournier-Facio, arXiv:2512.09180v2 (2026-06-08): no `SL_3(Z)` resolution found.
- arXiv:2607.17578: no `SL_3(Z)` resolution found.
- arXiv:2408.00110: no resolution of flexible stability of `SL_3(Z)` found.
- Chapman--Lubotzky, arXiv:2311.06706: no `SL_3(Z)` flexible-stability statement found.
- These were abstract-level or listing-level checks (the full-text extraction of some arXiv PDFs
  failed). "Not found" means only that.
- Ioana--Spaas--Wiersma, arXiv:2006.01874v2: Theorem A (the engine used by the graph's
  instability results).
- Web search budget was exhausted mid-session. Later checks used direct fetches only (Crossref
  API, the author's publication page).

## What was proven (research/ nodes written)

1. **`sl3z-schur-multiplier-is-klein-four`** (claim), with route
   **`sl3z-schur-multiplier-van-der-kallen-citation`** (`requires: []`, literature import).
   - `H_2(SL_3(Z); Z) = Z/2 × Z/2`.
   - Van der Kallen, Math. Ann. 212 (1974), 47--49, DOI 10.1007/BF01343979. Crossref metadata
     was fetched 2026-09-16, and the author's scan `schur.pdf` was fetched 2026-09-16; its page
     47 was read and the Theorem and Corollary pinned verbatim.
   - The identification `M(G) = H_2(G; Z)` for perfect `G` is classical (Milnor §5) and was not
     re-read.
2. **`sl3z-finite-index-fd-projective-multiplier-is-finite`** (claim), with route
   **`sl3z-finite-index-multiplier-lazard-whitehead-proof`**.
   - For every finite-index `K <= SL_3(Z)`, the finitely-dimensionally realizable multiplier
     `R(K) ⊂ H^2(K; T)` is finite and equals `H^2_cts(K^, Q/Z)`.
   - The proof is the graph's `Sp_4` argument
     (`sp4-finite-index-multiplier-lazard-whitehead-proof`) run at `SL_3`:
     - Step 0: finite dimension means profinite, via Malcev.
     - Step 1: congruence completion (`sl3z-finite-index-subgroups-are-congruence-subgroups`).
     - Step 2: Hochschild--Serre bookkeeping.
     - Step 3: primes not dividing the level, handled by van der Kallen.
     - Step 4: primes dividing the level, where `b_2(sl_3) = 0` goes through Lazard.
   - **Artifact.** `experiments/sl3z-finite-index-multiplier-2026-09-16/sl3-chevalley-eilenberg-betti.py`
     is an exact rank computation over `Q` of Chevalley--Eilenberg Betti numbers.
     - `sl_3`: `(b_1, b_2, b_3) = (0, 0, 1)`.
     - Calibrations: abelian `Q^2` `(2, 1, 0)`, `heis_3` `(2, 2, 1)`, `sl_2` `(0, 0, 1)`,
       `gl_3` `(1, 0, 1)`.
     - Output: `output.txt` in the same directory.
   - **Consequence** (with the established `finite-fd-multiplier-projective-models-round-strictly`):
     every exact finite-dimensional projective model of `K` with cocycles tending to 1 rounds
     strictly. So Dogon's Theorem 3.1 mechanism, realized by exact twisted representations,
     produces no instability at any finite-index subgroup of `SL_3(Z)`.
3. **`sl3z-finite-index-z-extension-centres-stay-bounded`** (claim), with route
   **`sl3z-z-extension-centres-bounded-proof`**. Let `K~ -> K` be a central `Z`-extension of a
   finite-index `K <= SL_3(Z)` with finite abelianization.
   - Its class is archimedean (`c_R != 0`), so `b_2(K) > 0`. There is no such extension at level
     one.
   - Every eigenvalue of `ρ(z)`, for every finite-dimensional unitary `ρ`, is a root of unity of
     order at most `C = m·|R(K)|`, where `m` is the divisibility of `c_R` in the integral
     lattice.
   - Centre orders in finite quotients are at most `C`.
   - `K~` has (T), and every model pulled back through `K~` with `||ρ_k(z) - 1||_2 -> 0` rounds
     strictly, since `1 - tr E_k <= ||ρ_k(z) - 1||_2^2 / (4 sin^2(π/C))`.
   - The mechanism: the `ζ`-eigenspace of `ρ(z)` is a projective representation of `K` with class
     `exp_*(θ c_R)`, `ζ = e^(2πiθ)`, whose order is `n/gcd(n, m)` when `θ = b/n` and infinite
     when `θ` is irrational.

## Approaches tried and exactly where each dies

**A. Visible central extension at level one.** Dies immediately.
- `H_2(SL_3(Z); Z)` is finite, so `H^2(SL_3(Z); R) = 0`.
- Every central `Z`-extension of `SL_3(Z)` has torsion class and hence infinite abelianization
  (Item 1 of the bounded-centres route).
- So there is no Kazhdan central `Z`-cover.
- The only scalar classes are the four torsion classes, and exact projective models round.

**B. Dogon Theorem 3.1 / exact twisted representations at finite index.** Dies at Step 4 of the
multiplier route.
- An infinite supply of realizable scalar classes on a finite-index `K` would need
  `H^2_cts(K^, Q/Z)` infinite.
- At primes dividing the level that would need `H^2(sl_3(Q_p), Q_p) != 0`, which Whitehead
  forbids.
- At the other primes it would need `H_2(SL_3(Z))` infinite, which van der Kallen forbids.
- Contrast: the control case `Z_p^2` has `b_2 = 1`, and there the supply is `Q/Z`.

**C. Visible central extension at finite index (the GHB_2(7) and `SL_3(F_q[t])` template).**
Dies at Item 3 of the bounded-centres route.
- A central `Z`-extension with finite abelianization exists only if `b_2(K) > 0`, which is not
  checked here.
- Even then, its centre survives only at orders `<= m·|R(K)|`, and every pulled-back model
  rounds.
- The difference from `GHB_2(7)` and `SL_3(F_q[t])`: those lack a known finite `R(K)`. For
  `SL_3(F_q[t])` the local factors are groups over `F_q[[t]]`, which are not `p`-adic analytic,
  so the Lazard step has no analogue. The graph records large `b_2` there
  (`sl3-polynomial-congruence-subgroups-have-large-b2`).
- Side remark (in the claim's Reading): wherever such an extension exists, degree-two goodness
  (G2) fails for `K`, by contraposition of
  `degree-two-inflation-onto-makes-z-extension-centres-survive`.

**D. Asymptotically projective or non-scalar defects.** Not attacked; this is where the target
now lives.
- The results above only concern models that are *exact* projective representations, or that
  are pulled back from a central `Z`-cover.
- A general asymptotic representation of `SL_3(Z)` need not be either. Dogon's
  weak-ucp-to-flexible-HS equivalence does not reduce to these.
- What would be needed for **stability**: rounding of asymptotic representations whose defect
  is not scalar. For Kazhdan groups this is the question of whether almost-invariant vectors of
  the bimodule representation can be found uniformly. Nothing here addresses it.
- What would be needed for **instability**: a mechanism not based on scalar 2-cocycles. By the
  results above it cannot be a finite-dimensional central-extension template at any finite-index
  subgroup.

**E. Archimedean classes.** Where `b_2(K) > 0`, `exp_*(H^2(K; R))` is an infinite subgroup of
`H^2(K; T)`, and only finitely many of its points are finite-dimensionally realizable.
- Only *asymptotically* realizable classes, with cocycles tending to 1, could matter. By (SF1)
  and rounding they cannot come from exact projective models.
- Whether they give asymptotic representations that do not round is the same open question as D.

## Credit and novelty

- The finiteness mechanism for `R(K)` is the Deligne-style congruence-subgroup-property
  folklore, and it is the graph's own `Sp_4` argument. Only the level-one input and the Lie
  algebra change.
- No claim of novelty beyond recording the `SL_3(Z)` instance and its consequence for central
  covers.

## Weakest steps (for the referee)

1. The Lazard imports (V (2.4.9), and (2.2.2.2)--(2.2.3.2)) are carried over from the source
   check recorded by `sp4-finite-index-multiplier-lazard-whitehead-proof` (2026-09-12); they
   were not re-read this session.
2. `M(G) = H_2(G; Z)` for perfect `G` (Milnor §5), classical and not re-read. Only finiteness of
   `H_2(SL_3(Z); Z)` is load-bearing.
3. Step 0 relies on Malcev's theorem and on the colimit description of continuous cohomology
   (Serre, *Cohomologie galoisienne*); both are classical and not re-read.

## Literature consulted

- W. van der Kallen, *The Schur multipliers of SL(3,Z) and SL(4,Z)*, Math. Ann. 212 (1974),
  47--49, DOI 10.1007/BF01343979. Crossref metadata and the author's scan were fetched
  2026-09-16, and page 47 was read.
- M. Dogon, arXiv:2211.10492v3.
- arXiv:2506.20843v2 (2026-06-23), arXiv:2512.09180v2 (2026-06-08), arXiv:2607.17578,
  arXiv:2408.00110, arXiv:2311.06706: listing and abstract level.
- A. Ioana, P. Spaas, M. Wiersma, arXiv:2006.01874v2, via the graph's records.
- M. Lazard, *Groupes analytiques p-adiques*, Publ. IHES 26 (1965), via the graph record of
  2026-09-12; not re-read.
- Bass--Milnor--Serre (1967), via the graph record; not re-read and not used directly. The
  `SL_3(Z)` congruence input is `sl3z-finite-index-subgroups-are-congruence-subgroups`.
- Soulé, Topology 17 (1978): the fetch returned 403. Not pinned and not used.
