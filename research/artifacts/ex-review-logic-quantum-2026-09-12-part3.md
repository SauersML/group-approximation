# EX review, logic and quantum: part 3. Compression rigidity across metrics (ex-free-unified-theory) and stabilizer rounding (ex-quantum-pcp)

Lane `ex-verify-logic-quantum`, 2026-09-13 01:20 CDT.  Index: `ex-review-logic-quantum-2026-09-12.md`.

## 3.0 Verdicts

| item | verdict |
|---|---|
| `kazhdan-commutant-compression-stability-is-finitary` (+ `-proof`) | PASS: the equivalence was re-derived.  The rows rest on established nodes not re-derived here |
| `leavitt-unit-group-outside-class-iff-compression-stability` (+ `-proof`) | PASS, given the established prerequisites |
| `hs-vertex-rounding-and-liftable-masa-force-normalization` (+ `-proof`) | PASS on Steps 3--4 (the new content); Steps 1, 2, 5, 6 rest on established nodes |
| `pauli-sums-near-their-one-norm-round-to-stabilizer-states` (+ `-proof`) | PASS |
| `pauli-projector-hamiltonians-are-stabilizer-approximable` (+ `-proof`) | PASS |
| `qudit-stabilizer-rounding-for-code-constraint-hamiltonians` (+ `-proof`) | PASS |
| `pauli-norm-games-qpcp-needs-imperfect-completeness` (+ `-proof`) | PASS.  The form of Natarajan--Nirkhe Lemma 6 was taken from the lane's citation and not re-read |
| Citation routes: NLTS (Anshu--Breuckmann--Nirkhe), commuting Hamiltonians on small-set expanders (Aharonov--Eldar), product states (Brandao--Harrow Thm 3, Cors 4, 5, 11), Natarajan--Nirkhe | Not re-read at source here.  Each quotes theorem numbers and says the PDF was read |
| Structural sweep of all landings of the twelve lanes (tip `c1132244e5`) | PASS: no false establishment of a famous root (§3.4) |

## 3.1 The finitary equivalence (UCS_C <=> NORM_C): PASS

Re-derived.

**The lemma.**
- `sigma(Gamma)` centralizes `C = C_U(sigma(Gamma))`.
- `sigma(t) C sigma(t)^-1 = C_U(sigma(t Gamma t^-1)) >= C`, since `t Gamma t^-1 <= Gamma`.
- If `<=` also holds, the two are equal, and `sigma(t)^-1` normalizes too.
- So `sigma(G)` normalizes `C` iff `sigma(t) C sigma(t)^-1 <= C` for every `t in T`.

**NORM => UCS.**
- A failing sequence of `(1/k, k)`-models, together with a free ultrafilter, gives a homomorphism
  `sigma`.
- `F` and `T` are finite, so `s` and `t` can be fixed along the ultrafilter.
- `z = [(z_k)]` commutes with `sigma(F)`, hence with `sigma(Gamma)`.
- Inverses are coordinatewise, so `d(sigma(t) z sigma(t)^-1 sigma(s), ...) >= eta`.

**UCS => NORM.**
- The `R`-ball is finite, so representatives form `(eps,R)`-models almost everywhere.
- The UCS bound `eta/2` passes to the limit and contradicts `eta = max_s d(w sigma(s), sigma(s) w)`.

**Scope.**
- Kazhdan is never used in the equivalence.  It is general for bi-invariant metric model groups.
- The rows use established nodes not re-derived here: `sofic-groups-kill-rigid-compression-defects`
  with `rigid-compression-defect-normalization-dichotomy`, `weak-mf-groups-can-carry-rigid-defects`,
  and `kazhdan-asymptotic-commutant-transport` (whose proof route is `requires: []`).
- In the weak MF row, a nontrivial corona element survives in some ultraproduct, so the corona
  representation does give a failing `sigma`.

## 3.2 The Leavitt pair and the median step: PASS

**Leavitt pair.**
- **2 <=> 3** is §3.1 at the rigid presentation `(F, {u,v})`.
- **2 => 1.**  A faithful `rho` puts `rho(j)` in `C_U(rho(Gamma))`.  Normalization puts
  `rho(u j u^-1)` there too.  Then `rho([u j u^-1, gamma]) = 1`, which contradicts faithfulness.
- **1 => 2.**  A wall makes `sigma` nontrivial.  Simplicity of `R^x` makes it faithful, and
  property (U) gives membership.
- **Prerequisites** (established, not re-derived): property (U) for the four classes,
  `binary-leavitt-unit-group-is-simple`, `leavitt-unit-group-carries-nontrivial-rigid-defect`,
  `openai-nine-leaf-leavitt-configuration`.

**Median step.**
- **Step 3.**
  - `f = sum_A q_A h_(m_A) q_A` commutes with every `q_A`.  By Step 2 it asymptotically commutes
    with `sigma(S)`, so `f in Q`.
  - `W*(C cup {f})` is abelian and lies in `Q`, so maximality of `C` forces `f in C`.
- **Step 4.**
  - Take `c_A >= 1/2`.  The spectral projection of `q_A f q_A` on `(-inf, 1/2]` has mass
    `>= 1/2`, and `|f - c_A| >= c_A - 1/2` on it, so `(c_A - 1/2)^2 <= 2 delta_A^2`.
  - Then `(a+b)^2 <= 2a^2 + 2b^2` gives the factor `6`.
  - Summing over the block-diagonal decomposition gives `||f - 1/2||_2^2 <= 6 ||f - sum c_A q_A||_2^2`.
- **Steps 1, 2, 5, 6** rest on `hs-block-gap-iff-liftable-masa-of-actor-commutant`,
  `hs-rounding-and-actor-gap-force-ccr`, `vertex-rounding-reduces-ccr-to-commutant-excess` and
  `commutant-excess-bounded-by-aspect-ratio-jump-mass`.  All are established; none was re-derived
  here.
- **Open inputs.**  (H1) = `hs-stable-vertex-rounding-for-every-model` and
  (LM) = `actor-commutant-has-liftable-masa-in-every-model` remain open, and the node says so.

## 3.3 Stabilizer rounding: PASS

**(SR), qubits.**
- **Good terms commute.**  Anticommuting signed Paulis satisfy `(A_P + A_Q)^2 = 2I`, so
  `<A_P> + <A_Q> <= sqrt2`.  Two terms above `1/sqrt2` therefore commute.
- **Sign pattern.**  Measure the good terms jointly.  Averaging shows some positive-probability
  pattern `x` has `sum_(G*) w_P (1 - x_P) <= sum_(G*) w_P delta_P`.  Because `E_x != 0`, the
  generated group contains no `-I`.
- **Other terms average to zero.**
  - A term anticommuting with a stabilizer element has expectation `0`.
  - Otherwise its class in `C(A)/A` is nonzero, and the quotient is nondegenerate symplectic, so
    some `R in C(A)` anticommutes with it.
  - `R` permutes the stabilizer states in `E_x` and flips the sign, so the uniform average is `0`.
- **Loss.**  Outside `G*`, `delta >= 1 - 1/sqrt2`, and there `max{0, 1-delta} <= (1+sqrt2) delta`
  (equality at the endpoint).
- **Example.**  For `(X+Z)/2` the ratio is `1/sqrt2`, since stabilizer states have
  `<X> + <Z> <= 1`.

**(PP).**
- `H = (W - K)/2` with `lambda_min(H) = (W - lambda_max(K))/2`, which gives the factor `2+sqrt2`.
- Code-space projectors expand into distinct signed Paulis of total weight `1`.
- Mixed terms: `H_s <= H` and `<H - H_s> <= V`.
- The NP verifier is a stabilizer tableau with exact rational energy (Aaronson--Gottesman).
- The example `(I-X)/2 + (I-Z)/2` gives ratio `1 + 1/sqrt2`.

**(SR_d), prime qudits.**
- `||u psi - psi||^2 = 2 delta`.
- `u_j u_k = omega^m u_k u_j` gives
  `2 sin(pi/d) <= |1 - omega^m| <= 2(sqrt(2 delta_j) + sqrt(2 delta_k))`, so terms with
  `delta < sin^2(pi/d)/8` commute.
- Weyl centralizer averaging uses `E <u_j> = omega^m E <u_j>`.
- `max{0, 1-delta} <= ((1-tau)/tau) delta`, which gives `8/sin^2(pi/d) - 1`.

**(GT1), (GT2).**
- Acceptance is `1/2 + tr(H rho)/(2W)`.
- `F_N > (2+sqrt2) F_Y` gives NP by (SR).
- With weight `<= 1`, `p > (2+sqrt2) q` gives NP.
- The lemma gap `(1 - x/r - e^(-x))/3` at `x = ln r` equals `(1 - (1+ln r)/r)/3 > 0` for `r > 1`.

**Credit.**  The novelty check was not rechecked (this session's web-search budget is exhausted).
Stabilizer and product-state approximation algorithms for Pauli Hamiltonians exist in the
literature, so an `ex-novelty` pass is advised before anything here is called new.

## 3.4 Structural sweep (tip `c1132244e5`)

Script `sweep2.sh` in the lane directory.  For every route landed by the twelve lanes:
- a `requires: []` route: list the claims whose `invalidates:` names it;
- any other route: whether all requires are established.

It also covers every `requires: []` route targeting UGC, quantum PCP, the games qPCP claim and the
two Pi^0_2 amenability/soficity cells.

- **Direct routes into famous roots, all killed by established invalidators.**
  - `qpcp-gap-from-abn-energy-semantics` (`abn-energy-to-fault-loss-is-exponential-in-depth`).
  - `qpcp-gap-from-ordinary-energy-amplification` (`ordinary-gap-amplification-grows-locality`).
  - `ugc-via-bkm-test-on-learnable-hardness` (`bkm-test-transparent-on-learnable-games`).
  - `ugc-via-subexponential-pairing-enrichment` (`separated-small-pairing-families-defeat-the-noise-test`).
  - `games-qpcp-from-tensor-power-amplified-xx-zz` (`natarajan-vidick-games-pcp-amplification-error`).
- **Firing routes.**  Every route whose requires are all established targets a non-famous claim.
- **Roots.**  `non-hyperlinear-group`, `unique-games-conjecture`,
  `amenability-of-finite-presentations-is-pi2-complete`,
  `sofic-recognition-finite-presentations-is-pi2-complete` and
  `qc-isomorphic-not-qa-isomorphic-graph-pair-exists` all say OPEN.
  `quantum-pcp-constant-gap-local-hamiltonian` has no live direct route.
- **One prose note.**  `global-walk-reducer-has-net-energy-gain` states a claim without a status word.
  It is a pre-existing open target from a peer campaign, not a landing of these lanes.
