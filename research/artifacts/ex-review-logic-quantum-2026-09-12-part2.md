# EX review, logic and quantum: part 2. The quantum symmetry rung (ex-nh-mipstar) and Galois unique games (ex-ugc, ex-ugc-rounding-pgroups)

Lane `ex-verify-logic-quantum`, 2026-09-13 01:00 CDT.  Index: `ex-review-logic-quantum-2026-09-12.md`.

## 2.0 Verdicts

| item | verdict |
|---|---|
| `qc-qa-graph-gap-gives-non-ce-quantum-automorphism-group` (+ `-proof`) | PASS |
| `lcs-tracial-nonru-gap-gives-qc-qa-cfi-graph-gap` (+ `-proof`) | PASS.  One import not re-read: (P1), synchronous algebra = BCS algebra |
| `closure-safe-support-is-exactly-the-colored-iso-rung` (+ `-proof`) | PASS |
| `colored-cfi-rung-is-the-solution-group-case` (+ `-citation`) | PASS; the quotes match the source |
| `non-ce-quantum-automorphism-group-of-finite-graph-exists`, `qc-isomorphic-not-qa-isomorphic-graph-pair-exists` | OPEN.  Their routes require open claims, so nothing fires |
| `unique-games-hard-at-completeness-one-half` (+ `-proof`), `two-to-two-games-theorem` (+ `-citation`) | PASS; the citation matches ECCC TR18-006 p. 2 |
| `galois-unique-game-value-is-transversal-expansion` (+ `-proof`) | PASS |
| `elementary-abelian-galois-games-round-with-linear-loss` (+ `-proof`) | PASS, with one wording note on `C_2` |
| `galois-games-round-through-free-subgroups` (+ `-proof`) | PASS: parts 1--5 re-derived |
| `free-subgroup-rounding-fails-for-non-normal-fibres` (+ `-proof`), refuting `free-subgroup-rounding-is-universal-at-bounded-exponent` | PASS |
| `sos-cannot-refute-unique-games-at-completeness-one-half` | OPEN with Attempts and no route, so it is not an establishment.  Its crux (i), whether completeness follows from the 3-XOR equations by low-degree identities, is still open and queued |

**Sources read at source** (PDFs fetched on MSI):
- BCEHPSW, arXiv:1812.11474v2, pp. 3--7 and 17--31;
- Roberson--Schmidt, arXiv:2111.12362v1, pp. 4--6 and 22--25;
- Khot--Minzer--Safra, ECCC TR18-006, pp. 1--3.

## 2.1 The rung theorem: PASS

Steps 1--7 re-derived.
- **(S1) and Schur closure.**
  - `(=>)`: multiply on the left by `v_(xa)` and on the right by `v_(x'a')`.
  - `(<=)`: expand `v_(x'a')` by the row `x`, then sum over `x'`.
  - Entrywise products act on scalars only.
- **Sizes and components.**  Summing all entries gives `|X| 1 = |Y| 1`.  If `X` is connected and
  `Y` has `c` components, then `c 1 = 1`, so `c = 1` in a nonzero algebra.
- **(S2).**
  - In the `(X,X)` block, `U R = R U` with `R = J_X (+) J_Y` reads
    `sum_(c in X) u_(xc) = sum_(c in X) u_(cx')`.  The left side depends only on `x` and the right
    only on `x'`, so both equal a constant `1 - P`.
  - The other identities follow from row and column sums.
  - Every `u_(cd)` lies below `P` or below `1 - P`, so `P` is central.
- **`P != 0`.**  `U' = [[0,V],[V^t,0]]`.  Transposing `A_X V = V A_Y` entrywise is legitimate
  because the adjacency matrices are scalar.
- **`h(P) = 1/2`.**  From `(id (x) h) Delta(P) = (1-P) h(P) + P h(1-P)` and `P != 0`.
- **Conclusion.**
  - The corner block is a magic unitary, and `2 h o psi` is tracial by Kac type.
  - `q R^U q ≅ R^U` for `tau(q) = 1/2`.
  - Composing gives a unital `A(Iso(X,Y)) -> R^U`.

**Citations checked at source.**
- Thm 2.1(3),(4), p. 7: perfect `qa` iff a unital *-hom into an ultrapower of `R`; perfect `qc` iff
  a unital *-hom into a C*-algebra with faithful trace.
- Remark 4.3, p. 19: `O(G_Y,G_X) = A(Iso(Y,X))` for classical graphs, with `(1 (x) A_Y) p = p (1 (x) A_X)`.
  The node's `A_X V = V A_Y` is the transposed indexing.
- Thm 4.9, p. 22: `≅_(A*)`, `≅_qc` and `≅_(C*)` coincide for classical graphs.
- Thm 4.7 (p. 22) and Thm 3.15(1),(3) with Example 3.14 (p. 17): bi-invariant states are unique and
  faithful, and tracial iff Kac.

**Notes.**
- The planar-count corollary rests on Mančinska--Roberson, read from abstracts only; the node says
  so.
- The attribution "LMR Thm 4.4: `≅_q` iff `≅_qc`" uses LMR's C*-notion of quantum isomorphism.  It
  was not re-read here, and nothing depends on it.
- Credit: the corner construction is LMR's.  The additions are `h(P) = 1/2` and the
  non-embeddability conclusion.  The novelty check was not rechecked, since this session's
  web-search budget is exhausted.

## 2.2 Linear-system graphs: PASS

- **Definitions and theorems.**
  - Def 5.5 (p. 28) matches the node's graph `G_(A,b)`.
  - Thm 5.6 (p. 28): `syncBCS(A,b)`, `Iso(G_(A,b), G_(A,0))` and `Hom(K_m, complement of G_(A,b))`
    are hereditarily *-equivalent.
  - Prop 5.3 (p. 27) transfers perfect strategies for `t in {loc, q, qa, qc, C^*}`.
  - Remark 5.9 (p. 31) withdraws plain *-equivalence.  The node correctly uses the hereditary form.
- **Transfer.**  A tracial state gives, through GNS, a faithful-trace target, and a faithful trace
  pulls back to a tracial state.  The `R^U` case is direct.
- **The one import not re-read.**  (P1), synchronous algebra of `syncBCS` = BCS algebra, taken from
  Paddock--Slofstra p. 2 (Kim--Paulsen--Schafhauser, Goldberg).

## 2.3 Closure-safe support: PASS

- (P0) holds by traciality: `tau(pq) = tau(qpq) = |pq|_2^2`.  (P1) holds under a faithful trace.
  (P2) holds by taking adjoints.
- **CS1 => CS2.**
  - Colours are support components.  Diagonal reservation comes from row orthogonality and
    injectivity.
  - Degree-zero answer pairs get fresh colours.
  - `qc` follows through GNS.  "Not `qa`" follows because closure safety makes `lambda = 0` pairs
    differently coloured.
- **CS2 => CS1.**  Colour equality is the rule.  Column sums are forced in `R^U` by (P1).
- **Colored union.**
  - The cross colour gives `R = J_X (+) J_Y` directly, with no connectivity step.
  - `U'` respects all colours.
  - `Qut` of a colored digraph is Kac because `S(u_(ij)) = u_(ji)`.

## 2.4 Colored CFI graphs: PASS

At source, Roberson--Schmidt:
- **Defs 3.1--3.2 (p. 4).**  `Gamma(M,b)` is defined for `b != 0`, and `Gamma_0(M)` separately.
- **Thm 3.8 (p. 6)**, quoted verbatim in the route.
- **Def 6.3 (p. 24).**  `Iso(G,G')` is the universal C*-algebra with relations (18)--(21).
- **Prop 6.4, with footnote 3 (p. 23).**  Commuting-operator strategies.
- **Def 6.5.**  `A(M,b) ≅ p C^*(Gamma(M,b))` for `b != 0`.
- **Thm 6.7 (p. 24).**  For `b != b'`, `A(M,b+b') ≅ Iso(G(M,b), G(M,b'))`.

The consequences with `b' = 0` and `b != 0` follow.  Tracial states and `R^U` models of the universal
C*-algebra are those of the *-algebra, because the generators are bounded.

## 2.5 Unique games at completeness one half: PASS

- **Citation.**  ECCC TR18-006 p. 2, Def 1.3 and Thm 1.4 verbatim: "For every constant `ε > 0`, there
  exists a sufficiently large integer `l = l(ε)` such that Gap 2-to-2`[F_2^l](1-ε, ε)` is NP-hard."
- **Splitting.**  A satisfied 2-to-2 constraint satisfies one branch if `b != b'` and both if `b = b'`.
  So `val/2 <= val' <= val`, which gives `Gap-UG((1-ε)/2, ε)`.
- **Credit.**  This is a standard two-line consequence.  KMS pp. 1--3 do not state it, and the later
  pages were not read.  Treat it as folklore, not as new.

## 2.6 Galois unique games: PASS

**Value, perfect case, SDP.**
- **Transversal bijection.**  Satisfaction iff `s t_v in T_f`.
- **Freeness.**  `Stab(gK) = g K g^-1`.  An invariant transversal is one right coset `Lambda g_O` per
  orbit.
- **SDP `(>=)`.**  `u_(v,a) = k^(-1/2) pi(tau(v) a) xi`, with orthogonality from `phi|_(K\e) = 0`.
- **SDP `(<=)`.**  Left translates of a feasible Gram matrix keep the objective, by conjugation
  invariance.  Their average is `phi(y^-1 y')/k`.  The basic SDP has no nonnegativity constraints.
- **Folded tests.**  `x - f(x) 1` is uniform on `T_f`.

**Elementary abelian, linear loss.**
- Bochner and Fourier inversion on `K`.
- Markov at `η = 2pε/(p-1)` leaves high mass `(p+1)/(2p) > 1/p`, so the high restrictions span
  `Khat`.
- The common kernel is a complement, with cost `<= r η/(1 - cos(2π/p))`.
- The greedy minimum-weight basis of the restriction matroid gives the SDP-free algorithm.
- **KV tightness.**  `Pr[t+s in T] = N Stab_ρ(1_T) <= N^(1 - 2/(1+ρ)) = 2^(-t/(1-ε))`.
- **Cycle.**  `1/n >= (2/π) sin(π/2n)`.
- **Wording note.**  The formula `C_p` gives `2` at `p = 2`.  The stated `C_2 = 3/2` comes from
  `η = 3ε`: for `p = 2`, any `η > 2ε` works.  This is not a defect.

**Free subgroups.**
- **Duality.**  `Stab_K(yH) = K cap y H y^-1`.
- **Rounding.**  `T = {g : g^-1 H in D}` is a transversal, and `s in H` fixes `g^-1 H`.
- **Kernels.**
  - Isotypic weights with Schur give `sum w_ρ (1 - λ_ρ) <= ε`.
  - On the good kernels, `Re phi >= 2/3 - 1/3`.
  - A halving chain needs `<= log_2 k` representations.
  - Hilbert--Schmidt Markov bounds `Pr[ρ(s) != I]`.
- **Part 5.**  For conjugation-invariant `mu`, `Pr[st in T] = Pr[ts in T]`.  `T = ⊔ g_j L`, one left
  `L`-coset per left `KL`-coset, is a transversal closed under right multiplication by `L`.

**The refutation.**
- The exponent is `4`: `(b,t)^2 in B`.
- `mu_δ` is conjugation-invariant, since `B` is abelian and translations preserve weight.
- `L = {b_0 = 0}` gives `SDP, val >= 1 - δ` by part 5.
- A free `H` omits every `e_j`.
- `N (1 - N^-2)^(N-1) > N - 1` while `ε log_2 k = N^-2`.

## 2.7 Queued

- **ex-ugc-rounding-pgroups.**
  - `normal-fibre-galois-games-round-linearly-over-all-groups` imports
    `primitive-projective-representations-have-a-trace-gap`, with a CFSG-uniform `gamma(G) < 1`.
    This import has priority.
  - Also `-over-m-groups`, `free-rounding-pays-the-number-of-fibre-conjugates` and
    `abelian-normal-closure-fibres-round-linearly`.
- **Other lanes.**  ex-free-unified-theory, ex-quantum-pcp, ex-complexity-amenable, and the
  complexity-sofic amplifier.
- **SoS crux (i).**
