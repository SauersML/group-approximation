# Swarm attack on `projective-commutant-transfer-for-arithmetic-pair` (2026-09-16)

Agent: `swarm-projective-commutant-transfer-`. Hole locked and worked:
`projective-commutant-transfer-for-arithmetic-pair` (PRCC, OPEN, no incoming
routes). Lock acquired with TTL 180m and released at the end.

## 1. Setup

- PRCC asks, for `(Lambda,Gamma)=(SL_n(Z),SL_n(Z[1/p]))`, a finite
  generating set `S` of `Lambda`, `h` outside `Lambda` and a fixed finite
  presentation of `Gamma`, for `K` and `eta(delta)->0` with
  `e(U,rho(h)) <= K sum_(c in S) e(U,rho(c)) + eta(delta)`, where
  `e(U,V)=1-|tr[U,V]|^2`.
- Established before today, and relevant:
  - `projective-transfer-linear-bound-equals-no-ultraproduct-leak`: a
    linear bound `e<=L(q+delta)` exists iff there is no leak sequence
    (`delta->0`, `q->0`, `liminf e>0`). Its body warns of a
    *trace-profile gap*: the HNN route supplies only regular-trace
    microstates.
  - `arithmetic-hnn-nonhyperlinearity-equals-global-collapse`: for every
    `n>=2` and prime `p`, nonhyperlinearity of `H=A *_C (C x Z)` is
    equivalent to regular-trace RCC (and four other assertions). The
    dimension-free inequality is added **only for `n>=3`** and one
    diagonal `h`.
  - `rf-perfect-pair-transfer-equals-regular-rcc`: linear bound iff
    regular RCC, but only for residually finite **perfect** pairs, so
    rank two is excluded (`SL_2(Z)^ab=Z/12`).
  - `kazhdan-rcc-has-prescribed-projective-transfer-slope`: needs `(T)`
    of the subgroup, so again not rank two.
  - PRCC's own body (the 2026-08-21 "How much of the projective slack is
    real" item) says that for `n=2` "the twisted enemies are characters of
    the finitely many `mu_12`-twisted carriers", as if they were separate
    obstructions.

## 2. What was proved (new nodes)

### 2a. `adjoint-regular-rcc-gives-projective-transfer` (claim), route `adjoint-regular-rcc-projective-transfer-proof`

For finitely presented **hyperlinear** `A=<X|R>`, `C=<S>`, `A=<C,h>`, the
following are equivalent:

- (AR1) regular-trace RCC in matrix ultraproducts;
- (AR2) a linear bound `e_h<=L(q+delta)` over all assignments;
- (AR3) RCC for every trace profile.

No perfectness, residual finiteness or spectral gap is needed. The proof
has three steps.

1. **Regularize.** Take a leak sequence from the linearization theorem.
   Tensor the tuple with canonical microstates `sigma_n` of `A` and the
   witness with `I`. Commutator traces are unchanged, defects add, and
   traces become canonical.
2. **Adjoint.** Replace the tuple by `Ad(rho~)` and the witness by
   `Ad(U~)`. By `||Ad W-I||_2^2=2-2|tr W|^2`, source phases vanish and
   the ordinary commutator energy is twice the projective one. The trace
   stays regular, since `tr Ad V=|tr V|^2`.
3. **RCC.** The ultraproduct witness is `C`-central, so RCC forces
   commutation with `h`, a contradiction.

Converse, for any finitely presented `A`: double the tuple, `rho+rho`,
and the witness, `u+I`. Then `tr(W+I)=(1+tr W)/2`, and energy
`<=eps` forces `||W-I||_2^2<=4eps`. So an honest commutant unitary
commutes with `h`. The Kazhdan route used both tricks, but around a
`(T)` projection; here they are joined to the linearization theorem
instead.

### 2b. `rank-two-projective-transfer-equals-hnn-nonhyperlinearity` (claim), route `rank-two-projective-transfer-hnn-proof`

For every prime `p`, with `C=SL_2(Z)` and `A=SL_2(Z[1/p])`, and for any
finite presentation, any generating words and any `h` in `A` minus `C`,
the following are all equivalent:

- nonhyperlinearity of `H`;
- regular RCC;
- unrestricted RCC;
- the linear inequality `(R2T1)`;
- the PRCC form `(R2T2)` with a qualitative modulus.

Inputs:

- finite presentation (Ihara amalgam);
- residual finiteness (reduction mod `l!=p`), hence hyperlinearity;
- Smith maximality `(SPL1)`;
- the HNN theorem with `n=2`;
- the linearization theorem.

Consequences:

- **Twisted leaks.** PRCC's `mu_12`-twisted enemies are not additional
  obstructions in rank two. A twisted projective leak becomes an
  untwisted regular-trace leak via `Ad`, and so makes `H` hyperlinear.
  The body text of PRCC should be read with this correction; I did not
  edit it.
- **Rank two, any prime.** PRCC is exactly nonhyperlinearity of the
  explicit finitely presented group `H_(2,p)`. Its truth value does not
  depend on `h`, `S` or the presentation. For `p=2` it is equivalent to
  `relative-commutant-collapse-for-sl2-pair`. So PRCC's `distinct_from`
  entry against that node ("this demands only that it become SCALAR")
  describes a difference in formulation, not in truth value.
- **Higher rank.** The same route applies verbatim to `n>=3` and every
  `h` outside `SL_n(Z)`. That extends the diagonal-`h` clause of the HNN
  node. I did not add this as a claim because it needs a citation for
  finite presentability of `SL_n(Z[1/p])`, and it adds nothing to the
  truth value there.

## 3. Where approaches die

- **Proving PRCC itself.** In rank two it is now literally equivalent to
  nonhyperlinearity of `H_(2,p)`, an explicit finitely presented group. A
  proof would give the first explicit non-hyperlinear group. That is at
  the level of the program's root goal, and I made no attempt beyond
  recording the equivalence.
- **Refuting PRCC** needs a hyperlinear approximation of `H`, or
  equivalently matricial models of the regular HNN leak. The graph already
  records that finite Hecke and Bernoulli models omit the denominator
  relations. I found nothing new there.
- **Two duplicate candidates were abandoned earlier in this session.** Both
  were already on the graph:
  - a camouflage equivalence (residual-finite tensor camouflage; see
    `rf-perfect-pair-transfer-equals-regular-rcc`);
  - a non-treeability observation.
- **Perfectness-based phase removal** is exactly what fails in rank two.
  The adjoint and doubling tricks replace it, but only qualitatively, via
  the linearization compactness. No effective `L` is produced.
- **Kazhdan projection** is unavailable for `SL_2(Z)`. The
  `(tau)`-strength exact result
  `sl2-exact-projective-transfer-via-doubled-squeeze` handles exact
  representations only. The approximate outlier sector is exactly the
  open common assertion.

## 4. Literature gate (2026-09-16)

- Dogon--Vigdorovich, *Hyperlinearity, stability and asymptotic spectral
  gap of higher rank lattices*, arXiv:2506.20843. v1 is dated 25 Jun 2025
  and v2 23 Jun 2026; the abstract page was fetched today. It relates
  flexible HS stability of `SL_2(Z[1/p])` to non-hyperlinear central
  extensions and poses the Iwahori question. It does not decide regular
  RCC or PRCC.
- Alekseev--Bradford, *Sofic actions, halo products, and metric
  approximations of groups*, arXiv:2601.18742 (26 Jan 2026; abstract page
  fetched). It covers closure of hyperlinear and sofic classes under
  semidirect products with sofic actions. It is not directly relevant to
  HNN extensions over `SL_2(Z)`.
- arXiv title search "hyperlinear", newest first, fetched today. The only
  2024--2026 hits were 2506.20843 and 2504.10988 (Kahl--Schneider,
  *Hyperlinearity via amenable near representations*, 15 Apr 2025); only
  titles were seen. Neither concerns arithmetic HNN extensions.
- arXiv title search "Connes embeddable", fetched today. The 2024--2026
  hits were 2502.06697 (Manzoor, 10 Feb 2025, an equivalence relation
  with non-Connes-embeddable von Neumann algebra) and 2411.15070
  (coarse Baum--Connes). Neither is relevant to this pair.
- Abstract searches with several keywords ("hyperlinear HNN extension",
  "hyperlinear stability commutant", "Hilbert-Schmidt stability SL_2")
  returned no results. The arXiv API query was rate-limited (HTTP 429),
  so the search is not exhaustive.
- Gelander--Meiri, arXiv:1511.05767, Section 7, as cited in the
  established Smith node; not re-fetched.
- Serre, *Trees*, Chapter II (Ihara's amalgam for `SL_2(Z[1/p])`): a
  standard reference, cited from memory without a theorem number and not
  fetched. Unverified in this session.

No 2024--2026 source found decides nonhyperlinearity of `H_(2,p)`, regular
RCC for the rank-two pair, or PRCC.

## 5. Files

- `research/adjoint-regular-rcc-gives-projective-transfer.md`
- `research/adjoint-regular-rcc-projective-transfer-proof.md`
- `research/rank-two-projective-transfer-equals-hnn-nonhyperlinearity.md`
- `research/rank-two-projective-transfer-hnn-proof.md`
- `research/artifacts/adjoint-regular-rcc-projective-transfer-2026-09-16.md`
- `experiments/projective-commutant-transfer-for-arithm-2026-09-16/verify_adjoint_identities.py`
  and `output.txt`. The script checks the adjoint, tensor and doubling
  identities numerically, plus a 12x12 clock/shift twisted pair whose
  adjoint commutator vanishes. It prints ALL OK.

## Referee (2026-09-16)

Checked, adversarially:

- **General route** `adjoint-regular-rcc-projective-transfer-proof`.
  Recomputed `(AP1)`, `(AP3)` (uses `|tr V|>=|Re tr V|` and `1+x<=2`),
  `(AP5)` (the identity `1-|1+t|^2/4-(1-Re t)=-|1-t|^2/4`), `(AP6)`
  (`|1+t|^2<=2+2Re t`) and `(AP8)` by hand.  Step 1 regularization: the
  microstate trace bound `|tr(rho(w)) tr(sigma(w))|<=|tr sigma(w)|` and the
  commutator identity `[U tensor I, V tensor Z]=[U,V] tensor I` are correct;
  the passage from almost-multiplicative maps to presentation assignments
  (via `phi(1)~I`, `phi(x^-1)~phi(x)^*`) is correct.  The only external
  input is the standard equivalence "hyperlinear iff there are asymptotically
  multiplicative unitary maps with `tr phi(g)->0` for `g!=1`"; in the rank-two
  application the route instead supplies zero-defect regular representations
  of finite congruence quotients, so nothing unverified is consumed there.
  The leak sequence from `(PL2)<=>(PL3)` of the established linearization node
  matches `(AP7)` exactly.  `(AR2)=>(AR3)`: the doubling bookkeeping, the
  generation step and "a von Neumann algebra is spanned by its unitaries" are
  correct.  No perfectness, (T) or residual finiteness is used.  Sound.
- **Rank-two route.**  Smith `(SPL1)` is stated for `n>=2`, every prime and
  every `g in A\C` (established).  The HNN node is established and covers
  `n=2`.  Matching assertion 2 (canonical `L(A)` embeddings) with
  regular-trace representations is standard and correct.  The
  qualitative-modulus step (`(R2T2)` excludes `(PL3)`) is correct, and
  `(R2T2)` is literally the `n=2` instance of `(PRT1)`.  Residual finiteness
  via reduction mod `l!=p` is correct.
- **Citation.**  Ihara's amalgam was cited from memory.  I could not fetch
  Serre's *Trees* this session either (web search budget exhausted, search
  pages blocked), so it remains unverified as a citation.  I added to the
  route a short Bass--Serre derivation from the standard facts that
  `SL_2(Q_p)` acts on its tree with an edge as fundamental domain and that
  `SL_2(Z[1/p])` is dense in `SL_2(Q_p)`; I rechecked the stabilizer
  computation `SL_2(Z) cap d SL_2(Z) d^-1=Gamma_0(p)`, `d=diag(1,p)`.
- **Duplicates.**  Compared with `rf-perfect-pair-transfer-equals-regular-rcc`
  (needs perfectness), `kazhdan-rcc-has-prescribed-projective-transfer-slope`
  (needs (T) of the subgroup, so not rank two),
  `projective-transfer-linear-bound-equals-no-ultraproduct-leak` (leaves the
  trace-profile gap) and `arithmetic-hnn-nonhyperlinearity-equals-global-collapse`
  (matrix inequality only for `n>=3`, diagonal `h`).  The new claims are
  genuine generalizations; the `distinct_from` entries are accurate.  The
  unlisted in-flight files `anti-central-swap-*` belong to another solver.
- **Numerics.**  Reran the script single-threaded; output is byte-identical
  to `output.txt`.
- **Status honesty.**  No route into the open target is added; the target
  stays OPEN and nothing decides the common truth value.

Changed: only the Bass--Serre paragraph in
`research/rank-two-projective-transfer-hnn-proof.md` and this section.

Verdict: sound; landed with a small fix (self-contained justification of
finite presentability).
