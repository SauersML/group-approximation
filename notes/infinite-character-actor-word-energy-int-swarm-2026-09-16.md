# Swarm notes: infinite-character-actor-word-energy-interface (2026-09-16)

Hole: `infinite-character-actor-word-energy-interface`. Outcome: **obstruction**. The terminal output of any such
interface is seed radical membership. For the SL3 codense lamp host, that is equivalent to a fixed-algebra rigidity
statement for all Connes-embeddable actions, and the open hypothesis `(SH1)` refutes it.

Long proofs: `research/artifacts/seed-radical-transfer-2026-09-16.md`.

## Setup

- The central D8 seed is `P(G,b) = <G, z, J | z^2 = J^2 = 1, J central, [b,z] = J>`, which is
  `(G x <J>) *_(<b,J>) D_8`.
- `infinite-character-interface-is-marked-radical-certificate` (ESTABLISHED) shows that a uniform interface for a
  packet `(M rtimes A, m_0)` gives the finite-window estimate `(ICR2)`. That estimate says `J in Rad_hyp(P)`.
- So the question is: **when is `J in Rad_hyp(P(M rtimes A, m_0))`?** Any interface proof must at least prove this for
  its packet.

## What was proven (new nodes)

1. **`central-d8-mark-radical-equals-seed-radical`**, direct route `central-d8-mark-radical-proof`.
   - `J in Rad_hyp(P(G,b))` iff `b in Rad_hyp(G)`, for every countable `G`.
   - Direction 1 is the easy one. Direction 2 builds an explicit ultraproduct homomorphism with `J -> -1`.
   - Construction: shift the seed trace to `(1+t)/2` and take tensor powers; make a diagonal choice; round with sign;
     rebalance to trace zero; then adjoin the swap.
   - Consequence: the interface's terminal output is equivalent to `m_0 in Rad_hyp(M rtimes A)`.
2. **`semidirect-seed-radical-is-ce-dual-measure-test`**, direct route `semidirect-seed-radical-dual-measure-proof`.
   - For hyperlinear `A`: `m_0 notin Rad_hyp(M rtimes A)` iff some `A`-invariant measure on `M^` that charges
     `{chi(m_0) != 1}` has a Connes-embeddable crossed product.
   - No novelty is claimed.
3. **`coset-lamp-seed-radical-is-ce-fixed-algebra-rigidity`**, route requiring nodes 1 and 2.
   - For a coset lamp `L = directSum_(A/C) F_2` and `m_a = delta_C + delta_(aC)`:
     `m_a in Rad_hyp` iff every Connes-embeddable p.m.p. action has `L^infinity(Z)^C <= L^infinity(Z)^(<C,a>)`.
   - Also proved: index-two with an involution gives `Rad_hyp(H) = Rad_hyp(G) cap H`. This settles the augmentation
     variant `L_0`.
   - Profinite actions never separate under finite-quotient codensity (Remark C4).
4. **`homogeneous-quotient-ce-frees-sl3-lamp-seed`**, route requiring node 3, node 1,
   `homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse` and `hyperlinear-radical-presentation-compactness`.
   - `(SH1)` implies that `m_h` escapes the radical of both `L rtimes A` and `L_0 rtimes A`.
   - It also implies `J notin Rad_hyp(P_host)`, and every finite window admits tuples with defect `< delta` and
     `||J(U) - I||_2 > 2 - delta`.
   - Unconditionally, the interface for this host implies `L^infinity(Z)^C = L^infinity(Z)^A` for every
     Connes-embeddable action. So it implies that `(SH1)` fails for every torsion-free cocompact `Lambda'` with
     `r >= 2`.
   - `<C,h> = A` is checked through conjugated elementary matrices and the Euclidean property of `Z[1/2]`.

## Approaches considered and where they stop

- **Decide `(SH1)`.** Not attempted beyond reading. `M` is a II_1 factor of a non-amenable, essentially free,
  non-profinite action with property (T) actor. No permanence theorem covers it, and the node stays open.
- **Hyperlinearity of `L rtimes A` by permanence.** No abelian-by-residually-finite permanence exists for soficity.
  Kun--Thom (arXiv:2608.06222) exhibit nonsofic binary coset wreaths over residually finite groups. Hyperlinearity of
  the base would itself refute the interface for this host, because `infinite-character-interface-is-marked-radical-certificate`
  shows the interface makes the base nonhyperlinear. But that hyperlinearity is not available.
- **Algebraic dual models.** Haar measure on a closed invariant subgroup of `F_2^X` is the dual of a quotient module
  `L/N`. Its crossed product is the group factor `L((L/N) rtimes A)`, so nothing is gained. Finite quotient modules
  kill `m_0`: `A` acts on `L/N` through a finite quotient where `C` and `A` have the same image, so
  `delta_(x_0) = delta_(h x_0)` mod `N`.
- **Linear lamp groups** (for example, affine groups over `F_2[t^(+-1)]`). They are residually finite, so their seeds
  are visible in finite quotients. They satisfy the dual-measure test trivially but are not codense coset-lamp
  packets, so they say nothing about the SL3 host.
- **Soficity of the coset action** (`sl3-dyadic-building-vertex-action-is-sofic`, OPEN). This is open. If a sofic
  action made the binary coset wreath sofic, the lamp base would be hyperlinear and the interface refuted. I did not
  check that transfer against a source, so it is marked unverified.
- **Profinite actions.** They are excluded by codensity (Remark C4): conditional expectations onto finite levels are
  equivariant, and `C`-invariant functions on finite `A`-sets are `A`-invariant.
- **Mackey duality for the homogeneous quotient.** `A` is dense and not closed in `SL_3(Q_2)`, so there is no Morita
  dual action of `Lambda'` on a standard quotient `A \ SL_3(Q_2)`. This does not reduce `(SH1)` to a lattice action.
- **Kun--Thom analogy.**
  - For the Kun--Thom pair the sofic radical is the fibre-even kernel `K_even`
    (`kun-thom-wreath-sofic-radical-is-fibre-parity-kernel`).
  - For the SL3 pair the normal closure of `C` is `A`, so the analogue of `K_even` is `L_0`, which contains `m_h`.
    The analogue would therefore predict `m_h in Rad`, which is consistent with the interface.
  - The Kun--Thom mechanism needs an infranormal compression pair. `SL_3(Z)` is not infranormal in `SL_3(Z[1/2])`:
    if `g C g^(-1) <= C`, then the vertex stabilizer of `g v_0` fixes `v_0`, which forces `g v_0 = v_0`. So the
    analogy does not transfer.
- **S-arithmetic candidate (unanalyzed).** Diagonal `A` acting on `(SL_3(R) x SL_3(Q_2)) / Lambda''` for a lattice
  `Lambda''`. Here `C` is a lattice in `SL_3(R) x K`. Whether there are `C`-invariant sets moved by `h`, and whether
  the crossed product is Connes embeddable, is not analyzed. The expected ergodicity input (Moore) was not checked
  against a source.

## For the referee

- Direct proofs with `requires: []`: `central-d8-mark-radical-proof` and `semidirect-seed-radical-dual-measure-proof`.
  Their standard ingredients F1--F7 are proved in Section 0 of the artifact.
- Attack first:
  - the diagonal tensor product and GNS extension in (B2), F4/F7;
  - the measurability and equivariance of `Phi` in (C1);
  - the use of HQ clause 3 in (D1), which Section 4 of the artifact rechecks independently.
- Suggestion, not done: `sl3-homogeneous-quotient-crossed-product-is-connes-embeddable` could add
  `sl3-codense-lamp-higman-route` to its `invalidates` list. Under `(SH1)` its interface requirement fails for that
  host. I did not edit the committed node.
- Not claimed:
  - `(SH1)` is not decided;
  - hyperlinearity of `P_host` is not decided;
  - `(ISC3)` and `(ICR1)` are untouched;
  - the sharply two-transitive host is not decided;
  - no sofic analogue is proved.

## Literature (fetched 2026-09-16 unless marked)

- G. Kun, A. Thom, "Nonsofic wreath products of residually finite groups", arXiv:2608.06222 (v1 6 Aug 2026, v3
  20 Aug 2026). Abstract page fetched. Theorem-level content is used only through repo nodes.
- F. Fournier-Facio, "A torsion-free non-sofic group", arXiv:2608.02025 (v1 3 Aug 2026, v2 14 Aug 2026). Abstract
  page fetched, not used in proofs.
- A. Dogon, I. Vigdorovich, "Hyperlinearity, stability and asymptotic spectral gap of higher rank lattices",
  arXiv:2506.20843 (v1 25 Jun 2025, v2 23 Jun 2026). Abstract page fetched, not used in proofs.
- A. Dogon, "Flexible Hilbert-Schmidt stability versus hyperlinearity for property (T) groups", arXiv:2211.10492
  (v3 25 Aug 2023). Abstract page fetched, not used in proofs.
- G. Elek, E. Szabó, "On sofic groups", arXiv:math/0305352 (25 May 2003). Abstract page fetched, not used in proofs.
- V. Capraro, M. Lupini, "Introduction to Sofic and Hyperlinear groups and Connes' embedding conjecture",
  arXiv:1309.2034 (v6 5 May 2015). Abstract page fetched, used for background conventions only.
- arXiv:2401.04945 and arXiv:1002.0605. Cited only through repo-verified artifacts, not refetched here.
- arXiv:2212.06020. Cited only through a repo node, not refetched here.
- No published source for the dual-measure test (Lemma B) was located. It is written out in full, with no novelty
  claimed.

## Referee (2026-09-16)

**Checked.**

- Read all nine research files and the artifact in full, plus the nodes they consume:
  `infinite-character-actor-word-energy-interface`, `infinite-character-interface-is-marked-radical-certificate`,
  `hyperlinear-radical-presentation-compactness`, `central-d8-seed-preserves-hyperlinearity` (and its proof),
  `homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse`,
  `sl3-homogeneous-quotient-crossed-product-is-connes-embeddable`, `sl3-codense-coset-lamp-recursive-host`,
  `sl3-codense-lamp-higman-route`, `corona-finite-index-radical-heredity`, `hyperlinear-elementwise-visibility`.
  The required nodes are ESTABLISHED.
- **Lemma A** (direct route), line by line. Checked:
  - the trace shift `(1+t)/2`, and the tensor-power defect and trace bounds (F1, with `|x^k - s^k| <= k|x-s|`);
  - that `D_k` is even;
  - the rounding inequality `|lambda - sgn lambda| <= |lambda^2 - 1|`, also checked numerically on a fine grid;
  - the rebalancing identity `||B_k - B'_k||_2^2 = 2|tr B_k|`;
  - the exact identity `B Z B Z = -I`, also checked numerically.
  Sound. No finite generation, amenability or separability is hidden, and countability is used only for the
  diagonal choice.
- **Lemma B** (direct route). Checked:
  - F3: Gelfand/Riesz, and uniqueness via Stone--Weierstrass;
  - F4: well-definedness of `Phi` uses faithfulness of `tau_2`; the unitary `T` and the bicommutant step;
  - F6: Hahn--Banach weak`*` density;
  - F7: the trivial-summand trick with `c_i < 1`, the `k^2`-fold tensor product and the `1/k^3` choice;
  - Step 1: invariance of `nu`;
  - Step 2: the tensor defect `<= 2/l` and the trace `delta_(a,1) phi(m)`;
  - Step 4: the generation of `N_nu`.
  Sound and complete for `requires: []`. No novelty is claimed, which is appropriate.
- **Proposition C.**
  - (C1): exact `C`-invariance of `E'`, well-definedness and equivariance of `Phi`, and the lamp covariance. The
    homomorphism `(l,d) -> F_l u_d` was verified by brute force for `A = S_3`, `C = Stab(0)`, `Z = A`, using the
    artifact's conventions.
  - (C2): the dual shift intertwining.
  - (C3): the index-two involution doubling. All four product cases were verified numerically for `A_3 < S_3`.
  - The sets-to-algebras step and "moved by some element of `<C,a>` implies moved by `a`" both hold.
  - Remark C4 (conditional expectations and martingale convergence) is correct as a conditional remark.
- **Corollary D.**
  - The conjugation formulas `h^(+-k) e_ij h^(-+k)`, generation of `SL_3` over the Euclidean ring `Z[1/2]` by
    elementary matrices, and density of `A` in `SL_3(Q_2)`.
  - The stabilizer of the compact open orbit `P` is open (tube lemma). Full support gives `hP = P` from a null
    symmetric difference. `C <= K` gives exact invariance.
  - (D3) is the negation of clause 2 of `hyperlinear-radical-presentation-compactness`.
  - The logic "interface ==> (ICR2) ==> `J in Rad_hyp`, contradicted under (SH1)" is valid.
- **Duplicates.** Ran `bin/cairn search --similar` on all four claims and keyword greps. No existing node states
  the element-level D8/seed radical transfer, the dual-measure test, or the coset-lamp fixed-algebra criterion.
  (C3) is the hyperlinear analogue of the induction in `corona-finite-index-radical-heredity`, which covers
  MF/fd/lin only. It is a sub-lemma, not a separate claim.
- **Citations.** Spot-checked arXiv:2608.06222 (Kun--Thom): title, authors and v1 6 Aug 2026 / v3 20 Aug 2026
  confirmed. The other arXiv ids are already cited elsewhere in the repo and are used only in notes, not in proofs.

**Changed.**

1. `central-d8-mark-radical-equals-seed-radical` and artifact Corollary A'. "The terminal output `(ICR2)` is
   equivalent to `m_0 in Rad_hyp`" was mildly overstated. Compactness returns *some* non-effective finite-window
   modulus, not one factoring through `E_act`/`eta_seed`. The wording is softened to "qualitative content". The
   consequence paragraph now says it uses two ESTABLISHED nodes and is not part of the direct route.
2. `homogeneous-quotient-ce-frees-sl3-lamp-seed`. Added a scope paragraph: the obstruction is for the recursively
   presented host `P_host` itself, where the Higman route applies the interface. It does not exclude interfaces for
   other packets, such as a finitely presented overgroup, where `Rad_hyp(P_host) <= Rad_hyp(Gamma) cap P_host` can be
   strict. The hole stays open.
3. `homogeneous-quotient-ce-frees-sl3-lamp-seed-proof`. Added `infinite-character-interface-is-marked-radical-certificate`
   (ESTABLISHED) to `requires:`, since (D3)'s "no such interface" clause consumes it.

**Not done.** The solver's suggestion to add `sl3-codense-lamp-higman-route` to the `invalidates` list of
`sl3-homogeneous-quotient-crossed-product-is-connes-embeddable` is logically correct under (SH1), but that is an
edit to a committed node and is left for a separate pass.

A further observation, not verified against a source: by Tits' theorem that a non-compact open subgroup of
`SL_3(Q_2)` is the whole group, together with maximality of `K` among compact subgroups, the closure of `<C,a>` is
all of `SL_3(Q_2)` for every `a in A - C`. That would extend Corollary D to every two-point seed. This is unverified
and is not recorded in a node.

**Verdict.** Sound. It lands with the three small fixes above.
