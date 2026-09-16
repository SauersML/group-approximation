# ternary-leavitt-swap-idempotent-is-full: swarm lane notes, 2026-09-16

Agent: `swarm-ternary-leavitt-swap-idempoten`. Hole locked and worked: `ternary-leavitt-swap-idempotent-is-full`.

Outcome: a **reduction**. The target is not decided. It is now proved equivalent to its anti-central half,
and a new implication from Thompson's `V` is recorded.

## Setup

- **Objects.**
  - `k = F_3`, `R = L_k(1,2)`, `G = R^x`, `z = -1`, `PG = G/<z>`.
  - `w = s0 t1 + s1 t0`, `e = 2(1 + [w])`.
  - The target: exhibit `b, c` in `F_3[G]` with `c e b = 1`.
- **What the graph had.** `ternary-leavitt-swap-problem-splits-at-central-involution` splits `F_3[G] = S_+ x S_-`.
  - The anti-central half `ternary-anti-invariant-swap-corner-is-full` asks for `c e_- b = eps_-` in `S_-`.
  - The projective half `projective-ternary-swap-idempotent-is-full` asks for `c ebar b = 1` in `F_3[PG]`.
  - Both halves were known consequences of the target, and each alone suffices for nonsurjunctivity.
  - Nothing related the two halves, and nothing gave the target back from them.

## What was proved

Full proofs are in `research/artifacts/anti-central-swap-fullness-gives-projective-2026-09-16.md`.

1. **Theorem 5 (anti-central => projective).** Solutions of the anti-central corner give explicit solutions of
   the projective one. The ingredients:
   - **Block-diagonal homomorphism.** `mu(g_1,g_2) = s0 g_1 t0 + s1 g_2 t1` is a homomorphism `G x G -> G`,
     with `mu(z,1) = zd`, `mu(1,z) = d` and `w mu(g_1,g_2) w = mu(g_2,g_1)`.
   - **Tensor map.** Linearizing `mu` modulo `z` gives a unital ring map `Psi : S_- (x) S_- -> f F_3[PG] f`,
     with `f = 2(1 - [dbar])` and the flip `[wbar] Psi(x (x) y) [wbar] = Psi(y (x) x)`.
   - **Images of the Cohn family.** The corner solution gives the family `beta_1 = e_- b`, `beta_2 = [d] e_- b`,
     `gamma_1 = c e_-`, `gamma_2 = c e_- [d]`. Tensoring it gives:
     - a Cohn family `X_i, Y_i` in `fAf`;
     - a swap-separated pair `X = Psi(beta_1 (x) beta_2)`, `Y = Psi(gamma_1 (x) gamma_2)`, with `YX = f` and
       `Y[wbar]X = 0`.
   - **Hadamard unit.** `h = [[1,1],[1,-1]]` in the chart, with `h^2 = z`, `h w h^-1 = d` and
     `h d h^-1 = w`. It swaps the Klein sectors `q_-+` and `q_+-`.
   - **Witnesses.** `b = q_++ + e_w X (X_1 H q_-+ + X_2)` and `c = q_++ + 2(q_-+ H Y_1 + Y_2) Y e_w` satisfy
     `e_w b = b`, `c e_w = c` and `cb = 1`.
2. **Corollary 6.2 (equivalence).** The target is equivalent to the anti-central half: glue `theta(b) + b_-` and
   `theta(c) + c_-`. The target is therefore also equivalent to `ternary-anti-central-summand-has-cohn-family`,
   through the existing two-route cycle.
3. **Proposition 7.1 (V embeds).** `V` embeds in `L_(F_3)(1,2)^x` by `g -> sum s_(b_i) t_(a_i)`, and the swap
   goes to `w`. Injectivity comes from simplicity of `R` through the prefix-replacement representation on
   `F_3^({0,1}^N)`. So `thompson-v-ternary-swap-idempotent-is-full` implies the target.
   - The graph already had `V <= L_(F_2)(1,2)^x` (`leavitt-surjunctivity-tower`) and a claim describing the
     signed Thompson group inside the ternary unit group. No route put the `V` corner claim on a path.

## Nodes written

- **Routes.**
  - `research/anti-central-swap-fullness-gives-projective-fullness.md`: anti-central half => projective half.
  - `research/anti-central-swap-fullness-gives-unit-group-swap-fullness.md`: anti-central half => target. It
    forms a deliberate two-route cycle with `ternary-swap-fullness-projects-to-anti-invariant-half`.
  - `research/thompson-v-swap-fullness-gives-ternary-swap-fullness.md`: `V` claim => target.
- **Artifact.** `research/artifacts/anti-central-swap-fullness-gives-projective-2026-09-16.md`.
- **Script.** `experiments/ternary-swap-fullness-equivalence-2026-09-16/verify_identities.py`, with output in
  `output.txt`: 131 PASS lines under `timeout 600`.
  - **Part A.** Chart relations and Lemma 7.2 in `F_3[Q]`, `Q = <w,d,h>` of order 16, plus the Klein and
    Hadamard idempotent algebra in `F_3[Q/{+-1}]`.
  - **Part B.** `Psi_0` restricted to `Q x Q` through the depth-2 chart: multiplicativity, `Psi_0(eps_- (x) 1) = f`,
    and the flip.
  - **Part C.** An operator model in which every Step-1 hypothesis holds, used to check the explicit `b, c`.
- **Second script.** `experiments/ternary-swap-fullness-equivalence-2026-09-16/verify_corner_map.py`, with
  output in `output_corner_map.txt`: 43 PASS lines. It checks the corner map `Phi` of artifact Section 8.1
  on `Q`.
- **No new claims.** No committed node was edited.

## Consequences not recorded by edits

These follow logically, but the graph will not propagate them automatically.

- **Shared refuters.** `projective-ternary-swap-idempotent-is-not-full` now refutes the anti-central half,
  and so does anything else that refutes the target.
- **Target equivalences.** The target is equivalent to the absence of a `K_0` state on `(K_0(S_-), [eps_-])`.
  This combines the graph's `twisted-leavitt-corner-fullness-equals-absence-of-k0-states` with the recorded
  equivalence of the anti-central half.
- **Where to search.** The Leavitt-visible half is not easier than the invisible one; it contains it.
  - A witness search should work in `S_-`, or equivalently search for a Cohn family there.
  - A solution found only on `PG` is weaker and is not known to give the target.

## Approaches and where each dies

1. **Converse, projective => anti-central.** Not proved. It would follow from a group homomorphism
   `phi : PG -> G` with `phi(wbar) != +-1`, pushed through `[gbar] -> eps_- [phi(gbar)]`.
   - The image of `wbar` is then an involution different from `+-1`. By `V(L_K(1,2)) = {0,[1]}` (Ara-Moreno-Pardo;
     imported, not re-verified here) it is conjugate to `w`.
   - **Dies at existence of `phi`.** `mu`, the diagonal `delta` and the corner maps all send `z` to `z`, `zd`
     or `d`, never to `1`.
   - The natural candidate `g -> Theta(g (x) (g^-1)^op)` needs a unital map `L(1,2) (x) L(1,2) -> L(1,2)` over
     `F_3`. This is Ara-Cortinas Question 5.7, recorded as open in `no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2`.
   - **A ring map that exists but is circular.** `Phi([gbar]) = p'[mu(g,1)] + p''[mu(1,g)]`, with
     `p' = eps_- 2(1-[d])` and `p'' = eps_- 2(1+[d])`, is a unital ring map `F_3[PG] -> S_-`.
     - It is not induced by a group map.
     - The projective half pushes to `eps_- <~ Phi(e_w)`.
     - The comparison still needed, `Phi(e_w) <~ e_-`, is equivalent to the anti-central half once the
       projective half holds.
     - `pi o Phi` is the augmentation, so the evaluation carries no information.
     - Artifact Section 8.1; checked by `verify_corner_map.py`, 43 PASS.
2. **Klein fullness from Theorem 5.** Not derived.
   - The construction carries `q_++` by the identity, and all its partial isometries live among `q_-+`, `q_+-`
     and `f`.
   - The images of `Psi` lie in `fAf`, and `f q_++ = 0`, so nothing moves mass into `q_++`.
3. **Deciding the anti-central half.** Not attempted beyond the reduction. The graph's own screens (gk3
   artifacts, 2026-09-14) were UNSAT on small supports, and the known obstructions are all consistent with
   the equation. The two surviving gates are a characteristic-three rank model and relative positivity of the
   lifted trace. Theorem 5 adds a third refuter of that half, `projective-ternary-swap-idempotent-is-not-full`.
4. **Invariants.** None obstructs:
   - trace;
   - Hattori-Stallings rank;
   - homology;
   - two-sided fullness;
   - augmentation, which vanishes on `f` and on the image of `Psi`.

## Literature gate (2026-09-16)

The WebSearch budget for this session was exhausted, so the gate ran through the arXiv API
(`export.arxiv.org`). Queries:
- `abs:"group algebra" AND abs:"directly finite"`
- `abs:"Thompson" AND abs:"group algebra" AND abs:"finite"`
- `abs:"Leavitt" AND abs:"tensor" AND abs:"unital"`
- `abs:"Leavitt" AND abs:"unit group"`
- `abs:"surjunctive" OR abs:"surjunctivity"`
- `abs:"linear sofic"`
- `abs:"Kaplansky" AND abs:"finiteness"`

**Relevant hits.** None decides the target or proves the equivalence above.
- arXiv:2608.02025v2, F. Fournier-Facio, "A torsion-free non-sofic group", 2026-08-03. Other non-sofic
  examples using the same criterion as the binary Leavitt unit group.
- arXiv:1603.03618v1, Brownlowe-Sorensen, "L_{2,Z} (x) L_{2,Z} does not embed in L_{2,Z}", 2016.
- arXiv:2606.17757v1, Ceccherini-Silberstein-Coornaert-Salo, "On surjunctive and injunctive subshifts of
  finite type", 2026-06.
- arXiv:2603.18183v1, X. K. Phung, "Around Gromov's injectivity lemma and applications to post-injunctive
  groups", 2026-03.
- arXiv:2605.20008v2, J. Oinert, "Central idempotents in group-graded rings", 2026-05. Not relevant.
- arXiv:2210.11650, "Stable finiteness does not imply linear soficity"; arXiv:1212.6780, Arzhantseva-Paunescu,
  "Linear sofic groups and algebras". Titles only.

**Via repo nodes, not re-read.**
- Ara-Cortinas arXiv:1108.0352v3, Question 5.7.
- Bilich-Hazrat-Nam arXiv:2512.09241v2, Question 2.8.
- Ara-Moreno-Pardo, nonstable K-theory of graph algebras, for `V(L(1,2)) = {0,[1]}`.

## Weakest step

Lemma 3 of the artifact is where a referee should look first: that `Psi_0` is a ring homomorphism with
`Psi_0(eps_- (x) 1) = Psi_0(1 (x) eps_-) = f`, and that the flip holds, so that `Y[wbar]X = 0`.
- Each is a one-line computation from `mu(z,1) = -d`, `mu(1,z) = d` and `w s0 = s1`, `t0 w = t1`.
- Part B of the script checks them on the finite subgroup `Q x Q`.
- Everything after Step 1 of Theorem 5 is idempotent bookkeeping, which Part C checks in an operator model.

## Referee (2026-09-16)

**Checked.**
- Read all nine listed files, plus `ternary-leavitt-swap-problem-splits-at-central-involution`,
  `ternary-anti-invariant-swap-corner-is-full`, `projective-ternary-swap-idempotent-is-full`,
  `thompson-v-ternary-swap-idempotent-is-full`, `ternary-swap-fullness-projects-to-anti-invariant-half`,
  `leavitt-algebras-l-k-1-n-are-simple`, and Lemmas 7.1-7.3 of the 2026-09-12 artifact. `git status` shows no
  unlisted solver files.
- Rederived every step by hand:
  - **Lemma 1.** The chart matrices of `w, d, h`; `h^2 = z`, `h w h^-1 = d`, `h d h^-1 = w`, `d w d = z w`;
    multiplicativity of `mu`; `mu(z,1) = zd`, `mu(1,z) = d`; the flip `w mu(g1,g2) w = mu(g2,g1)`.
  - **Lemma 2.** The Klein idempotent algebra, and `u = H q_-+ = q_+- H` with `vu = q_-+`.
  - **Lemma 3.** `Psi_0` is the linearization of a group homomorphism. `Psi_0(eps_- (x) 1) = Psi_0(1 (x) eps_-) = f`.
    The image of the central idempotent `eps_- (x) eps_-` is `f`, so the restriction lands in `fAf`. The flip
    extends bilinearly.
  - **Lemma 4.** `[d]e_-[d] = eps_- - e_-`, hence `e_-[d]e_- = 0`, and the Cohn relations.
  - **Theorem 5, Steps 1-4.** Including the membership claims and the vanishing cross terms of `cb`. I expanded
    `x'' = x_B x'` and `y'' = y' y_B` against the displayed `b, c`; they match.
  - **Corollary 6.1 (gluing).** Only needs `theta` to be a unital ring homomorphism into `S_+`.
  - **Proposition 7.1.** The Leavitt relations on basis vectors; `t_a`, `s_b` in the stated orders; `pi(u_g) = P_g`;
    injectivity from simplicity (the claim covers every field and `n >= 2`); `u_(w_V) = w`.
  - **Section 8.1.** `Phi` is well defined and multiplicative, and `pi o Phi` is the augmentation
    (`pi(p') = s1 t1`, `pi(p'') = s0 t0`). The "restatement" claim is correct.
- Reran both scripts under `timeout 600`: 131 and 43 PASS, outputs byte-identical to the committed `output*.txt`.
- Duplicates: `bin/cairn search --similar` on the three route ids finds no route relating the two halves or
  putting the `V` claim on a path; the target and projective claim had no such routes. No established node
  asserts that the halves are independent.
- Citations spot-checked on the arXiv API: arXiv:1603.03618 (Brownlowe-Sorensen, title as stated, 2016-03) and
  arXiv:2608.02025 (Fournier-Facio, 2026-08-03) are correct. Ara-Cortinas Question 5.7 matches the verbatim quote
  recorded in `no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2`. Ara-Moreno-Pardo is used only in the
  non-derived Section 8.1 and is flagged there as imported.
- `check.sh` on the four research paths exits 0.

**Changed.** One wording fix in artifact Section 8.1: conjugacy of two idempotents different from `0, 1` also
needs the complements to be equivalent. That section is labelled not derived anyway.

**Not an issue, but noted.**
- The three routes all have nonempty `requires:`, and none claims a direct proof.
- `anti-central-swap-fullness-gives-unit-group-swap-fullness` and `ternary-swap-fullness-projects-to-anti-invariant-half`
  form a two-route cycle, which the least fixpoint does not let justify itself.
- The "target equivalent to absence of `K_0` states" remark above depends on the `q = 3, d = m = 2` specialization of
  `twisted-leavitt-corner-fullness-equals-absence-of-k0-states`. It is a remark in notes only.

**Verdict.** Sound. Land as is, apart from the wording fix. Established by these routes (not as claims):
anti-central half => projective half; anti-central half <=> target, through the existing projection route; and
`V` swap fullness => target. Still open: the anti-central half itself, and the converse projective => anti-central.
