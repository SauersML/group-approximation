# sk-general-master: the right generality for the note's proof

- Lane: sk-general-master (SK swarm), 2026-09-13.
- Status: analysis plus one new explicit route (`local-annihilation-el-simplicity-explicit-extraction`), UNREVIEWED,
  queued with sk-referee-1. Every other input is a reviewed node on main.
- Line numbers refer to `$SK/manuscript-disk-1646.tex` (md5 7b3dc4ec92b4581553bc0dc2b0edcb99).

## 0. Verdict

1. **The minimal ring axioms of the note are already on main.**
   - (T): `R` finitely generated.
   - LEF: `R` is a LEF ring.
   - Simplicity: `R` simple with *local annihilation* (`local-annihilation-makes-projective-el-simple`: established,
     Lean-certified, reviewed PASS).
   The note's clopen towers are one way to verify local annihilation for `LC(X,F_2) ⋊ Z`, and not the shortest.
2. **Master theorem (a composition of reviewed nodes).** Let `R` be a finitely generated simple ring with local
   annihilation, and `n ≥ 3`.
   - Every normal subgroup of `EL_n(R)` is central or everything, and `EL_n(R)/Z` is an infinite simple Kazhdan group.
   - `EL_n(R)` is LEF iff `R` is a LEF ring. The "if" is three lines; for `n ≥ 4` the "only if" is
     `lef-elementary-groups-force-lef-rings`.
3. **Recommendation, on reader merits only.**
   - Keep the headline theorem concrete: infinite minimal Z-subshifts.
   - Replace l.154-227, the tower subsection (74 lines), by a ring lemma with an explicit Stepanov-type extraction plus
     a nine-line check for `R`: 49 lines in total.
   - The lemma is shorter, works over every finite field and every `n ≥ 3`, uses neither finite simple groups nor
     towers, and gives the reader a criterion that applies to every free minimal action of a finitely generated group
     on a subshift.
   - An optional three-line remark can say so.
   - Lane sk-proof-minimal-conceptual reached the same lemma independently (2acfcb8559), with 47 lines for simplicity
     and a candidate note of 314 lines. Two lanes starting from different points converged on local annihilation, which
     is evidence that it is the right generality. Adopt one text.
4. **Not recommended: my first abstraction, "local matrix units".** This asks that the elements `s` for which `s` and
   `FsF` lie in a subring isomorphic to `∏ M_k(F_2)` generate `R`. It is exactly the note's argument at ring level. It
   gives a correct lemma (§3), but it needs coefficients `F_2` and finite simple groups, the proof is no shorter, and
   it applies to fewer rings.

## 1. What each step of the note needs

| Step | Where | Hypothesis actually used | Node on main |
|---|---|---|---|
| (T) | l.97-99 | `R` finitely generated with 1, `n ≥ 3` | `elementary-groups-over-fg-rings-have-property-t` (EJZ, verbatim quote) |
| infinite | l.100 | `R` infinite | none needed |
| LEF | l.118-149 | `R` LEF as a ring: injective partial models into finite rings, equivalently an injective hom into an algebraic ultraproduct of finite rings | `minimal-subshift-algebra-is-simple-lef-ring` item 3; converse `lef-elementary-groups-force-lef-rings` (n ≥ 4) |
| simple ring, centre | l.102-116 | minimality, no periodic points | same node, item 2 |
| normal subgroups | l.154-227 | `R` simple, and for each finite `F` enough small elements absorbed into matrix corners | `local-annihilation-makes-projective-el-simple` (weaker hypothesis) |
| `Z(G) = 1` | l.114-116 | `Z(R) = F_2` | centre clause of the same node |

The three properties are controlled by three independent ring hypotheses: finite generation, the LEF property and
local annihilation. §4 shows none implies another.

## 2. The three formulations of the simplicity step

- **(T) The note's towers** (l.154-227, 74 lines):
  - the tower rings `B_m(U) ≅ M_{2m+1}(LC(U,F_2))`;
  - absorption (eq:absorb);
  - the corner invertibility of `k`;
  - a locally constant `κ`;
  - a constant piece `W`;
  - a copy `H_W ≅ GL_d(F_2)`, with a commutator identity for its transvections;
  - simplicity of `GL_d(F_2)`, `d ≥ 3`.
  It is specific to `F_2`, since it uses that `GL_d(F_2)` has trivial centre. Lane sk-simplicity-short-a's tower
  shortening reaches 47 lines, still `F_2`-based.
- **(M) Local matrix units** (this lane, not landed as a claim):
  - The proof is (T) with the tower bookkeeping moved into the hypothesis.
  - It needs coefficients `F_2`, for the same reason.
  - Its hypothesis implies the needed instances of local annihilation (take `t = 1 − e` for the unit `e` of the
    matricial subring, when `e ≠ 1`).
  - It is expected to fail near isotropy points, e.g. for Leavitt algebras, where local annihilation still holds.
    I did not prove that failure.
- **(A) Local annihilation** (`local-annihilation-makes-projective-el-simple`):
  - one additive-subgroup step;
  - one annihilation observation;
  - two explicit commutators;
  - the level ideal.
  About 36 lines as a lemma plus 13 lines to check it for `R` (proposal). Every simple ring, every `n ≥ 3`, any
  coefficients.

## 3. The explicit extraction (the content of the new route)

`N ⊴ EL_n(R)`, `g ∈ N` noncentral, and `F` the set of entries of `g`.
1. Some annihilated `s` (with its `t`) and `i ≠ j` give `ρ = [g, e_ij(s)] ≠ 1`. Here
   `ρ − I = (g sE_ij g⁻¹)e_ij(−s) − sE_ij` has entries in `FsR + sR`, so `t(ρ − I) = 0`.
2. `Y = ρ⁻¹ − I`, `Y_qm ≠ 0`, `l ∉ {m,q}`, `z = Y_qm c t ≠ 0` (primeness). From `e_ml(ct)ρ = ρ + ctE_ml`:
   `v = ρ⁻¹e_ml(ct)ρe_ml(−ct) = I + Y·ctE_ml ∈ N`, a one-column matrix with `v_ql = z`.
3. For `b ∉ {l,q}`: `e_bq(1)v = v·e_bq(1) + zE_bl`, so `[e_bq(1), v] = e_bl(z(v⁻¹)_ll)`, a nontrivial root.
   `(v⁻¹)_ll` is a unit.
4. The level ideal is `R`.

Each identity is checked in the route body (steps 1-6). The (M) lemma, for comparison, reads: *for a simple
`F_2`-algebra with local matrix units and `n ≥ 3`, normal subgroups of `EL_n` are central or everything*. I checked
its proof, which is the note's proof with `B_{w+1}(U)` replaced by an abstract matricial subring `A`. The component
`κ` of `eI + (k − I) ∈ GL_n(A) = ∏ GL_{nk_t}(F_2)` is nontrivial, `H ≅ GL_{nk_t}(F_2)` sits in `EL_n` through the
commutator `[e_pq(E_ab), e_qp(E_bb)] = I + E_ab E_pp`, and `k` acts on `H` by `κ`. It stays in this artifact only.

## 4. Model tests of the master hypotheses

| Ring | simple | f.g. | local annihilation | LEF ring | conclusion, consistent with known behaviour |
|---|---|---|---|---|---|
| `R_X = LC(X,F_q)⋊Z`, X infinite minimal | yes | yes | yes (§5 of proposal) | yes | `EL_n/Z` infinite simple Kazhdan LEF: the note |
| `F_q` | yes | yes | NO (`S_F = 0`) | yes | criterion silent; `PSL_n(F_q)` simple by classical means, finite |
| `M_d(F_q)` | yes | yes | NO: take `F` all matrix units, then `tM_d s = 0` forces `t = 0` or `s = 0` | yes | criterion silent (finite group) |
| `F_q[t]`, free algebra `F_q⟨x,y⟩` | no | yes | NO (domain) | yes (residually finite) | congruence normal subgroups: simplicity fails, as it must |
| Weyl algebra `A_1(F_p)` | no (centre `F_p[x^p,y^p]`) | yes | NO (domain) | yes (f.g. PI, so residually finite) | congruence normal subgroups |
| `LC(X,F_q)`, X Cantor | no | only for subshift-type X | yes (`steinberg-algebras-have-local-annihilation`) | yes | congruence normal subgroups. So local annihilation without simplicity is not enough |
| `L_k(1,d)`, k finite | yes | yes | yes (Steinberg algebra of the Cuntz groupoid) | NO (not directly finite; LEF rings are directly finite) | `EL_n/Z` simple Kazhdan, not LEF, no MF quotient (non-MF paper). Simplicity and approximation separate |
| `LC(X,F_q)⋊Z²`, free minimal aperiodic SFT | yes | yes | yes | not checked here; never LEF if `R` is finitely presented (`lef-el-groups-matricial-via-lef-ring` plus the un-lef-converse note) | `EL_n/Z` simple Kazhdan; LEF status unknown to me |
| `LC(X,F_q)⋊Γ`, free minimal Γ-subshift, Γ f.g. | yes (minimal, topologically free) | yes | yes (Steinberg node) | only with exact finite pattern models, e.g. RF Toeplitz actions (lanes sk-general-actions-a, sk-verify-3) | simple Kazhdan; LEF under that hypothesis |

So the trivial models (fields, matrix rings, domains, commutative Cantor algebras) fail the hypotheses they should
fail. The note's example satisfies all three. The Leavitt row shows that local annihilation and simplicity do not
force LEF.

## 5. Reader-merits assessment of the options

- **Ring-level headline theorem.**
  - Stronger in form.
  - Costs a definition in the abstract and the introduction.
  - The only rings verified inside the note would still be `R_X`, and LEF for the other examples needs its own proof.
  - Verdict: not better for the reader than the concrete headline.
- **Lemma inside the proof (recommended).**
  - Shorter than the tower subsection (49 vs 74 lines).
  - Coefficient-independent: the same text proves the `F_q`, `n ≥ 3` version with `Z(G) ⊆ F_q^× I`.
  - No new machinery, and no new fact to trust: each identity is displayed.
  - The reader can reuse it.
  - Verdict: better.
- **Optional remark (three lines).** "For every finitely generated simple ring `R` satisfying the hypothesis of the
  lemma, `EL_n(R)/Z` is an infinite simple Kazhdan group, and `EL_n(R)` is LEF whenever `R` is LEF. Such rings include
  the crossed product of any free minimal action of a finitely generated group on a subshift." True by reviewed nodes
  (the Steinberg local-annihilation node and Steinberg simplicity). It gains generality at three lines. The user
  decides.
- **Credit consequence.** l.58-62 credit the tower argument as the new step. With the lemma, the extraction is
  Stepanov's (Lemma 4.3) and the new input is the annihilation hypothesis. The sentence must change (proposal (a2)).
  Its exact citation waits for sk-citations.

## 6. Open items bearing on the note

- Whether local annihilation implies Stepanov's condition (b) (`local-annihilation-implies-stepanov-condition-b`,
  open). It bears only on credit wording.
- Whether the (M) failure for Leavitt algebras holds as stated in §2. It only matters if (M) is ever used.
