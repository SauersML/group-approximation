# Swarm log: zaremsky-2-12-loop-braided-v-type-f-infinity, 2026-09-16

- **Lane:** swarm-zaremsky-2-12-loop-braided-v-t.
- **Hole worked:** `loop-braid-descending-links-are-eventually-simply-connected` (locked, TTL 180m).

## Literature gate (2026-09-16)

- Zaremsky's open problems list (PDF dated July 12, 2026) still lists Problem 2.12 (type F_∞ for the
  loop braided Thompson group) as open.
- Checked arXiv 2504.05787, 2110.05318, 2411.04800, 2503.21882, Zaremsky's paper listing and a web
  search. No source found proves finite presentability or higher finiteness properties of `V_loop`.
  WZ (arXiv:1405.5491v3, Conjecture `conj:Vloop_Floop_conj`) state F_∞ as a conjecture and "do not
  attempt to prove" it.
- For the ingredients:
  - WZ arXiv:1405.5491v3 (TeX): §5.3 definitions, Obs 5.8, Prop 5.9, the forest action conventions;
  - BFMWZ arXiv:1210.2931 (TeX): matching complex connectivity and the Quillen form;
  - Ershov–Zaremsky arXiv:2505.18826v3 §2.2, a verbatim McCool presentation. This upgrades McCool
    from "unverified" in the DL artifact.

## Result

- **Theorem.** `L_n(LB_*)` is simply connected for `n ≥ 8`. With the established claims (properly
  graded, `LB_n` of type `F_∞`) and WZ Prop 5.9, `V_loop` is finitely presented.
- **Artifact:** `research/artifacts/zp-loop-braid-descending-links-simply-connected-2026-09-16.md`.
- **Nodes:**
  - `ordered-matching-complex-kn-simply-connected-n-ge-8` with `-proof` (`requires: []`);
  - `pure-loop-braid-group-is-colimit-of-cabling-stabilizers` with `-proof` (`requires: []`);
  - `loop-braid-desc-links-simply-connected-via-colimit`, targeting the hole and requiring both claims.

## Proof outline (carrying out DL artifact §4)

1. **Strict fundamental domain.**
   - `LB_n = PLB_n ⋊ S_n`.
   - Cloning sends permutation braids to permutation braids, with the permutation computed from Lemma A.
   - So `r[g, Γ] = [s_g, Γ]` is a P-invariant retraction onto `Q = {[s, Γ]}`, which is a strict
     fundamental domain.
   - `Q ≅ OM(K_n)` via `[s, e_k] ↦ (ρ(s)k, ρ(s)(k+1))`, and the stabilizers are
     `P_π (PLB_{n−m})κ_Γ P_π^{-1}`.
2. **Covering criterion.** If Q is simply connected and the vertex-edge colimit of stabilizers maps
   isomorphically onto P, then X is simply connected. A direct universal-cover proof is in artifact §3.
3. **`OM(K_n)`.**
   - Connected for `n ≥ 5` (diameter 2).
   - Simply connected for `n ≥ 8`, by Quillen 9.1 over `M(K_n)`: fibers over closed k-simplices are
     `S^k`, links are `M(K_{n−2k−2})`.
   - Machine certificate for `n = 8, 9`.
4. **Cabled McCool generators**, with a hand proof from three base cases plus conjugation by
   permutation braids:
   - `(A_pq)κ_k = A_{p̂q̂}`;
   - `(A_pk)κ_k = A_{p̂,k+1} A_{p̂,k}`;
   - `(A_kq)κ_k = A_{k,q̂} A_{k+1,q̂}`.

   Hence `P_{(a,b)} = ⟨A_ij (i, j ∉ {a,b}), A_ib A_ia, A_aj A_bj⟩`.
5. **Colimit for `n ≥ 7`.**
   - Glue `ι_v(A_ij)` over the connected complex `OM(K_{n−2})` of vertices avoiding `{i, j}`.
   - McCool relators involve at most 4 indices, so they die in one vertex group.
   - Mixed generators `A_ib A_ia` lie in an edge stabilizer with a vertex avoiding their indices, which
     gives surjectivity.

## Dead ends and corrections

- **Complete join over `OM(K_n)`** (DL artifact §3). It is dead: the invariant
  `f = e_13 − e_23 − e_14 + e_24` shows that fusion bands can clasp. Not needed here: the covering
  criterion only uses the colimit, not a join structure.
- **"Cable twist" worry** (DL artifact plan). The explicit formulas show no twist: the conjugator of
  `x_{p̂}` for `q = k` is exactly the cable `x_k x_{k+1}`, and the cable itself is conjugated rigidly
  by `x_{q̂}`. The script also checks that the exponents `e_{k,k+1}`, `e_{k+1,k}` vanish.
- **First formula order.** My first guess `A_{p̂,k} A_{p̂,k+1}` for `q = k` was wrong: that conjugates
  by `x_{k+1} x_k`. The script caught this, and the correct order is `A_{p̂,k+1} ∘ A_{p̂,k}`.
- **Small n.**
  - `OM(K_5)` and `OM(K_6)` have `H_1(F_2)` of rank 41 and 46, so the method genuinely needs larger n.
  - `OM(K_7)` is inconclusive by the greedy certificate, with `H_1 = 0`.
  - The colimit argument needs `n ≥ 7`, because `OM(K_{n−2})` must be connected.

## Computations

In `experiments/zaremsky-2-12-loop-braided-v-type-f-infi-2026-09-16/`:

- `cabling.py` and `cabling_output.txt`:
  - Lemma A (random);
  - well-definedness of letterwise cloning on short words;
  - McCool relators R1–R3 for `n = 4, 5, 6`;
  - cabled formulas for `n ≤ 7` (350 cases).

  All True.
- `matching_pi1.py` and `matching_pi1_output.txt`: π_1 certificates and `H_1(F_2)` ranks for `OM(K_n)`,
  `M(K_n)` and `M(L_n)`.

## Weak points for a referee

- **Quillen's Theorem 9.1** is used in the (k−1)-fiber / (d−k−1)-link form of BFMWZ and WZ. The
  original was not fetched. For `d = 1`, `n = 8, 9` are machine-checked, and the general n rests on
  the cited form.
- **Dangling bookkeeping in Lemma 2.3.** It relies on `g · λ_k = λ_{ρ(g)k}` (WZ TeX l. 937, 1038), so
  that `h · e_k = e_{ρ(h)k}`.
- **Composite clonings in (C1)/(C3).** `κ_{{e_1,e_3}} = κ_2` then `κ_1`, and
  `κ_{{e_1,e_5}} = κ_4` then `κ_1`. Both factorizations of `E(Γ)` agree by the product-of-clonings
  axiom.

## Open

- Higher connectivity of `L_n(LB_*)`, and hence type F_∞ of `V_loop` (Problem 2.12), is untouched.
  `loop-braid-descending-links-are-increasingly-connected` stays open.

## Referee (2026-09-16)

**Verdict: sound; landed with small citation fixes.** No mathematical error found. The chain is: the
hole `loop-braid-descending-links-are-eventually-simply-connected` (n ≥ 8) ⇐ `OM(K_n)` simply
connected (n ≥ 8) + `PLB_n` is the colimit of its cabling stabilizers (n ≥ 7) + the covering
criterion. This makes `V_loop` finitely presented through WZ Prop 5.9. Type F_∞ (Problem 2.12)
stays open.

### What was checked

- **By hand.** Lemmas 2.1–2.4, Prop 3.1 (the universal-cover argument, including injectivity of Z),
  Prop 4.1 with Remark 4.2, Lemma 5.1, Cor 5.2, Lemma 5.3, Theorem 6.1, and §7.
  - In Theorem 6.1, the relator step needs a vertex avoiding ≤ 4 indices (n ≥ 6).
  - Independence of the vertex choice needs `OM(K_{n−2})` connected (n ≥ 7).
  - Surjectivity uses (C3) with `|{a,b} ∪ S(h)| = 3`.
- **WZ conventions**, checked against the TeX of arXiv:1405.5491v3:
  - the forest action `g·λ_k = λ_{ρ(g)k}`;
  - the dangling definition, Obs 5.8 and Prop 5.9;
  - "We do not attempt to prove this conjecture here".

  Symmetry of dangling forces the `ρ(h)k` convention used in Lemma 2.3.
- **Citations fetched and compared verbatim.**
  - BFMWZ arXiv:1210.2931 TeX: `prop:matching_cpx_conn`, `ν(n) = ⌊(n+1)/3⌋−1`, and the Quillen
    application at l. 3654.
  - Ershov–Zaremsky arXiv:2505.18826v3 TeX l. 298–304: the McCool presentation and the convention
    `α_ij: x_i ↦ x_j^{-1} x_i x_j`, matching (M).
  - The solver's convention-independence argument (invert generators / reverse words, modulo R2) is
    correct.
- **Independent computation.** `referee_indep_check.py` is a new implementation, sharing no code with
  `cabling.py`. It computes letterwise cloning from the WZ generator formulas via (CS1), and gets
  `A_ij` by conjugating `σ_1β_1` by permutation braids. Results:
  - Lemma 5.1 for m ≤ 7 (644 cases);
  - the product-of-clonings identity on random words;
  - (C1) and (C3) for n = 6, 7, 8.

  All True.
- **Novelty and status.**
  - An arXiv API search (2026-09-16) found no prior proof of finite presentability or F_∞ for
    `V_loop`.
  - `bin/cairn search --similar` on both new claims found no duplicate; the only hits are the
    program's own nodes.

### Issues and changes

- **Unfetched Quillen original in a `requires: []` route.** `ordered-matching-complex-kn-simply-connected-n-ge-8-proof`
  relied on Quillen's Theorem 9.1, of which only the form used by BFMWZ/WZ had been seen. **Fixed.**
  - I added a second derivation from Hatcher–Wahl arXiv:0709.2173v4 (TeX checked), using Def 3.2
    (complete join complex) and Prop 3.5 (a complete join over a wCM complex of dimension n is wCM
    of dimension n).
  - `OM(K_n) → M(K_n)` is a complete join, and the solver's Base/Links items are exactly "`M(K_n)`
    is wCM of dimension 2". So simple connectivity now rests on BFMWZ + HW, both verified.
  - The same text was added to artifact §1 (HW) and §4, and to §9.
- **"Unreviewed" markers.** Replaced by "Refereed 2026-09-16" in the artifact header and the colimit
  route.
- **Added `referee_indep_check.py` and its output**, recorded in artifact §8.
- **Not changed (acceptable).** The colimit route cites Lemma A from the PG artifact, which is part of
  the established `loop-braid-cloning-system-is-properly-graded` derivation. The machine certificates
  for `OM(K_8)`, `OM(K_9)` are corroboration only, and the route text says so.

### Still open

- Higher connectivity of `L_n(LB_*)`, i.e. `loop-braid-descending-links-are-increasingly-connected`,
  and hence Problem 2.12.
- Simple connectivity of `OM(K_7)` is undecided but not needed.
