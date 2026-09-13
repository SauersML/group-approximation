# The length-15 unpeelable residue: virtual fibring certificates

Lane `or-length15-residue`, 2026-09-13. Input: the 30 classes of `|w| = 15`
two-generator one-relator relators left uncertified by
`research/artifacts/or-unpeelable-extreme-2026-09-12.md`.

**Status:** 21 of the 30 classes are **residually finite, hence sofic**. Each
has an explicit subgroup `H` of index `k ≤ 10` and a character `φ : H ↠ Z`
with free kernel of finite rank, so `H ≅ F_n ⋊ Z`. Every certificate was
re-checked from scratch by an independent verifier. The other 9 classes have
no certificate in covers of index `≤ 10`. No root is marked ESTABLISHED on the
strength of a finite census.

## 1. The residue

Scripts' convention: `a_h = t^h a t^-h`. Every residue class has Magnus word

    W_0 = a_1^e a_0^x1 a_2^x2 a_0^x3 a_2^x4,   e = ±1,  {|x1|,|x3|} = {|x2|,|x4|} = {1,2},

with exponents not all of one sign. Up to `census.canon` the family has 36
classes:
- 3 are partially positive, so the census had already closed them;
- 3 more have a partially positive Whitehead image of length `≤ 19`
  (`census2.pp_search`);
- 30 remain (REST).

The 33 census survivors and the 30 remaining classes match the |w| = 15 row of
the census table in the 2026-09-12 artifact. `residue.py` regenerates the 36;
its output is `residue-output.txt`.

Invariants shared by all 30:
- Solving `W_0` for `a_1` gives `G = <x, y, t | x^t = V, V^t = y>`, where
  `V = (x^x1 y^x2 x^x3 y^x4)^-e`. So `G` is an HNN extension of `F(x,y)` whose
  associated subgroups `<x,V>` and `<V,y>` have rank 2.
- `b_1(G) = 1` and `H_1(G) = Z ⊕ Z/|Δ(1)|`, where `Δ(t) = δ_0 + δ_1 t + δ_2 t^2`
  and `δ_h` is the exponent sum at level `h`.
- `ker χ` is not finitely generated, because the top and bottom letters each occur
  in two syllables (Brown). So `χ` itself never fibres.
- `χ(G) = 0` and `b_2^(2)(G) = 0`.
- `π(w) = 2` (automatic for a non-primitive relator in rank 2), so the
  negative-immersion results of Louder–Wilton and Linton never apply.

## 2. The certificate

**Proposition.** Let `G = <a,t | w>` with `w` cyclically reduced and not a proper
power. Suppose:
- `H ≤ G` has index `k`, with covering complex `X_H` (`k` vertices, `2k` edges,
  `k` cells);
- `cp` is an integer cellular 1-cocycle on `X_H` whose loop values have gcd 1,
  defining `φ : H ↠ Z`;
- `X̃` is the infinite cyclic cover along `φ`, with vertex `(v,x)` placed at height
  `x`;
- `X[p,q]` is the full subcomplex of `X̃` on heights `p..q`, and `S` is the
  largest height span of a cell.

If `X[0,S+1]` and `X[-1,S]` both collapse elementarily onto `X[0,S]`, then:
- `ker φ` is free of rank `n = 1 − χ(X[0,S])`;
- `H ≅ F_n ⋊ Z`;
- `G` is residually finite, hence sofic.

*Proof.* Consider a window `X[p,q]` with `q − p > S`, and the pieces at its top
level `q`. Every coface of such a piece lies between heights `q − S` and `q`.
So these pieces and their incidences are translates of those in the collapse
`X[0,S+1]` → `X[0,S]`, and the same collapse sequence removes them. Likewise at
the bottom. By induction `X[−m,m]` collapses onto a translate of `X[0,S]` for
every `m`. So the inclusion `X[0,S] → X̃` induces isomorphisms on all homotopy
groups. By Whitehead's theorem `X̃ ≃ X[0,S]`.

`X̃` is connected because the loop values of `cp` have gcd 1. It is aspherical
because the presentation complex of a one-relator group whose relator is not a
proper power is aspherical (Lyndon). So `ker φ = π_1(X̃)` is finitely presented.

`H` is finitely generated with `cd H ≤ 2`, and `ker φ` is a normal subgroup of
infinite index. By Bieri, *Normal subgroups in duality groups and in groups of
cohomological dimension 2*, JPAA 7 (1976), Theorem B, `ker φ` is free. For the
statement as used here, see Theorem 1.7.11 and the paragraph after it in
arXiv:2501.18306. Since `X[0,S] ≃ K(F_n,1)`, `χ(X[0,S]) = 1 − n`.

A split extension of a finitely generated residually finite group by a residually
finite group is residually finite (Mal'cev), so `H` is RF. RF passes to
finite-index overgroups, so `G` is RF and hence sofic. ∎

For `k = 1` with `φ = χ`, the collapse condition says the top and bottom letters
of `W_0` each occur once. That is Brown's criterion.

Literature context, from arXiv:2501.18306 §2.5.5:
- Kielak–Linton, GAFA 34 (2024): a hyperbolic, virtually special one-relator
  group is virtually a subgroup of an f.g.-free-by-cyclic group.
- Fisher: a virtually RFRS one-relator group is virtually free-by-cyclic.
- Wise's conjecture: hyperbolic one-relator groups are virtually free-by-cyclic.
- Button: there are RF one-relator groups that are not virtually free-by-cyclic.

None of these decides a given class. The certificates above do.

## 3. Pipeline and controls

`vfib.py WORD KMAX RPOT LAM KMIN` does the following for each index `k`:
1. Enumerate transitive degree-`k` representations by coset-table backtracking
   (`reps_bt`).
2. Build `X_H`, compute `H^1(X_H; Z)`, and try characters that are small
   integer combinations (`|λ_i| ≤ LAM`) of a basis.
3. Keep a character only if its Alexander polynomial `Δ_φ = D_j / (1 + … +
   t^(|c_j|−1))` has unit leading and trailing coefficients (necessary for
   fibring).
4. Search vertex potentials `pot ∈ [−RPOT, RPOT]^(k−1)` for a representative `cp`
   passing the top and bottom collapse test.

`verify.py` shares no code with `vfib.py`. From `w, a, t, c, pot, cp` and the
claimed `Δ` it re-checks:
- the representation and transitivity;
- the coboundary identity, the cocycle condition and primitivity;
- the two collapses, on explicitly built windows, with free faces recounted
  from scratch after every step;
- that `deg Δ = 1 − χ(X[0,S])` and that `Δ` has unit ends.

Controls. Outputs are in `cal.out` (positive) and `controls.txt` (the rest).
- **Positive.** `atataTAAT` (`W_0 = a_0 a_1 a_2 a_1^-2`, Brown-fibred): `vfib.py`
  finds a `k = 1` certificate with `Δ = t^2 − t + 1`.
- **Negative, search.** `BS(1,2) = taTAA` and `BS(2,3) = taaTAAA` are not
  virtually free-by-cyclic. No certificate for `k ≤ 6`.
- **Negative, verifier.** Fake `k = 1` certificates for BS(1,2) with `φ = ±χ`
  are rejected with `FAIL bottom-collapse` and `FAIL top-collapse`
  (`negcert.txt`).
- **Enumerator.** `reps_bt` matches brute force over `S_k × S_k` for every
  `k ≤ 6` on `taTAA`, `AAtAtAATTattaTT` and `AAtAtaTTAttaaTT`.

Bugs found on the way:
- `alexander()` crashed on a cancelled Fox entry (7 words in the first sweep).
  Only zero-valued entries hit it, so there was no wrong output; those words were
  rerun after the fix.
- The first `verify.py` let vertex and cell ids collide and rejected everything,
  including the positive control. It was fixed before any result counted.

## 4. Per-class table

Route for every row: virtual fibring (route 1). "open" means no certificate for
`k ≤ 10` (`RPOT = 1`, `LAM = 2`).

| # | relator | (e,x1,x2,x3,x4) | δ | tors | certificate (index k, span S, fibre) | result |
|---|---|---|---|---|---|---|
| 1 | AAtAtAATTAttaTT | (1,2,−1,1,2) | [−3,−1,−1] | 5 | k=10, S=5, F_26 | RF, sofic |
| 2 | AAtAtAATTattaTT | (1,2,−1,−1,2) | [−1,−1,−1] | 3 | k=3, S=5, F_8 | RF, sofic |
| 3 | AAtAtATTAttaaTT | (1,1,1,−2,2) | [−3,−1,1] | 3 | none, k ≤ 10 | open |
| 4 | AAtAtATTattAATT | (1,1,−1,2,2) | [−1,−1,−3] | 5 | k=4, S=8, F_18 | RF, sofic |
| 5 | AAtAtATTattaaTT | (1,1,−1,−2,2) | [−1,−1,1] | 1 | k=5, S=6, F_13 | RF, sofic |
| 6 | AAtAtaTTAttAATT | (1,−1,1,2,2) | [−3,−1,−1] | 5 | none, k ≤ 10 | open |
| 7 | AAtAtaTTAttaaTT | (1,−1,1,−2,2) | [−3,−1,3] | 1 | k=9, S=5, F_18 | RF, sofic |
| 8 | AAtAtaTTattAATT | (1,−1,−1,2,2) | [−1,−1,−1] | 3 | k=3, S=5, F_8 | RF, sofic |
| 9 | AAtAtaTTattaaTT | (1,−1,−1,−2,2) | [−1,−1,3] | 1 | none, k ≤ 10 | open |
| 10 | AAtAtaaTTAttATT | (1,2,1,1,−2) | [−3,−1,1] | 3 | none, k ≤ 10 | open |
| 11 | AAtAtaaTTAttaTT | (1,2,−1,1,−2) | [−3,−1,3] | 1 | k=6, S=4, F_11 | RF, sofic |
| 12 | AAtAtaaTTattATT | (1,2,1,−1,−2) | [−1,−1,1] | 1 | k=6, S=4, F_9 | RF, sofic |
| 13 | AAtAtaaTTattaTT | (1,2,−1,−1,−2) | [−1,−1,3] | 1 | k=4, S=6, F_12 | RF, sofic |
| 14 | AAtatAATTAttaTT | (1,−2,−1,1,−2) | [−3,1,−1] | 3 | k=10, S=10, F_42 | RF, sofic |
| 15 | AAtatAATTattaTT | (1,−2,1,1,−2) | [−1,1,−1] | 1 | k=5, S=4, F_11 | RF, sofic |
| 16 | AAtatATTAttaaTT | (1,−1,−1,2,−2) | [−3,1,1] | 1 | none, k ≤ 10 | open |
| 17 | AAtatATTattAATT | (1,−1,1,−2,−2) | [−1,1,−3] | 3 | k=8, S=3, F_11 | RF, sofic |
| 18 | AAtatATTattaaTT | (1,−1,1,2,−2) | [−1,1,1] | 1 | none, k ≤ 10 | open |
| 19 | AAtataTTAttAATT | (1,1,−1,−2,−2) | [−3,1,−1] | 3 | none, k ≤ 10 | open |
| 20 | AAtataTTAttaaTT | (1,1,−1,2,−2) | [−3,1,3] | 1 | k=9, S=6, F_21 | RF, sofic |
| 21 | AAtataTTattAATT | (1,1,1,−2,−2) | [−1,1,−1] | 1 | k=3, S=5, F_9 | RF, sofic |
| 22 | AAtataTTattaaTT | (1,1,1,2,−2) | [−1,1,3] | 3 | k=8, S=6, F_23 | RF, sofic |
| 23 | AAttAATTAtAtaTT | (1,1,2,2,−1) | [−3,−1,−1] | 5 | k=10, S=6, F_21 | RF, sofic |
| 24 | AAttAATTAtataTT | (1,1,−2,−2,−1) | [−3,1,−1] | 3 | k=6, S=4, F_13 | RF, sofic |
| 25 | AAttAATTatAtaTT | (1,−1,2,2,−1) | [−1,−1,−1] | 3 | k=3, S=4, F_8 | RF, sofic |
| 26 | AAttAATTatataTT | (1,1,−2,−2,1) | [−1,1,−1] | 1 | k=3, S=5, F_9 | RF, sofic |
| 27 | AAttATATAttaaTT | (1,1,−2,2,1) | [−3,−1,1] | 3 | k=6, S=5, F_15 | RF, sofic |
| 28 | AAttATATattaaTT | (1,1,2,−2,−1) | [−1,−1,1] | 1 | k=10, S=5, F_23 | RF, sofic |
| 29 | AAttATaTAttaaTT | (1,−1,−2,2,−1) | [−3,1,1] | 1 | none, k ≤ 10 | open |
| 30 | AAttaTATAttaaTT | (1,1,−2,2,−1) | [−3,−1,3] | 1 | none, k ≤ 10 | open |

The full certificates (`a`, `t`, `c`, `pot`, `cp`, `Δ`) are in
`or-length15-residue-scripts/certs13.txt` (index `≤ 6`) and `certs10.txt`
(index 8–10). The verifier transcripts are `verify13.out` and `verify10.out`.

## 5. The 9 open classes

Open: rows 3, 6, 9, 10, 16, 18, 19, 29, 30.
- **Certification index.** Of the 21 certified classes, 13 are certified at
  index 3–6 and 8 at index 8–10. The index `≤ 7` sweep ran on all 30 classes;
  the index 8–10 sweep ran on the 17 then open (`words17.txt`).
- **Rows 16 and 29.** These are the two classes with `δ = [−3,1,1]`, i.e.
  `Δ = t^2 + t − 3`. In both, no character of a subgroup of index `≤ 10` passes
  the monic filter at `LAM = 2`.
- **Row 18** (`Δ = t^2 + t − 1`, unit ends). Already `χ` passes the monic
  filter, and at index 10 42 characters pass it. None has a collapsing
  representative with `RPOT = 1`.
- **Rows 3, 6, 9, 10, 19, 30.** Some character passes the monic filter at some
  index `≤ 10`, but none collapses.
- **Δ alone does not separate the classes.** Apart from `[−3,1,1]` and
  `[−1,1,1]`, every open `δ` also occurs in a certified class. All six classes
  with cyclotomic `Δ` (rows 2, 8, 15, 21, 25, 26) are certified at index `≤ 5`.
- **No obstruction isolating the 9 has been identified.** A certificate is
  sufficient but not necessary: a character that fibres can still fail the
  collapse test for every small potential.

## 6. Reproduction

Scripts are in `research/artifacts/or-length15-residue-scripts/`. `residue.py`
imports `census.py` and `census2.py` from
`research/artifacts/or-unpeelable-census-scripts-2026-09-12/`, so put that
directory on `PYTHONPATH`. All runs used Python 3.11 on MSI.

    python3.11 residue.py > residue-output.txt
    ./sweep.sh words30.txt vf7 7 1 2 30              # index <= 7 -> certs13.txt
    ./sweep.sh words17.txt vf10 10 1 2 17 8          # index 8..10 -> certs10.txt
    python3.11 verify.py certs13.txt > verify13.out  # 13 VERIFIED
    python3.11 verify.py certs10.txt > verify10.out  # 8 VERIFIED
    python3.11 verify.py negcert.txt                 # 2 FAIL
    python3.11 vfib.py atataTAAT 1 1 2               # positive control
    python3.11 vfib.py taTAA 6 1 2                   # no CERT
    python3.11 vfib.py --crosscheck AAtAtAATTattaTT 6
