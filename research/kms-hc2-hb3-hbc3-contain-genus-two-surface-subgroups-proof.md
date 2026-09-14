---
rg: 2
id: kms-hc2-hb3-hbc3-contain-genus-two-surface-subgroups-proof
kind: route
title: Integer-labelled girth surfaces with trivial vertex words in faithful integral matrix models are girth surfaces for G_HC2(2)(p), G_HB2(3)(p) and G_HBC2(3)(p) at every odd prime
target: kms-hc2-hb3-hbc3-contain-genus-two-surface-subgroups
requires: [kms-girth-surfaces-give-surface-subgroups, cckw-kms-triangle-groups-structure]
artifacts:
  - experiments/kms-hb2-surface-subgroups/kms_girth_search.py
  - experiments/kms-hb2-surface-subgroups/search-results/summary-job785007.txt
  - experiments/kms-hb2-surface-subgroups/search-results/hc2-t24.json
  - experiments/kms-hb2-surface-subgroups/search-results/hb3-t16.json
  - experiments/kms-hb2-surface-subgroups/search-results/hbc3-t16.json
  - experiments/kms-hb2-surface-subgroups/verify_kms_certificates.py
  - experiments/kms-hb2-surface-subgroups/search-results/verify-kms-certificates.log
  - experiments/kms-hb2-surface-subgroups/verify.log
---

## The certificates

`kms_girth_search.py` ran on MSI (job 785007), with vertex words evaluated in the integral groups through the
normal-form laws.
- It enumerates all girth surfaces of a given size, up to relabelling.
- It solves for labels in `{±1, ±2}`.
- It re-evaluates every solution before recording it.

Each JSON file lists involutions `r_0, r_1, r_2` and one label `[k, t, s, x]` per side, with `t < s = r_k(t)`.
The convention is that of `kms-girth-surfaces-give-surface-subgroups`.

## Verification

`verify_kms_certificates.py` shares no code with the search. `verify-kms-certificates.log` shows ALL PASS on nine
certificates, including the three used here. For each certificate it checks:
1. the `r_k` are fixed-point-free involutions generating a transitive group;
2. every alternating `<r_j, r_k>` walk closes after exactly `2m_i` distinct chambers;
3. orientability, and `V − E + F = −2`;
4. one nonzero integer label per side; the only prime dividing a label is 2;
5. every vertex word is the identity matrix over `Z`, in these models:
   - `U_3` vertex: `x ↦ I+E_03+E_12`, `y ↦ I+E_10−E_23`;
   - `U_4` vertex: designated `x ↦ I+E_31`, other generator `↦ I+E_10−E_23`;
6. the models satisfy the `U_3` and `U_4` relators over `Z`.

## The matrix models are faithful on the integral vertex groups

Let `N_3 = <x,y | [x,y,x], [x,y,y]>` and `N_4 = <x,y | [x,y,x], [x,y,y,x], [x,y,y,y]>`.
- *Normal forms.* By Step 0(a) of `kms-girth-surfaces-give-surface-subgroups-proof`, whose argument uses no
  `p`-th powers, every element of `N_3` or `N_4` has a normal form `y^β x^α u^μ` or `y^β x^γ u^μ v^ν`.
- *`N_3`.* `verify.log` item 9 prints the symbolic image of `y^s x^t u^w` (as `b^s a^t u^w` with `x = a`,
  `y = b`). Its entries `(1,0) = s`, `(0,3) = t` and `(1,3) = −2w + st` vanish only for `s = t = w = 0`.
- *`N_4`.* `verify.log` item 9 prints the symbolic image of `y^s x^t u^w v^z` (as `b^s c^t u^w v^z` with `x = c`,
  `y = b`). Its entries `(1,0) = s`, `(3,1) = t`, `(3,0) = w` and `(2,0) = 2z + w − sw` vanish only for
  `s = t = w = z = 0`.
- So the models are injective on normal forms. A vertex word that maps to `I` is trivial in `N_3` or `N_4`.
- `U_3` is symmetric in its two generators, since `[y,x] = [x,y]^{−1}` is central. So the check does not depend
  on which generator of a `U_3` vertex is called `x`.

## Deduction for a fixed odd prime `p`

- No label is divisible by `p`.
- Adding `x^p, y^p` gives surjections `N_3 → U_3(p)` and `N_4 → U_4(p)` onto the vertex groups `X_i ≤ G`, with
  the designated generators as in the table of `kms-girth-surfaces-give-surface-subgroups`.
- So every vertex word is `1` in `G`, and each certificate is a girth surface for its group at `p`.
- Each certificate surface is orientable, with `T/8·3 − 3T/2 + T = −2` for `T = 16` (type `(4,4,4)`) and
  `T/6 + T/8 + T/8 − 3T/2 + T = −2` for `T = 24` (type `(3,4,4)`).
- `kms-girth-surfaces-give-surface-subgroups` then gives a quasiconvex genus-2 surface subgroup.
