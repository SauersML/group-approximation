# The P-isotropy spectral sequence as a computable obstruction to the coning statement

Author: swarm-0917-w19-w19-z-last1 (2026-09-19). Target:
`loop-braid-forbidden-ring-coning-statement` (CS). Notation from
`zp-loop-braid-forbidden-ring-push-reduction-2026-09-17.md` §0–§1.

## 0. Summary

- P = PLB_n = PΣAut_n acts on Y = Y_n(F;v,w) with strict fundamental domain
  Q_Y = OM(G), where G = K_{free∖{v,w}} ⊔ {vw}. So Q_Y ≅ ΣOM(K_{N−2}).
- The stabilizer of σ ∈ Q_Y is P_σ ≅ PLB_{n−|σ|}. It is embedded by cabling.
- The isotropy spectral sequence is
  E^1_{p,q} = C_p(Q_Y; H_q(P_−)) ⇒ H^P_{p+q}(Y) = H_{p+q}(EP ×_P Y).
- **Theorem A (necessary condition).** Suppose Y is 2-connected. This is CS at N = 11 and at
  N = 12. Then, over every field k:
  - H_2(Q_Y; k) = 0, and
  - E^2_{1,1} = H_1(Q_Y; U^1) = 0.
  Here U^1_σ = im(H_1(P_σ) → H_1(P)).
- **Theorem B (reduction to linear algebra).** If H_1(Q_Y) = H_2(Q_Y) = 0 and the
  B-term below vanishes, then E^2_{1,1} is the cokernel of an explicit map between finite
  F_p-vector spaces. The map comes from the homology of OM-links. `e2_row1.py` computes it.
- **Validation.** In degree 1 the same code reproduces the independent abelianized-colimit
  ranks of artifact §6:
  - coker = 2 over F_3 at N = 7 (n=7, F=∅ and n=8, |F|=1);
  - coker = 0 rationally;
  - coker = 0 at N = 8, 9.
- **Decisive run.** N = 11, d = 2, p = 3: see §5.

## 1. Inputs

(I1) **Jensen–McCammond–Meier.** For every k, H^*(PΣAut_k; Z) is torsion-free and generated in
degree 1, with Poincaré series (1 + kt)^{k−1}. Equivalently, it is the quadratic dual of the
McCool presentation. So H_*(PΣAut_k; k) is the quadratic coalgebra dual to it, over every field k.

(I2) **Cabling on H_1.** Cabling the fused ring f onto the pair (a, b) sends
- A_pf ↦ A_pa + A_pb,
- A_fq ↦ A_aq + A_bq,
- A_pq ↦ A_pq.

This is checked in `experiments/loop-braid-push-2026-09-17/abelian_colimit.py`. The dual map on
H^1 is surjective onto H^1(P_σ). Because H^* is generated in degree 1, H^*(P) → H^*(P_σ) is
surjective in every degree. Hence H_q(P_σ; k) → H_q(P; k) is injective for all q.

So E^1 is a subspace coefficient system on Q_Y: E^1_{p,q} = C_p(Q_Y; U^q), with
U^q_σ ⊂ H_q(P).

(I3) **Description of U^1.** Let W = H_1(P) = k^{n(n−1)}, with basis e_ij. Then U^1_σ is the space
of vectors (w_ij) such that:
- w is constant on each block product I × J of the partition of [n] determined by the pairs
  of σ (unordered);
- w is zero on each diagonal block I × I.

Also U^1_σ = ∩_{e ∈ σ} U^1_e. Moreover dim U^1_σ = (n − m)(n − m − 1), where m = |σ|.

## 2. Theorem A

**(A1) Row 0 splits off.** Q_Y ⊂ Y is a strict fundamental domain. So the composite
Q_Y → EP ×_P Y → Y/P = Q_Y is the identity, where the first map is σ ↦ (∗, σ). Hence the edge
map H_p^P(Y) → E^2_{p,0} = H_p(Q_Y) is split surjective. So E^∞_{p,0} = E^2_{p,0}, and every
differential leaving row 0 is zero.

**(A2) Row 2 fills H_2(P).** Take any McCool relator. Its quadratic part is one of
- A_ij ∧ A_kl,
- A_ij ∧ A_kj,
- (A_ij + A_kj) ∧ A_ik,

and each of these uses at most 4 indices. For N ≥ 7 there is a vertex pair (a, b) of the K_{N−2}
part of Q_Y avoiding all of them. Its stabilizer contains the corresponding subgroup PΣAut on the
remaining rings, and (I1) with (I2) shows that the class lies in U^2_{(a,b)}. By (I1), H_2(P) is
spanned by these classes. So Σ_v U^2_v = H_2(P); that is, E^∞_{0,2} → H_2(P) is onto.

**(A3) Conclusion.** Assume Y is 2-connected. Then H^P_k(Y) = H_k(P) for k ≤ 2. The filtration of
H^P_2 has graded pieces E^∞_{0,2}, E^∞_{1,1}, E^∞_{2,0}. By (A2), F_0 = H_2(P) is everything, so
E^∞_{1,1} = E^∞_{2,0} = 0.

By (A1), E^∞_{2,0} = H_2(Q_Y). The only differential that could hit (1,1) is
d^2: E^2_{3,0} → E^2_{1,1}, and it leaves row 0, so it is zero by (A1). Hence
E^2_{1,1} = E^∞_{1,1} = 0. ∎

Remark. H_2(Q_Y) = H̃_1(OM(K_{N−2})), which vanishes at N = 11 over F_2, F_3, F_5, Q by
`om_homology_output.txt`. So the first half of the conclusion passes.

## 3. Theorem B: a Čech resolution

For e = (a, b) and f = (c, d) disjoint, M_ef := W/(U_e + U_f) is 2-dimensional. Its coordinates are
- λ_1 = w_ac − w_bc − w_ad + w_bd,
- λ_2 = w_ca − w_cb − w_da + w_db.

**Lemma.** For every simplex σ, the sequence
0 → W/U_σ → ⊕_{e∈σ} W/U_e → ⊕_{e<f∈σ} M_ef → 0
is exact.

*Proof.*
- The composite is zero, by the Čech sign convention.
- Injectivity on the left holds because U_σ = ∩ U_e.
- Exactness in the middle: W/U_e ≅ k^{2n−2}, with coordinates the "row/column across e"
  differences. The M_ef coordinates of different pairs {e, f} use disjoint entries (the cross
  entries between e and f). So the right map is onto.
- Dimensions: (2n − 2)m − 2·C(m, 2) = n(n−1) − (n−m)(n−m−1), which is dim W/U_σ. ∎

Write A = W/U, B = ⊕_e W/U_e and C = ⊕ M. B and C are sums of coefficient systems supported on
stars:
- H_k(Q; B) = ⊕_u W/U_{e(u)} ⊗ H̃_{k−1}(lk u);
- H_k(Q; C) = ⊕_{τ edge} M_τ ⊗ H̃_{k−2}(lk τ).

Suppose H_1(Q) = H_2(Q) = 0 (so H_1(Q; W) = H_2(Q; W) = 0) and H_2(Q; B) = 0. Then

  E^2_{1,1} = H_1(Q; U) ≅ H_2(Q; A) ≅ coker(H_3(Q; B) → H_3(Q; C)).

The map takes u ∗ z (with z a 2-cycle of lk u, tensored with y ∈ W/U_{e(u)}) to its residues at
the edges τ ∋ u, each tensored with ±λ(y). The general-degree version (d in place of 2) is what
`e2_row1.py MODE n |F| d p` computes. At d = 1 it computes H_0(Q; U) − dim(image), and this
matches artifact §6, as recorded in `e2_validation.txt`.

## 4. Validation (degree 1)

In degree 1 the map U^1 → W gives an exact sequence:
0 = H_1(Q; W) → H_1(Q; A) → H_0(Q; U^1) → W → H_0(Q; A) → 0.

Here H_0(Q; U^1) = colim^ab. With H_0(Q; A) = 0 this gives
rank colim^ab = n(n−1) + dim H_1(Q; A).

`experiments/loop-braid-isotropy-2026-09-17/e2_validation.txt` has coker = dim H_1(Q; A). The
table compares it with `experiments/loop-braid-push-2026-09-17/abelian_colimit_output.txt`.

| case | e2_row1 coker | colim^ab − n(n−1) |
|---|---|---|
| Y, n=7, F=∅, p=3 | 2 | 44 − 42 = 2 |
| Y, n=7, F=∅, p=10^6+3 | 0 | 0 |
| Y, n=8, \|F\|=1 (N=7), p=3 | 2 | 58 − 56 = 2 |
| Y, n=8, F=∅, p=3 | 0 | 0 |
| Y, n=9, \|F\|=1 (N=8), p=3 | 0 | 0 |

The two codes are independent, one using a colimit presentation and the other the Čech
resolution. All five values agree, including the 3-torsion anomaly at N = 7.

## 5. The decisive computation at N = 11 (degree 2), and what it shows

**Inputs** (`om_homology_output.txt`):
- H̃_*(OM(K_7); F_3) = (0, 1, 462). So H_1(OM(K_7); Z) = Z/3, and it is torsion.
- H̃_1(OM(K_9); F_3) = 0, so H_1(Q_Y) = H_2(Q_Y) = 0 at N = 11.

**Only p = 3 can contribute.** The target H_3(Q; C) = ⊕_τ M_τ ⊗ H̃_1(lk τ) is nonzero only for
τ ∋ (v,w) or (w,v), with lk τ = OM(K_7). So the target is 0 over every field of characteristic
≠ 3, and the test is vacuous there. Over F_3 the target has dimension 36·4·2·1 = 288.

**Result** (`e2_Y11_p3.txt`):
- dim H_2(Q; B) = 0;
- rank(H_3(B) → H_3(C)) = 288;
- coker = 0.

Hence E^2_{1,1}(Y_11; F_3) = 0, and the necessary condition of Theorem A holds at N = 11 over
every field.

**N = 12** (`e2_Y12_p3.txt`, which prints target dim 0): the same target vanishes identically.
- τ ∋ vw has link OM(K_8), and H̃_1(OM(K_8)) = 0.
- τ in the K_10 part has link ΣOM(K_6), and H̃_1 = H̃_0(OM(K_6)) = 0.

So the degree-2 test is vacuous at N = 12, and **N = 11 is the unique nonvacuous degree-2 instance
of the row-1 test.**

**What this establishes.**
1. The mechanism that refutes the degree-1 strengthening at N = 7 is exactly a nonzero row-1
   class, H_1(Q; A) ≠ 0 mod 3 (§4). Its degree-2 analogue is fed by H_1(OM(K_7)) = Z/3, and it
   does **not** obstruct CS at N = 11: the class vanishes. That removes the most natural candidate
   counterexample to CS.
2. It does **not** prove CS. The isotropy spectral sequence detects only H^P_*(Y), and
   H^P_*(Y) = H_*(P) in low degrees is necessary but not sufficient for connectivity of Y. The
   higher rows are forced by (A2), and (A1) makes row 0 split. So at N = 11 the total-degree-2
   information in this spectral sequence is used up. **The cohomology-index family cannot decide
   CS at N = 11 beyond this test.** A proof must come from a geometric input, such as the Björner
   nerve or the one-ring push (★′) of artifact §7.

## 6. Reproduction

From `experiments/loop-braid-isotropy-2026-09-17/`:
- `python3 om_homology.py 4 5 6 7 8` → `om_homology_output.txt`. K_9 mod 3 was run separately
  and appended.
- `python3 e2_row1.py Y 7 0 1 3` (and the other rows of §4) → `e2_validation.txt`.
- `python3 e2_row1.py Y 11 0 2 3` → `e2_Y11_p3.txt`. This takes about 10 min, and python-flint is
  required.
