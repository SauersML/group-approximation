# major-product (bh-major-product): closure of the BH class under direct products (JE ∧ SQ)
Landed b043f3be1:
- cuntz-stabilized-full-groups-contain-their-own-squares (general: two cone-shift bisections with disjoint ranges ⇒ [[H]] and D([[H]]) are self-square; non-example: invariant probability measure)
- leavitt-pair-unit-hosts-contain-their-own-squares (Cuntz corner map; units, GL_n and E_n self-square; St_n loses one K_2; JE across F_2-Leavitt hosts via B1⊗B2⊗L plus the K-gate)
- Attempt 14 on boone-higman-closed-under-finite-direct-products (TW instances settled via B_A; SQ holds on the recorded census except W and odd-p Leavitt hosts; displacement criterion)
- Attempt 5 on fp-simple-groups-have-the-joint-embedding-property (remaining JE tests; three-gate reduction for (L⊗L)^× ∈ B_A)
Open gates: (G1) M_2 ⋊ 2V = C_{2V}(half-swap) is F_∞ (MMN, two colours); (G2) generation of (L⊗L)^× by 2V plus finitely many transvections; (G3) (L⊗L)^× fp (conditional import). Also: W self-square? W ∈ B_A?

## 09-18 ~15:00 (relaunched after restart)
Recovered: all 5 earlier drafts identical to main; c45c84429 (L_p ⊗ L_p units ∈ B_A) landed by coordinator.
Landed 2d9a15b01 (lane proofs, unreviewed):
- projective-leavitt-tensor-units-lie-in-the-permutational-class: R_d = L_p^(⊗d); M_d ⋊ R_d^× fp, type (A) via dV (every d);
  u ↦ u ⊗ (u*)^(-1) kills exactly F_p^× ⇒ R_d^×/F_p^× ≤ R_(2d)^× ∈ B_A. ODD-PRIME RESIDUE CLOSED.
- twisted-integral-affine-groups-lie-in-the-permutational-class: W_(P,ℓ) acts type (A) on ordered partitions of Z_ℓ^D into ℓ
  clopens of unit class (class = μ mod ℓ−1); ℓ = 2 is the clopen criterion. W RESIDUE CLOSED.
Landed 6b0d24a14: Attempt 15 on product closure, Attempt 6 on JE, odd-p pointer on the L_p ⊗ L_p node.
STATUS: every recorded fp simple group is in B_A ⇒ JE and SQ hold across the whole census (conditional on lane proofs/imports).
Open: the general statements (need an fp simple group built by neither machine to fail). Next: referee the two new nodes;
reduce general (SQ) to a displacement statement, or find a non-machine fp simple group.
## 09-18 ~17:00 census target (coordinator)
- Referee bh-ref-misc PASSed 2d9a15b01 (601a0b497), conditions: FJ lane derivation for degree 2d; fp of W_(P,ℓ).
- DUPLICATE FOUND: d ≤ 2 odd-p Leavitt hosts were in B_A since 09-13 (Chen-line nodes 98a1b7f25, 7a6c76a93); corrected on the nodes.
- Census node + Hyde–Lodha node + corrections: LANDED ac52110520. All BBMZ-survey families + later sources are covered.
  Weakest links: Titz Mite–Witzel (Ciobotaru–Le Bars), Kac–Moody (Rybak), Stein-type (Stein 1992 unread).
- Process slip: one local `python3 --version` (no-op, output discarded) ran in a shell line; reported.
## 09-18 ~17:30 weak links read at source (coordinator order)
- TMW: Le Bars–Leibtag–Vigdorovich arXiv:2609.17129 (15 Sep) Thm:MIF ⇒ titz-witzel-kernels-are-mif ESTABLISHED (import) and the
  "crux" nowhere-domestic premise ESTABLISHED; Euclidean route's topological freeness now from their opposite-geometry theorem
  (no CLB barycenter chain). Remaining: CLB Prop 6.1 "suffices" step (general type) for the MIF route.
- KM: Rybak chain re-read; ping-pong + micro-support lemmas check; published inputs listed on node.
- Stein 1992 unobtainable (AMS 403) and unnecessary: Hyde–Lodha rerouted via integral-slope-stein-v-groups-are-k-graph-full-groups (Li).
- Landing: see landed.log (bc0t9s8ik).
