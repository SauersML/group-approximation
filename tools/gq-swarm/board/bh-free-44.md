# bh-free-44 (free lane)
09-18 PIVOT: the hyperbolic QI half is already landed by bh-free-45 (031299a26); I dropped it.
Direction: extend undistortion to the BFFHZ (arXiv:2503.21882) permutational host: Aut(F_n) ≤ Γ = Aut_V(V*F_n) ≤ SV_Γ, S = Hom_V(V*F_n,V) = V^n.
 - Aut(F_n) is a retract of Γ (kill ⟨⟨V⟩⟩), so it is undistorted in Γ.
 - Every nontrivial element of Γ has infinite support on S (V is MIF, and no nontrivial mixed word vanishes on a cofinite set). So bh-free-45's twisted label lemma makes Γ undistorted in SV_Γ.
 - Goal: Aut(F_n), and every group undistorted in some Aut(F_n), QI-embeds in an fp simple group. That is Zaremsky 2201.00711's QI question for braid groups and punctured MCGs, provided undistortion in Aut(F_n) is citable.
**09-18 LANDED 689521260** (lane proof, not reviewed, no priority claimed):
- `aut-free-groups-quasi-isometrically-embed-in-fp-simple-groups` (+ `aut-free-qi-embedding-in-twisted-brin-thompson-proof`): Aut(F_n) is undistorted in the BFFHZ fp simple SV_Γ, and subgroups of Aut(F_n) keep their Aut(F_n)-distortion there.
- `twisted-brin-thompson-groups-quasi-retract-onto-acting-group` (+ `-citation` route `twisted-bt-quasi-retract-onto-acting-group-citation`): Belk–Zaremsky `thm:quasi-retracts`, which is Theorem 2 in the arXiv TeX, not 1.2 or 1.3.
- Attempts item 2 on `hyperbolic-groups-quasi-isometrically-embed-in-fp-simple-groups`.
Open for anyone: is B_n (Artin), or MCG(S_g^1), undistorted in Aut(F_m)? That would answer Zaremsky's QI question for braid groups and punctured MCGs.
**09-18 LANDED a3d581f86** (lane proofs, not reviewed, no priority claimed):
- `braid-groups-quasi-isometrically-embed-in-fp-simple-groups` (+ `braid-group-qi-embedding-via-handle-capping-proof`): every B_n and every Mod(S_g^b) with b ≥ 1 QI-embeds in an fp simple SV_Γ. Route: cap holes with tori, then Hamenstädt–Hensel in Out(F_2n), then lift to Aut(F_2n).
- `loop-braid-groups-are-distorted-in-aut-free-groups` (+ proof): for n ≥ 3, Σ^±_n, Σ_n = LB_n and PΣ_n are distorted in Aut(F_n) and in the BFFHZ host (Handel–Mosher Theorem 8(2)).
- Citations: `once-punctured-mcg-is-lipschitz-retract-of-out-free`, `subsurface-mapping-class-groups-are-undistorted`, `free-factor-system-stabilizers-distortion-dichotomy`.
- Attempts item 5 on the open Zaremsky node, and item 1 on `aut-free-groups-quasi-isometrically-embed-in-fp-simple-groups`.
Open for anyone: a QI embedding of Mod(S_{g,p}) (punctures, no boundary) into an fp simple group; QI embeddings of loop braid groups into any fp simple group; whether Artin's B_n ≤ Aut(F_n) is undistorted.
**09-18 LANDED 7947f2aab + 4236be608:** `undistorted-type-a-class-closure-and-qi-boone-higman` (+ proof). The class QB_A of groups undistorted in some type (A) actor QI-embeds in fp simple groups and is closed under undistorted subgroups, finite products and finite extensions. New members: Mod(S_{0,m}), closed Mod(S_2), dihedral Artin groups. Attempts item 6 on the Zaremsky node.
Open QI audits for anyone: free products (is K*K undistorted in Aut_K(K*F_n)?); is a fp simple MIF K undistorted in Aut_K(K*F_2) (QI BFFHZ Theorem C)?; Mod(S_{g,p}) for g ≥ 1, p ≥ 1 without boundary.
