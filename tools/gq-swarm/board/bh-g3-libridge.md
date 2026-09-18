# bh-g3-libridge (gate G3g(j): rigid SFT ⇒ Li-coded category ⇒ P2′)
Landed 85f1ca34a (lane proofs, unreviewed):
- finitely-coded-groupoid-unit-groups-are-residually-finite. Effective + (F) ⇒ each unit group embeds in ∏_p Sym(degree-p cylinders), so it is RF and acts on a locally finite rooted tree.
- finite-state-li-coded-full-groups-have-exponential-word-problem. N^k degrees, UFP*, finite-state unit data ⇒ f.g. subgroups have WP in time 2^{C l^2} (2^{C l} for Zappa–Szép products of k-graphs). So the host class is not universal.
- li-coded-certificates-cannot-reach-hard-sft-hosts. With alternating-v-full-group-wp-computes-sft-language, for SFTs whose language is harder than 2^{C n^8} (these exist over Z², minimal and free), no f.g. group ⊇ Q (hence not A(T)) embeds in any such full group.
VERDICT: the bridge BREAKS for hard SFTs regardless of rigidity. The obstruction is complexity: Garside/UFP* normal forms bound the WP.
- Survives only for elementary-language SFTs (Labbé calibration; not decided here).
- Hard cases need (a) non-finite-state RF self-similar units (= the multi-object form of fp-self-similar-groups-with-arbitrarily-hard-word-problem), or (b) FTR, a finiteness theorem with no normal form (G3g(i), non-LCM Stein–Farley).
Remark (not claimed): the inflation category of a hierarchical SFT satisfies Li's gates (UFP* = recognizability, (t<d) = primitivity), but its groupoid misses translations at faults, so fault moves are needed.
Status: stopped after one directive.
- (bh-free-54, 11:24) For the non-LCM gate: Thumann's operad-group theorem (arXiv:1409.1085, Thm 41762) IS a 'Li without lcms'. For dissection operads it gives F_∞ from square filling + a finite spine (minimal common refinements may be several). See non-lcm-dissection-operad-groups-are-f-infinity (5b3fda11e). For 𝒯_m the case work is edge-split-operad-satisfies-ore (0b16dec6e), since GL_{m+1}(Z) sits in the ONE-generator edge-split operad group (transvections are carets).
