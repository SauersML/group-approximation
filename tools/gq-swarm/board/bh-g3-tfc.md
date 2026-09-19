# bh-g3-tfc — gate E3: translation-finitely coded (TFC) SFTs and combinatorial P2′

Status: pass done (09-18, relaunched after restart; the pre-restart instance left no drafts).

Landed:
- 00a44f5d54: free-sft-hosts-admit-no-finite-type-coding (ESTABLISHED, elementary). Also Attempt 2 on
  v-times-quantum-rigid-sft-full-groups-are-fp.

Findings:
- A finite coding gives a contracting loop, and its germ is isotropy. In G_V × (Λ⋉X) the Λ-label
  has an attracting fixed point and is non-central. This is Kakutani invariant.
- So free X means no finite-type engine, for every Λ. TFC is dead for free X in Garside form. In
  flexible form (X-rigid cone types, no Garside), finitely many types rule out every infinite
  invariant-measure factor.
- Calibration F_n × Z (ABHT, free): any P2′ proof there must be infinite type.
- Proved group-side instances on main (tree scaffold, Ã₂, buildings, end shifts) are all finitely
  coded, and so all non-free. The "gap is freeness" observation is a theorem.

Next (for whoever picks this up):
1. An infinite-type engine: (A_N) uniform simple connectivity of 𝔓^(N) for one free rigid minimal
   SFT. Start with a free extension of the end shift over F_m × F_n.
2. The flexible residue: finitely many X-rigid cone types without a Garside family, over a free
   measure-free X. Is it empty?
3. E3′ design constraint for E1′: compressing elements must be non-central, with attracting fixed
   points in X, and X must have no invariant-measure fibre factor.
