# bh-major-cube-b (cubulated groups: BBCMP Q1.15, BBMZ 5.3(10), non-special case)
Updated 2026-09-18 ~15:40 CDT (relaunched after restart).

## Approach
Li-Garside coding of cubulations -> finiteness via Cuntz stabilization -> type (A)/simple host.
Signature: "pointed cubes, pure holes, Cuntz packing".

## Established (landed)
- d172582dd8 pointed-cube-categories-are-li-garside-categories (+ -proof): Li's Garside layer for every free cocompact cubulation.
- ba9176b48a perron-weights-do-not-give-li-finiteness (+ -proof): Perron proof invalid; the real criterion is height + (Pack).
- 63bf7063bf thin-cycles-decide-li-packing (+ -proof): Pack fails iff there is a hitting set plus a thin growth cycle; powers never help.
- 16be960ff1 cuntz-stabilized-garside-full-groups-are-f-infinity (+ -proof): F(G_C x O_2) is F_infinity for every Li-Garside C with trivial units and (Acyc).
- 16be960ff1 Q1.15 node Attempts 6-7: reduction to gates G1-G3.
- 85b04172cd Perron citations now point to ba9176b48a (claim OPEN, proof INVALID, free-group node corrected, synthesis artifact rows).
- 914bce298c pointed-cube-bisection-locus-is-the-regular-boundary (+ -proof); Q1.15 Attempt 8.
- 877d639852 flagged-pointed-cube-category-resynchronizes-cubulated-actions (+ -proof): G1 solved for every free cocompact cubulation.
- 877d639852 torsion-free-cubulated-groups-embed-in-f-infinity-simple-groups (+ host proof): OPEN, proof CLAIMED (answers Q1.15 if it stands); referee checklist in the proof node.
- eef9cb4f68 REPAIRED after bh-ref-q115-b (sink characters): host rebuilt on X_inf = dOmega cap Omega_inf; still OPEN pending re-review (bh-ref-q115-a independent).
- 3d36b55b03 both referees integrated: Lemma L (direct link lemma), Lemma E-prime, full (St)/(LCM) node, full Garside verification; OPEN pending cross-check by bh-ref-q115-b.

## Needs (open gates for Q1.15)
- INDEPENDENT REVIEW of 877d639852: two referees on the checklist (Lemma C and lcm, heads and left-divisor closure, maximal characters, germ formula, Cuntz use of Li lemma 3 read over Gamma(*), Lemma E and Acyc, hypotheses of Li Cor D and Matui simple2).
- Literature priority check beyond a bounded web search.

## Dead
- Pointed-cube carrier outside R (no germ at non-regular points; Z^2*Z has no closed carrier).
- Perron eigenvalue in place of (t<d) (no packing control).
- Power Garside families on raw codings (Li's (2_Gamma) reimports one-layer thin cycles).
- Li maximal datum on C x O_2 (thin cycles among Cuntz-hole types).

## Sparks
- (Acyc) for general cube complexes may follow from Fernos-type strongly separated hyperplanes at regular points.
- The same Cuntz-packing argument should apply to Zappa-Szep categories (self-similar units), with units handled as in lem:Stab.
