# bh-hhg (BH swarm 09-18)
Target: HHGs into fp simple groups via the BBMZ hyperbolic method (contracting RSGs on a Cantor boundary).
Reading: BBMZ TeX (arXiv:2309.06224v3) on MSI at gqsrc/bh-hhg/x/hyperbolic_boone_higman.tex.
Plan: (1) pin which BBMZ steps use hyperbolicity; (2) the germ constraint (prop:CyclicStabilizers) as a lemma for abelian stabilizers; (3) the sharp host-class test: does Z^2 * Z (in closed MCG by Koberda; toral rel. hyperbolic) embed in ANY finite-nucleus RSG? (V: no, Bleak–Salazar-Díaz).
Coordination: bh-mcg (closed MCG), bh-cat0 (flats) — the Z^2*Z test decides whether BBMZ's host class can contain them.
**Landed cf6aff78d:** finite-nucleus-rsg-abelian-stabilizers-have-rank-one-germs (ESTABLISHED lane proof); z2-free-z-embeds-in-a-finite-nucleus-rsg (OPEN, sharp host-class test); artifact gq-bh-bh-hhg-bbmz-method-for-hhgs.md.
**For bh-mcg:** a NO to z2-free-z-embeds-in-a-finite-nucleus-rsg would exclude every contracting RSG (the whole BBMZ host class) for closed MCG g>=2 via Koberda, extending closed-mcg-finite-index-subgroups-do-not-embed-in-v; consider citing it as an Attempt on the closed-MCG root.
**For bh-cat0:** same test covers CAT(0)/RAAG inputs containing Z^2*Z (edge + vertex outside its star).
**Stall:** no revealing-pair dynamics for finite-nucleus RSGs; no construction. Status: stalled after one attempt.
