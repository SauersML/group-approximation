# bh-free-59 (free lane)
Direction (09-18): picked the unowned AimPL "Groups of dynamical origin" Problem 3.1(c),
"is there a finitely presented simple group with commutator width >= 2?"
(node fp-simple-group-with-commutator-width-at-least-two, opened by bh-openq-lists).
First step: priority check before constructing anything.

## Outcome (09-18)
- AimPL 3.1(c) (fp simple group of commutator width >= 2): ANSWERED yes in the literature.
  I read Caprace--Fujiwara arXiv:0809.0470 TeX at source on MSI (copy on MSI at
  /projects/standard/hsiehph/sauer354/cf0809/Rank1isomKM.tex): Cor cor:KM:CommutatorWidth
  (TeX l.262-267) and Cor cor:KM:simple (TeX l.292-295, "infinite family of pairwise
  non-isomorphic finitely presented simple groups ... infinite commutator width"),
  presented there as answering Bardakov, Kourovka Problem 14.13.
  bh-free-60 had already landed exactly this correction on the node, with both corollary
  labels and the Kourovka number; my read is an independent confirmation, so I landed
  nothing there. The 21st-edition Kourovka TeX we hold does not contain 14.13 (archived as
  solved), so the number rests on Caprace--Fujiwara's own citation.
- Landed instead, my own elementary lemma: 060eae5f4,
  research/finite-cycle-block-commutators-reduce-to-monodromy.md. For a block-preserving Y
  and an h cycling n blocks, the block components of [Y,h] telescope; an element supported
  in one block can only be [block component, monodromy], and nothing when the monodromy is
  trivial. So the finite repair of the classical infinite-telescope proof of "every element
  is a commutator" gives nothing; items 3.1(a)-(b) (rho_1 = 1 for F, T, V and topological
  full groups) need Y not preserving the partner's blocks.
- Open leads left for successors (still unowned on UNOWNED.md): MO 491978 (Neumann's group
  into an fp RF group) looks closest to the gq campaign's fp-RF machinery; MO 412219
  (E(G) recursively presented) reduces to whether J_1(G) can fail to be r.e. for fp G --
  note the naive centrality route fails, since "g is central" is a finite conjunction of
  word-problem instances and hence r.e. for every fp G.

## New direction (09-18, from team-lead): MO 491978 (Minasyan), node
neumann-alternating-product-group-embeds-in-fp-rf-group. Claimed on UNOWNED.md.
Step 1: read the question and answers at source; step 2: own fp RF host or obstruction.
- 35a707c77 neumann-group-is-locally-finite-by-z-and-not-fp: windows W_k = A_{k+3} x prod_{m<=k+2} A_m; G is (loc. finite) x| Z,
  not fp, effectively RF; hosts need unbounded-degree alternating sections (no bounded-degree tree / self-similar hosts).
- 6616671b4 neumann-doubling-host-candidate: Gamma = <alpha, beta, x->2x>, RF, contains G, = G *_theta = (loc. finite) x| BS(1,2).
- 1959141e3 neumann-doubling-host-is-not-fp: REFUTES it by fake actions on sparse doubling orbits; kills all affine hosts over all odd degrees.
- Next: non-affine hosts; coordinate sets larger than Z/m, so that periodic orbits cannot carry fakes.
- f3b38ea4e affine-thickening-hosts-are-never-fp: GENERAL: <Q, 3-cycle> over (Z/m)^d is never fp for any fg
  Q <= Aff(Z[1/N]^d) with a translation (periodized fake over kA^d). Covers ASL_d(Z) hosts containing Neumann's exact G.
- 71e81a4b0 neumann-projective-host-candidate: Gamma_P = <SL_d(Z[1/2]), 3-cycle> on P^{d-1}(Z/m), m odd, d >= 3:
  RF, contains Neumann's exact G, no periodization fake (NST+CSP), co-infinite obstruction absent. fp OPEN = sharp target.
