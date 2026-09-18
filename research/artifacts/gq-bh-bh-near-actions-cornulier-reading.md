# bh-near-actions: Cornulier, "Near actions" (arXiv:1901.05065), reading for Boone--Higman

Source: arXiv e-print fetched on MSI 2026-09-18 (source file near_2018_1226.tex,
7698 lines), copied to gq/src/bh-near-actions/near.tex. Labels below are the TeX labels.

## Definitions used
- Near action: homomorphism to Sym*(X), bijections between cofinite subsets modulo finite
  disagreement. Index character: the homomorphism G -> Z given by the index of near
  permutations; it vanishes on realizable (induced by an action) near actions.
- Finite type (for G finitely generated): some/every near Schreier graph has finitely many
  components (line 560).
- Neat: near isomorphic to (realizable) ⊔ (finite type) (Theorem `nearactionfp`, line 2905).
- Profinitely finitely presented (Definition `profipre`, line 3036).

## Results used (verbatim content, paraphrased only where marked)
- Theorem `nearactionfp` (line 2905): for a finitely presented group, every near action is
  neat.
- Proposition `notfp` (line 3044): for Γ finitely generated, the following are equivalent:
  Γ is profinitely finitely presented; every sparse near Γ-action is realizable; ... is
  completable; ... is neat. So a group that is not profinitely finitely presented has a
  non-neat near action.
- Example in §`dig_pfp` (line 3114): for any nontrivial finite F and d >= 1, F wr Z^d is not
  profinitely finitely presented (argument via [CGD]: a finitely presented cover has a
  finite-index subgroup mapping onto F * Z^d).
- Remark after `notfp` (line 3073): restricting a neat near action to a finitely generated
  subgroup need not give a neat near action. (The printed example has a typo: "H is
  profinitely finitely presented" should read "is not".)
- §`s_neretin` (lines 292, 771-773): Thompson's V and Neretin's groups are near
  automorphism groups of (colored) rooted binary / regular trees.
- The Kapoudjian class of a near action lies in H^2(G, Z/2) (§`i_kapou`, line 5108 onward);
  Houghton near actions of Z^d have nonzero class.

## What this gives for BH
1. (a) Necessary conditions: none from neatness. Node
   `lamplighters-in-v-show-near-action-neatness-is-no-bh-obstruction`: F wr Z ≤ V, yet F wr Z
   has non-neat near actions and is not profinitely finitely presented. The only extra
   near-action property of an infinite simple (or perfect) host is that its index character
   vanishes, so every near action of the host is balanced. That restricts nothing about the
   input either, since restriction of a balanced near action is balanced.
2. The shell route: the near shift group R_ν = ⟨λ(P), s⟩ acts on N with one component in
   its near Schreier graph (s joins n to n+1), so its near action is of finite type and
   Theorem `nearactionfp` says nothing. This was already recorded by gq-typeA-design
   (Attempt 1 on `steinberg-resolvent-shell-envelope-is-finitely-presented`). The index
   character of R_ν on N is nonzero (it is ±1 on s, 0 on λ(P)), so that near action is never
   completable. This is consistent, and it is not an obstruction.
3. (b) Constructions: Cornulier's framework recovers V and Neretin groups as near
   automorphism groups, but I found no theorem in the paper that produces finitely presented
   simple groups from near actions of an input. The near-automorphism group of a regular tree
   is simple (Kapoudjian 1999, cited at line 6790) but uncountable, and simplicity in the
   eventually regular case is left open there (line 6850). No construction attempted beyond
   this reading. Stalled per the stall rule.

## Spark (out of scope, for other lanes)
Infinite finitely generated simple LEF groups are not profinitely finitely presented
(line 3110). Examples: commutator subgroups of topological full groups of minimal subshifts
(Juschenko--Monod; LEF by Grigorchuk--Medynets). Whether these, when their word problem is
solvable, embed in finitely presented simple groups is a natural named-type question for an
amenable/topological-full-group lane.
