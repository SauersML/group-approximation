# Zaremsky Problem 1.25: simple FP_2 envelopes of countable groups (lane z1-25, 2026-09-13)

Question (Zaremsky list, July 12, 2026, Problem 1.25; Llosa Isenrich–Schesler–Wu arXiv:2510.01952v1,
Question 1.12, attributed there to Zaremsky): does every countable group embed in a simple group of
type FP_2(Z)? Root: `zaremsky-1-25-countable-groups-embed-in-simple-fp2`. Status: OPEN. No answer
found after July 12, 2026. The search was bounded: arXiv abstract and HTML pages, arXiv site
search, web search; no MathSciNet or zbMATH.

## 1. Sources read, with verification level

| Source | What is used | Level |
|---|---|---|
| Leary, arXiv:1610.05813v5 (Math. Ann.) | Thm 1.1: countable ⊂ FP_2; Thm 1.3: J(l,S); definition of FP_2; Neumann's count | PDF pp. 1–2, verbatim |
| FFWZ, arXiv:2603.24687v2 | [HA_n] definition; Cor 4.14; Prop 4.12; Thm 3.6; Lemma 4.3; Remark 4.16 | HTML, fetched quotations |
| LISW, arXiv:2510.01952v1 | Thm 1.4; Cor 1.2, 1.3; Question 1.12 | abstract verbatim; HTML quotations |
| Zaremsky, arXiv:2405.18354 | fp criterion for SV_G (already on main) | repository node |
| Genevois–Tessera, arXiv:2401.13520v1 | Thm 1.5; lampshufflers over infinite groups are never fp | HTML, fetched quotations |
| Palmer–Wu, arXiv:2510.16879 | twisted BT groups acyclic; F_n inputs into acyclic F_n groups | abstract only |
| Fournier-Facio–Zaremsky, arXiv:2607.21727 | Higman/Leary rope-trick outputs are never FP_3(Q) | abstract only |

## 2. What landed (a653188efd, 38564219ba)

- Root and answer claims: `every-countable-group-embeds-in-a-simple-fp2-group` (open),
  `some-countable-group-embeds-in-no-simple-fp2-group` (open); routes `zaremsky-1-25-by-yes/no`.
- Imports: `every-countable-group-embeds-in-an-fp2-group` (Leary),
  `ha2-actions-give-fp2-twisted-brin-thompson-groups` (FFWZ),
  `rational-linear-groups-embed-in-simple-groups-same-finiteness` (LISW).
- Reduction: `every-countable-group-embeds-in-simple-fp2-via-ha2-actors` requires the open
  `every-countable-group-lies-in-a-faithful-ha2-actor` and the FFWZ import.
- Established lemmas:
  - `universal-fp2-simple-envelopes-force-uncountably-many`: yes to 1.25 gives continuum many
    simple FP_2 groups, some not recursively presented;
  - `perfect-orbit-quotients-of-fp2-actors-are-ha2-actors`: an FP_2 actor with finitely many pair
    orbits and fg stabilizers, divided by a perfect normal subgroup with faithful orbit partition,
    is a faithful [HA_2] actor. The Bieri–Strebel characterization FP_2 = fp/perfect is proved
    inline; the 1.20 lane also landed it as `fp2-iff-quotient-of-fp-group-by-perfect-normal-subgroup`.

## 3. The reduction chain

countable H ⊂ G of type FP_2 with a faithful action G ↷ S such that
(i) there are finitely many G-orbits on S × S, and (ii) point stabilizers are finitely generated
⟹ SV_G is simple (FFWZ Thm 3.6 with Belk–Zaremsky), of type FP_2 (FFWZ Cor 4.14), and contains G
(Lemma 4.3). The input group H may fail to be recursively presented. The actor G then fails too,
and so does SV_G, because a finitely generated subgroup with unsolvable word problem forces an
unsolvable word problem on the whole group.

Why the finitely presented analogue does not transfer: a type (A) actor is finitely presented, so
SV_G is a finitely presented simple group, and Kuznetsov's argument forces a solvable word problem.
[HA_2] actors have no such restriction. That is the whole reason the FP_2 question can have a
universal answer.

## 4. Dead or unpromising approaches (with the reason)

1. **Regular actions.** Pairs (g, h) have the invariant g⁻¹h, giving infinitely many pair orbits
   for infinite G.
2. **Imprimitive wreath actions over a regular base.** W ≀_Y A on W × Y keeps the invariant
   w⁻¹w' on pairs inside a block, whatever A is.
3. **Finite orbits.** A faithful action with all orbits finite embeds G in a product of finite
   groups, so G is residually finite. Inputs such as BS(2,3) or Leary groups that are not
   residually finite need infinite orbits.
4. **Houghton-type twisting by an infinite fibre group.** A permutation of W × (rays) that agrees
   with "translate along rays and multiply fibres" outside finitely many points must translate by
   zero. The complement of a nonzero translate contains infinitely many points (a whole fibre),
   which a finite modification cannot fill. What survives is FSym extended by a group acting with
   infinitely many orbits, which is not even finitely generated.
5. **Perfect orbit quotients of primitive actors.** In a primitive group containing Alt_fin(S),
   every nontrivial normal subgroup contains Alt_fin(S), so it is transitive and the orbit
   partition is trivial (proof in the lemma's route). The lemma needs imprimitive actors.
6. **Wreath-product actors with base normal subgroups.** For C ≀_Y A acting on Z × Y and
   N = N₀^(Y), the orbit kernel is K₀^(Y), where K₀ is the orbit kernel of C ↷ Z/N₀. The problem
   moves to the base actor C, so this is circular.
7. **Röver–Nekrashevych envelopes.** Every finitely generated subgroup of V_d(G), with G finitely
   generated self-similar, has co-r.e. word problem (1.20 lane,
   `rover-nekrashevych-groups-have-co-re-word-problem`). So these envelopes cannot be universal.
8. **Lampshuffler actors FSym(Γ) ⋊ Γ.** These are faithful, highly transitive, with fg point
   stabilizers, and contain any Γ. For infinite Γ they are never finitely presented (Genevois–Tessera
   Thm 1.5: infinitely many h with ⟨τ, hτh⁻¹⟩ not a free product). FP_2 is not settled by that
   theorem. Heuristic against it: their mechanism turns far commutations into free products, and in
   Z/2 ∗ Z/2 the kernel onto Z/2 × Z/2 is infinite cyclic, not perfect. Also H_2 = FSym(Z) ⋊ Z is
   not FP_2 (Brown). Recorded as open and unpromising.
   - Local-derivation attempt (by hand): trying to derive [t_e, t_f] = 1 for far edge transpositions
     from relations inside balls fails for the same reason in every group. The conjugators that move
     f toward e are themselves far transpositions whose commutation with t_e is the thing being
     proved. Houghton groups avoid this because translations supported away from e act as
     conjugators; lampshufflers have no such elements.

## 5. Live cruxes (sharpest first)

- **C1: non-recursively-presented [HA_2] actors exist?** One such actor answers FFWZ Remark 4.16
  (a simple FP_2 group with unsolvable word problem). An uncountable family answers 1.20 part 1
  (the 1.20 lane's target `uncountably-many-fp2-groups-have-faithful-ha2-actions`). Candidate
  mechanism: `perfect-orbit-quotients-of-fp2-actors-are-ha2-actors`, with P a finitely presented
  imprimitive actor and N a non-r.e. perfect normal subgroup. Leary's perfect kernels
  G_L({0}) → G_L(S) are normal in Leary's groups, not in any known actor.
- **C2: the 1.20 lane's alternating restriction groups.** A(G) for G = G_V × (Z ⋉ {0,1}^Z) is
  finitely generated and restricts onto simple groups for 2^ℵ0 minimal subshifts. It is open
  whether the kernels are perfect and whether A(G) is FP_2. If both hold, the Bieri–Strebel
  lemma gives continuum many simple FP_2 groups. That settles 1.20 part 1, not 1.25.
- **C3: universality.** Even with C1, 1.25 needs every countable input inside one [HA_2] actor.
  The fp analogue of this step is the permutational Boone–Higman conjecture, which is open for
  decidable inputs. The FP_2 version has no word-problem obstruction, and no universal mechanism
  is known.

## 6. Next steps for a follow-up lane

- Decide FP_2 for FSym(Γ) ⋊ Γ with Γ one-ended, starting from the Bieri–Eckmann product criterion
  and the relation module of the local presentation. This is a sharp yes/no computation; a yes
  would close C3 through Leary's theorem.
- Look for imprimitive finitely presented actors with many perfect normal subgroups of small
  orbit: labelled Thompson groups (Palmer–Wu) and Houghton groups over graphs with ≥ 3 ends and
  nontrivial fibre actions.
