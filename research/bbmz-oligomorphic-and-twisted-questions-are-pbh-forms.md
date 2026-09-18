---
rg: 2
id: bbmz-oligomorphic-and-twisted-questions-are-pbh-forms
kind: claim
title: BBMZ Question 1.5 is equivalent to the permutational Boone--Higman conjecture, and BBMZ Question 1.6 is equivalent to BFFHZ Question 3.4, while its abstract reading is answered by FFWZ
distinct_from:
  permutational-boone-higman-conjecture: that is the conjecture for type (A) actors, which ask only for finitely generated point stabilizers and finitely many orbits of pairs; this proves it equivalent to the stronger-looking oligomorphic form that BBMZ asked, with finitely generated stabilizers of all finite subsets.
  bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh: that proves BFFHZ's equivalences among Question 3.4, high transitivity and PBH for finitely presented simple groups; this adds BBMZ Question 1.6, in its faithful reading, to that list.
  boone-higman-implies-relative-permutational-bh: that is FFWZ Theorem C; this records that it answers the abstract reading of Question 1.6 and that the gap to the faithful reading is kernel removal.
  permutational-boone-higman-iff-full-cantor-hosts: that is the equivalence with finitely presented full clopen-transitive Cantor hosts; this uses the same hosts to upgrade type (A) to oligomorphic with finitely presented finite-set stabilizers.
---

**ESTABLISHED** by `bbmz-oligomorphic-twisted-questions-proof` (lane proof, elementary, assembling
landed nodes; not independently reviewed). No priority claimed; Zaremsky's text, where type (A)
was introduced after these questions were posed, was not re-read for a remark to the same effect.

## The questions

Belk--Bleak--Matucci--Zaremsky, *Hyperbolic groups satisfy the Boone--Higman conjecture*,
arXiv:2309.06224v3, §1.3 (TeX, read on MSI):
- **Question 1.5.** "Does every finitely presented group with solvable word problem embed in a
  finitely presented oligomorphic group with finitely generated stabilizers of finite subsets?"
- **Question 1.6.** "Does every finitely presented simple group embed in a finitely presented
  (simple) twisted Brin--Thompson group?"

Here a group of permutations of `S` is *oligomorphic* when it has finitely many orbits on `S^n`
for every `n` (Cameron), and the twisted Brin--Thompson group `SV_G` is defined by BBMZ for a group
`G` acting faithfully on `S`.

## Statement

1. **Oligomorphic upgrade.** If a finitely generated group `H` lies in `B_A`, then `H` embeds in a
   finitely presented group acting faithfully and oligomorphically on a set, with every
   stabilizer of a finite subset finitely presented.
2. **Question 1.5.** A positive answer to Question 1.5 is equivalent to
   `permutational-boone-higman-conjecture`.
3. **Question 1.6, faithful reading.** A positive answer to Question 1.6, with twisted
   Brin--Thompson groups taken for faithful actions as in BBMZ's definition, is equivalent to each
   of: every finitely presented simple group lies in `B_A`; BFFHZ Question 3.4 (every finitely
   presented simple group embeds in a finitely presented simple MIF group); Zaremsky Question
   5.13(ii); and "Boone--Higman implies permutational Boone--Higman"
   (`bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh`).
4. **Question 1.6, abstract reading.** If non-faithful actions are allowed, the answer is yes:
   by FFWZ Theorem C every finitely presented simple group sharply embeds in the pair
   `(G, ker(G ↷ S))` of a type [A_2] action, hence embeds in the finitely presented abstract
   twisted Brin--Thompson group `SV_G`. That group is not simple when the action has a kernel
   (it is relatively simple over `SK_G`), so the parenthetical "(simple)" of Question 1.6 is not
   met.
5. **The gap between the readings** is, for each finitely presented simple group, removal of the
   kernel of its FFWZ Theorem C actor: by `a2-kernel-removal-iff-image-satisfies-pbh` the kernel
   is removable exactly when the action image lies in `B_A`.

So Question 1.5 is the permutational Boone--Higman conjecture in disguise, and Question 1.6 is
BFFHZ Question 3.4 in disguise. Neither is settled here; both are now attached to the nodes that
carry them.
