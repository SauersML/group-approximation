# Adversarial check: `almost-all-one-relator-groups-satisfy-boone-higman` (bh-refute, 2026-09-18)

This is a self-chosen rotation item. It bears on BBMZ Problem 5.3(9) and Linton–Nyberg-Brodda 1.8.6.

Verdict: **PASS**. It is a composition: Sapir–Špakulová's embedding theorems, plus
`ascending-hnn-of-free-groups-satisfy-boone-higman`, which was already adversarially checked (ba768a12c).

## Checks at source

The source is Sapir–Špakulová, arXiv:0809.4693v2 (`gq/src/bh-free-05/sapir-spakulova-0809.4693v2.tex`). Each
statement below was extracted by label:
- `thm3`: "A random `k`-generator `1`-relator group, `k >= 3`, can be embedded into an ascending HNN extension of a
  finitely generated free group with probability `1`." This matches the node.
- `thm1` (SS1) and `lm4` (SS2) match the node's criteria. Their "ascending HNN extension of a free group" means a
  finitely generated base, by their definition (l.138, quoted on the node).
- `lm0` (Brown, Thm 4.4) matches criterion (Br).

## Checks on the derivation

- **Composition.** The event "embeds in some `F*_φ`" is contained in the event "BH+". So the lim inf of the
  probability of BH+ is at least 1, in each of the models NR, CR and IC.
- **Priority correction.** Item 1 is genuinely not new, because generic one-relator groups are `C'(1/6)`, hence
  hyperbolic. The node now says so. Items 2 (explicit criteria) and 3 (subgroups) are the content.

## Lesson for general BH

Among one-relator groups, BH is now reduced to the ones outside the ascending class. Those are the groups
whose Magnus–Moldavanskii hierarchy needs an HNN step with both edge groups of infinite index; the
Baumslag–Gersten group is the basic case. So the missing permanence theorem for one-relator BH is exactly
`bh-embeddability-survives-decidable-edge-hnn`, restricted to the edge groups that occur in the hierarchy.
There, Magnus subgroups have decidable membership. That is the named target, not more generic cases.
