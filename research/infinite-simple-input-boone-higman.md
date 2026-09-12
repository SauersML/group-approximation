---
rg: 2
id: infinite-simple-input-boone-higman
kind: claim
title: Every infinite finitely generated computably presented simple group embeds in a finitely presented simple group
distinct_from:
  boone-higman-conjecture: that quantifies over all finitely generated groups with solvable word problem; this restricts to infinite computably presented simple inputs, although Thompson's theorem makes the restriction exactly equivalent.
  boone-higman-thompson-simple-envelope: that established theorem embeds an arbitrary decidable-word-problem group into an infinite finitely generated computably presented simple group; this asks for the missing upgrade of that simple group to a finitely presented simple overgroup.
  simple-envelope-forces-solvable-word-problem: that proves decidability for subgroups of finitely presented simple groups; this asks for the converse embedding only on infinite computably presented simple inputs.
---

**OPEN.** Let `S` be an infinite, finitely generated, computably presented
simple group. Then there is a finitely presented simple group `H` and an
embedding `S <= H`.

By [[boone-higman-iff-infinite-simple-inputs]], this is not merely a special
case of [[boone-higman-conjecture]]: it is exactly equivalent to it. Thus a
proof here closes Boone--Higman, and any failure of Boone--Higman already has
an infinite simple counterexample of this form.

Current-status check, 2026-08-30: Fournier-Facio--Wu--Zaremsky,
*Abstract twisted Brin--Thompson groups*, arXiv:2603.24687v2, Conjecture 1.4,
still states the full Boone--Higman assertion as a conjecture. Belk--Bleak--
Matucci--Zaremsky, *Hyperbolic groups satisfy the Boone--Higman conjecture*,
Duke Math. J. 175 (2026), 1519--1592,
doi:10.1215/00127094-2025-0055, proves the hyperbolic subclass, not this
universal statement.
