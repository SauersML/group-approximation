---
rg: 2
id: mod3-twisted-fibre-llp-forces-f2xf2-llp
kind: claim
title: LLP of the mod-three twisted fibre of Sp4(Z) forces LLP of C*(F2 x F2) and of both parabolic group algebras
distinct_from:
  sp4-mod3-twisted-fibres-have-llp: that is the open lifting question (TF3) itself; this is an implication from (TF3) to LLP of explicit untwisted subgroup algebras, among them the LLP half of Fournier-Facio--Willett Question 1.6.
  sp2g-z-full-c-star-algebra-has-llp: that open claim is the untwisted fibre, whose Attempts record the F2 x F2 calibration through ordinary subgroup permanence; this gets the same calibration from the twisted fibre alone, where subgroup permanence gives only twisted subgroup algebras until the multiplier is untwisted.
  twisted-c-star-opposite-inverts-cocycle: that identifies the alpha and alpha^2 fibres as opposite algebras; this proves the implication for both fibres directly and does not use that identification.
artifacts:
  - research/artifacts/sp4-mod3-twisted-fibre-f2xf2-calibration-2026-09-16.md
---

**CLAIM.**  Let `alpha` be the `mu_3`-valued multiplier of Deligne's triple
cover `1 -> Z/3 -> E_3 -> Sp_4(Z) -> 1` (`sp4-mod3-twisted-fibres-have-llp`).
Let `A` be `C^*(Sp_4(Z); alpha)` or `C^*(Sp_4(Z); alpha^2)`.  Let `K` be a
subgroup of one of the three groups of
`deligne-multiplier-trivial-on-sl2xsl2-and-parabolics`:

- the block-diagonal `SL_2(Z) x SL_2(Z)`;
- the Siegel parabolic `P_S(Z) = Sym_2(Z) x| GL_2(Z)`;
- the Klingen parabolic `P_K(Z) = N(Z) x| ({+-1} x SL_2(Z))`.

Then there are an injective unital *-homomorphism `j : C^*(K) -> A` and a ucp
map `E : A -> C^*(K)` with `E o j = id`.  Moreover `j o E` is a conditional
expectation onto `j(C^*(K))`.  Consequently:

```text
if A has Kirchberg's local lifting property, then C^*(K) has it.   (CAL-TF3)
```

The LLP is used in its local form: every ucp map into a quotient `B/I` lifts
ucp on each finite-dimensional operator system (artifact, Lemma 7.4).

**Instances.**  (TF3) implies the LLP of each of the following:

1. `C^*(F_2 x F_2)`.  Take the Sanov subgroup
   `< [[1,2],[0,1]], [[1,0],[2,1]] >` in each block.  This instance uses only
   the splitting of the triple cover over products of free subgroups.  It
   needs no presentation of `SL_2(Z)`.
2. `C^*(SL_2(Z) x SL_2(Z))`.
3. `C^*(Sym_2(Z) x| GL_2(Z))`.
4. `C^*(N(Z) x| ({+-1} x SL_2(Z)))`.
5. `C^*(E)`, for the index-two subgroup `E = N(Z) x| S_2(Z)` of `P_K(Z)`.
   This is the Klingen extension of another agent's in-flight Klingen
   central-quotient work, which had not landed when this node was checked
   (artifact, remark 9.5).

**Why it matters.**

- LLP of `C^*(F_2 x F_2)` is the LLP half of Fournier-Facio--Willett
  Question 1.6, arXiv:2603.18456v2, p. 6: "Does `F_2 x F_2` have the (L)LP?"
  That quote is taken from `research/artifacts/sp4-llp-decide-2026-09-13.md`,
  section 0, and was not re-read in this session.
- So any positive proof of (TF3) settles that half of Question 1.6.  This
  holds whatever the untwisted fibre `sp2g-z-full-c-star-algebra-has-llp`
  does.  The same applies to the mouth `nonhyperlinear-from-odd-maslov-fibre-llp`,
  which uses (TF3) without the untwisted fibre.
- Contrapositively, an LLP failure for any listed algebra, or for any other
  subgroup algebra of the three groups, refutes (TF3).
- The target's last Attempt calls the twisted subgroup fence inert because no
  twisted-algebra LLP failure is published.  On these subgroups the twisted
  subgroup algebras are untwisted group algebras.  So the fence needs only an
  untwisted LLP failure there.

**Not claimed.**

- Nothing here refutes (TF3), and there is no converse.
- The subgroups cannot be taken of finite index.  By (DTC2) of
  `deligne-triple-cover-fd-central-invisibility`, `alpha` survives on every
  finite-index subgroup (artifact, remark 9.3).
- Instance 5 is a consequence of (CAL-TF3) only.  Remark 9.5 links it to the
  in-flight Klingen central-quotient constraints.  That link was not
  re-verified, and nothing here uses it.

The proof is `mod3-twisted-fibre-llp-forces-f2xf2-llp-proof`.
