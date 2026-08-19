---
rg: 2
id: literal-mark-quotient-flexibly-stable
kind: claim
title: Flexible permutation stability of the literal marked quotient
distinct_from:
  literal-mark-quotient-mf: That claim asks whether `E/<w>` admits a faithful operator-norm corona model; this asks whether its almost-actions on finite sets are close to genuine actions after flexible enlargement.
  wreath-flexible-hs-stability: That claim is flexible Hilbert-Schmidt (Frobenius) stability of the wreath candidate of the hyperlinear program; this one is flexible *permutation* stability of the literal marked quotient.
  literal-mark-quotient-sofic: That established claim gives permutation microstates for `E/<w>`; this one asks whether its almost-actions are near genuine ones, which soficity does not decide — and which is refuted by combining that claim with the quotient's finite residual.
  literal-mark-quotient-not-stable-in-finite-actions: That established claim is the negation of this one at the weakest stability notion, hence refutes it.
artifacts:
  - notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md
---

The finitely presented group

    E/<w> = (*_{i in I} (Z/2)^8) semidirect_product V
          = V *_{B_1} ((Z/2)^8 semidirect_product B_1)

is flexibly stable in permutations: there is a rate function `rho` such that
every `eps`-almost action on a finite set `Omega` is `rho(eps)`-close, after
enlarging `Omega` to a finite superset, to a genuine action.

## Status: REFUTED (2026-08-14)

This claim is FALSE.  `literal-mark-quotient-not-stable-in-finite-actions`
establishes that `E/<w>` is sofic (`literal-mark-quotient-sofic`) with
nontrivial finite residual (`literal-mark-quotient-finite-residual`), hence not
stable in finite actions — the weakest notion in use — and a fortiori not
flexibly stable.  Nothing further should be attempted here; the correct target
is the negation, which is already established.

*(Any "open but unreachable from any root" warning on this node is expected and
should be read as "refuted by
`literal-mark-quotient-not-stable-in-finite-actions`", not as "unattempted":
the node's only consumer route was invalidated and a refuted claim has nowhere
to hang.  Do not re-hang it.)*

## History, all superseded — kept because two of the reversals are instructive

Read nothing below as a current status; each entry was overturned by the next.

1. **First status, WRONG.**  The node was marked "expected false" on the ground
   that soficity of `E` plus Gohla--Thom refuted flexible stability of `E/<w>`
   directly.  That used the secondary rendering of the theorem
   (`arXiv:2410.02913` "Theorem 1.5") and dropped hypotheses.
2. **Second status, also superseded.**  After `cairn-scout` read the primary
   (`arXiv:2403.09582v2` Theorem 3.13, recorded in
   `gohla-thom-stable-base-nonsofic-extension`), the correct reading was that
   the theorem also needs the base residually finite of finite type and
   satisfying a dimension-2 cosystolic inequality, so soficity of `E` yielded
   only a three-way disjunction: `E/<w>` fails residual finiteness of finite
   type, or fails the cosystolic inequality, or is not stable in finite
   actions.  At that point the claim was genuinely open.
3. **Third status, superseded by the refutation above.**  Soficity of `E/<w>`
   collapsed the disjunction to two, since a sofic group stable in finite
   actions is residually finite (`sofic-stable-implies-residually-finite`), so
   the stability disjunct was not independent of the residual-finiteness one.
4. **Resolution.**  The finite-residual computation showed the
   residual-finiteness disjunct is the one that fails, which both resolves the
   disjunction and, with soficity, refutes this claim outright.  Gohla--Thom
   hypothesis (i) fails for `E/<w>`, so their theorem never applied to the
   pair `(E/<w>, E)` at all.

The cosystolic disjunct was therefore never reached and is moot for this group.
The heuristic recorded while it was live — that `E/<w> = V *_{B_1} ((Z/2)^8
semidirect B_1)` is a nontrivial amalgam acting on a Bass-Serre tree, with
nothing resembling the Bruhat-Tits geometry behind the known cosystolic
inequalities (Kaufman-Kazhdan-Lubotzky, Evra-Kaufman) — was never more than a
heuristic and is not load-bearing anywhere.
