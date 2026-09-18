---
rg: 2
id: fpbs-malnormal-exhaustion-blind-to-cost
kind: claim
title: Malnormal exhaustion is shared by F_inf, so Gamma_mal methods must consume the forced stage relations
distinct_from:
  fpbs-malnormal-subgroup-relations-finite-contacts: that is a counting obstruction for one repair family inside a malnormally anchored class; this exhibits a calibration world with the same lattice hypotheses and infinite cost, killing every lattice-only method at once, and names the separating datum.
  fpbs-locally-free-free-actions-have-finite-cost: that is the open finiteness statement for locally free groups with finite c*; this is an established calibration that any proof of it for Gamma_mal must use c* through the kernel of H_n * <t> -> H_m.
artifacts:
  - research/artifacts/fpbs-malnormal-exhaustion-calibration-2026-09-17.md
---

**ESTABLISHED.**

1. **Calibration world.** Let `W1 = ker(F_2 -> Z)`, with `a -> 0` and
   `b -> 1`. It is locally free and not finitely generated. Every finitely
   generated subgroup lies in a finitely generated malnormal stage (a free
   factor), so wq-normal hulls and Gaboriau chains of finitely generated
   subgroups never leave a stage. `W1` is normal in `F_2` with quotient `Z`,
   and conjugation by `b` shifts the stages. Every free p.m.p. action of `W1`
   has cost infinity.
2. **Forced relations.** Let `G` be free of finite rank, `H <= G` malnormal
   and finitely generated, and `t` in `G \ H` with `<H, t> = G`.
   - If `rank G = rank H + 1`, the natural map `H * <t> -> G` is injective.
   - If `rank G <= rank H`, it has nontrivial kernel, and every nontrivial
     kernel element has at least 3 `t`-letters.
   - The bound 3 is attained at the stage pairs of `Gamma_mal`: the relation
     `t a t^{-2} b_{m-1}^{-1}` with `t = b_m`.

**Consequence.** Consider an argument whose `Gamma_mal`-specific inputs are
only malnormal exhaustion, absence of chains or anchors, finite contacts, a
cyclic finitely generated overgroup with a shift, and H. No such argument
proves that the free costs of `Gamma_mal` are finite. If one did, it would
refute H via `W1`.

Relative to the list (P1)–(P7) of the artifact, the only input separating
`Gamma_mal` from `W1` is the uniform rank bound. At a stage pair, that bound is
exactly the nontrivial kernel in item 2, which is the coset-cycle data that
detour packing consumes. `W1` also has malnormal finitely generated pairs of
equal rank, for example `<x_0, x_1 x_0 x_1^{-2}> < <x_0, x_1>`, and these carry
3-letter relations. So the separating datum is relations at every step of a
uniform-rank exhaustion, not relations at some malnormal pair.

**Proof.** Artifact sections 1–3:
- item 1 is Reidemeister–Schreier plus [G00] Prop VI.9;
- item 2 follows from Hopficity and rank invariance of free groups, plus a case
  check of relators with at most 2 `t`-letters against malnormality.

## Attempts

- **2026-09-17, audit (three referee lenses: math, hypotheses and citations,
  calibration).** All three survived. Checked: the Reidemeister–Schreier basis
  of `W1` and [G00] Prop VI.9 at source; Hopficity and rank invariance in
  Proposition 3(a)(b); the case check in 3(c), including the implicit steps
  that cyclic reduction adds no `t`-letters and that `t^e = 1` is excluded by
  torsion-freeness; malnormality of `<a, b a b^{-2}>` in `<a, b>` from its
  Stallings graph; sharpness via `t a t^{-2} b_{m-1}^{-1}`. Caveats recorded:
  the "only separating input" sentence is relative to (P1)–(P7); and height-3
  tower descent is a further open route not listed among the survivors
  (`Gamma_mal` lies in `T_2`, `W1` is not in `T`), consistent with the thesis.
