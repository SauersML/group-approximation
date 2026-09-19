---
rg: 2
id: thompson-f-amenability-unprovable-in-elementary-arithmetic
kind: claim
title: The Følner sentence of Thompson's group F is not provable in elementary arithmetic, even with every true Π1 sentence added as an axiom
distinct_from:
  thompson-f-folner-function-exceeds-every-tower: that is Moore's lower bound on the size of Følner sets; this turns it into a statement about proofs of every strength up to elementary arithmetic, constructive or not, with every true Π1 fact available.
  thompson-f-is-amenable: that is the open problem; this is unconditional (it holds whether F is amenable or not) and kills one class of proofs of it.
  folner-functions-of-fp-amenable-groups-have-no-recursive-bound: that is Gromov's question over all finitely presented amenable groups; this concerns one group and the proof-theoretic strength needed for it.
  decidable-amenable-groups-have-no-recursive-folner-bound: that builds groups with fast Følner functions; here it serves only as a calibration showing this kill does not separate F from elementary amenable groups.
---

**ESTABLISHED** by `thompson-f-amenability-unprovable-in-elementary-arithmetic-proof`,
unrefereed. Family: quantifier-shift (the arithmetic form of the statement).

## Statement

Fix a finite symmetric generating set `Γ` of `F`. Let `C > 1` be Moore's constant for `Γ`
(`thompson-f-folner-function-exceeds-every-tower`), and fix an integer `c >= C`. Code elements
of `F` by natural numbers through an elementary enumeration of normal forms, and code finite
sets canonically, so that the coded set `A_a` satisfies `|A_a| <= a`. Put

```text
R_Γ(n, a)  :⟺  A_a ≠ ∅ and  Σ_(γ∈Γ) |A_a γ △ A_a|  <  c^(-n) |A_a|      (Moore's definition)
g_Γ(n)     :=   µa R_Γ(n, a)
Føl_Γ      :=   g_Γ↓   (the Π2 sentence ∀n ∃a R_Γ(n,a), written as totality of the search)
```

`R_Γ` is elementary (the word problem of `F` is solvable in polynomial time on normal forms), and
by Følner's criterion `Føl_Γ` is true iff `F` is amenable.

**Theorem.** Let `T = IΔ0 + Exp + Th_Π1(N)`, elementary arithmetic together with every true
Π1 sentence. Then `T ⊬ Føl_Γ`. The same holds for every sentence `τ` with
`IΔ0 + Exp ⊢ τ → Føl_Γ` (for example `∀m ∃A (A is 1/m-Følner)`), and for `EA` in place of
`IΔ0 + Exp`.

This is unconditional. If `F` is not amenable, `Føl_Γ` is false and `T` is sound. If `F` is
amenable, the proof below shows that a `T`-proof would bound `g_Γ` by a fixed tower `exp_k`,
which Moore's theorem forbids.

## The class this kills

- *Class:* every argument for the amenability of `F` whose Π2 content can be carried out in
  elementary arithmetic. The argument may be non-constructive: counting, pigeonhole, averaging,
  probabilistic existence over finite sets, and case splits are all allowed. It may use
  arbitrary true Π1 facts as black boxes, for example computer-verified finite inequalities,
  consistency statements, or finite Ramsey instances of Π1 form.
- *Invariant:* the growth class of the Skolem function of the Følner sentence, set against the
  class of provably recursive functions of the proof system.
- *Step where every member dies:* witness extraction. The proof makes the search `g_Γ`
  provably total, so `g_Γ` is Kalmár elementary and `<= exp_k`. Moore's tower
  `|A| >= exp_n(0)` for `c^-n`-Følner `A` is not elementary.
- This formalizes and strengthens the root's attempt "Explicit Følner families". That attempt
  excluded families of bounded recursive complexity. This excludes proofs of bounded strength,
  whether or not they exhibit a family.

## Calibration: what this does not say

- *It is not evidence against amenability.* Take `U(n) = exp_n(0)` in
  `decidable-amenable-groups-have-no-recursive-folner-bound`. That gives a finitely generated
  elementary amenable group `Δ_U` with solvable word problem whose Følner function exceeds
  `C U(Cn)` infinitely often, for every `C`. The same witness extraction shows its Følner
  sentence is not `T`-provable either. So the kill measures only Følner growth, and it
  cannot separate `F` from elementary amenable groups.
- *It depends on the arithmetic form: the Ore and Ramsey forms escape.* Two equivalent Π2 forms
  of amenability are in the graph.
  - The Ore condition for `K[F]` (`thompson-f-amenable-iff-group-ring-is-ore`). By
    `ore-radius-function-bounds-folner-radius`, the translation to Følner sets iterates
    `τ(R) = R + Ω(R)` a factorial number of times.
  - Moore's Ramsey form (`moore-ramsey-criterion-for-amenability`). The Towsner bound
    `Føl <= 5^(R^(2p)(1))` iterates the Ramsey function `Θ(log 1/ε)` times.

  In both cases an elementary witness function translates only into a tower-type Følner bound.
  That is exactly what Moore's theorem permits. So an elementary-arithmetic proof of the Ore
  sentence, or of the Ramsey sentence, is not excluded. These are the same two survivors the
  graph records, from different directions: exponential Ore radius is not excluded
  (`thompson-f-ore-radius-function-is-not-quasi-polynomial`), and an elementary `R_F` is not
  excluded (`thompson-f-ramsey-function-iterates-reach-towers`). The gate out of this kill is
  therefore precisely a Π2 form whose conversion to Følner sets costs a tower.
- *The next rung is open.* `IΣ1` proves the totality of every primitive recursive function,
  including towers, so Moore's bound says nothing against an `IΣ1`-proof. Killing proofs in
  `IΣ1`, `PRA` or `WKL0` would need a non-primitive-recursive lower bound on `Føl_F`, for
  example Moore's recursion with each exponential step replaced by a tower. No such bound is
  known.

## Remark (not load-bearing)

B. Eastaugh, arXiv:1807.10022v1, p. 11, reports from Simpson and Smith (1986) that "WKL∗ is
conservative over a proper subtheory of PRA, known as I∆0 + exp". If this conservativity
covers Π2 sentences, as the standard statement (Simpson, SOSOA §X.4) does, then the theorem
extends to `WKL0*`, so proofs using weak König's lemma compactness over `RCA0*` die at the
same step. The level of that conservativity was not read at source, so the extension is not
claimed.
