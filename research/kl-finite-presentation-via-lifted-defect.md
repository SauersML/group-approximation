---
rg: 2
id: kl-finite-presentation-via-lifted-defect
kind: route
title: Lift the collapse identity to a free group and kill only the finitely many relators the defect uses
target: kl-counterexample-can-be-finitely-presented
requires: [kl-failure-localizes-to-the-coefficient-subgroup]
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

By the prerequisite, take the counterexample over a finitely generated `A`,
with `deg_t(w) = m != 0` and `1 != a in A` dying in `A_w`.  Death in a normal
closure is a finite identity: in `A * <t>`,

    a  =  prod_{j=1..r} u_j w^{e_j} u_j^{-1} ,      e_j in {±1}.      (*)

Choose a finite-rank free `F` and `phi : F ->> A`, and lift to `F * <t>` the
element `a`, every coefficient of `w`, and every `A`-letter of the finitely
many conjugators `u_j`; write `a~, w~, u~_j`.  The defect

    d  =  a~^{-1} prod_j u~_j w~^{e_j} u~_j^{-1}

lies in `ker(phi * id : F * <t> ->> A * <t>) = <<ker phi>>_{F*<t>}`.  One
element of a normal closure is a finite product of conjugates of finitely
many of its generators, so `d in <<r_1, ..., r_k>>_{F*<t>}` for some
`r_1, ..., r_k in ker phi`.

Put `P = F/<<r_1, ..., r_k>>_F`, finitely presented, with `P ->> A`.  Since
`(F/<<R>>_F) * <t> = (F * <t>)/<<R>>_{F*<t>}`, the defect dies in `P * <t>`,
so (*) holds there with everything lifted.  The image `a_P` is nontrivial —
it maps to `a != 1` in `A` — and dies in `P_{w~}`, while
`deg_t(w~) = m != 0`.

## Where the finiteness actually comes from

Not from the group and not from the word, but from the **defect**: a single
element of a normal closure uses finitely many relators.  Everything else in
the argument is bookkeeping around that one fact.  This is also the reason
the route yields no decision procedure — it selects the relators after being
handed the identity (*), and nothing bounds them in advance.
