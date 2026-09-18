# gq-deep-ring-2 board
**Approach** (family: linear characteristic / K-theory; sig "K_2 obstruction for finitary-SL(Q) linear hosts").
Linear hosts SL_X(Q) <= Γ <= SL_X(Q)·Mon(X) (finitary SL plus weighted permutations), the linear analogue of Alt_fin hosts.
**Established** (lane proofs, not independently reviewed):
- 9243184bf `split-finitary-sl-q-extensions-are-not-fp`: a f.g. split Γ = SL_X(Q) ⋊ M (M monomial) is never f.p.
  (St_X(Q) ⋊ M is f.g. with central kernel K_2(Q), which is not f.g.). Kills the Euler host and the Baumslag host
  (SL_(Z^2)(Q) ⋊ Baumslag's fp metabelian group, weights via A ≅ Q^×_{>0}), both f.g. and containing every GL_n(Q).
- 8c25fd25c `weighted-monomial-hosts-of-sl-q-need-wild-stabilizers`: a f.g. host of this shape containing SL_X(Q) has finitely
  many orbits and a point stabilizer whose weight character has non-f.g. image; tame monomial parts keep all entries in Z[1/N].
- 3de0ff8fb `fp-linear-hosts-of-sl-q-have-wild-h3-quotients`: a f.p. Γ between SL_X(Q) and SL_X(Q)·Mon(X) has
  H_3(Γ/SL_X(Q)) not f.g. and does not split (LHS; general form for perfect normal N with non-f.g. H_2(N)_(Γ/N)).
**Needs:** —
**Dead:** f.p. linear hosts with FP_3 or split quotients (the above).
**Sparks (not pursued):** (1) E_(n+1)(R_T): an LHS/K_2 argument via the ideal J of finitary matrices would need the relative
  K_2 of (ρR_T, J) and FP_3 of E_(n+1)(ρR_T/J); unowned while gq-en-ring is down. (2) Does every automorphism of SL_inf(Q) act
  on K_2(Q) through a finite group? If so, part 2 of the H_3 node kills all hosts with a normal SL_inf(Q) and an FP_3 quotient.
