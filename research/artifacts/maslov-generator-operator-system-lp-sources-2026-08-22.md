# Primary-source certificate for the Maslov generator-system LP audit

The operator-system inputs used in
`maslov-generator-complete-order-model-is-llp-strength` are taken from:

1. A. S. Kavruk, V. I. Paulsen, I. G. Todorov, M. Tomforde,
   *Quotients, exactness, and nuclearity in the operator system category*,
   Advances in Mathematics 235 (2013), 321--360,
   https://arxiv.org/abs/1008.2811.

   - The operator-system lifting property is equivalent to
     `S tensor_min B(H)=S tensor_max B(H)` for all Hilbert spaces `H`.
   - Their enough-unitaries multiplicative-domain proposition promotes the
     corresponding tensor equality from `S subset A` to `A`.
   - A system containing enough unitaries has its ambient generated algebra
     as C-star envelope (the same multiplicative-domain argument).

2. A. S. Kavruk, *Nuclearity related properties in operator systems*,
   Journal of Operator Theory 71 (2014), 95--156,
   https://arxiv.org/abs/1107.2133.

   - Theorem labelled `thm lp-quotient` in the source: a quotient of a
     finite-dimensional lifting-property operator system by a null subspace
     again has the lifting property.
   - The coproduct proposition in Section 8: a finite coproduct has the
     lifting property exactly when its factors do.
   - The same paper records that `C_u^*(S)` has LLP iff finite-dimensional
     `S` has LP.  The present argument uses the stronger relation supplied by
     enough unitaries in the *specific* C-star envelope `A_alpha`, rather than
     confusing `C_u^*(S_alpha)` with `A_alpha`.

The last distinction is load-bearing: LLP does not generally pass to C-star
quotients.  The proof instead uses the tensor equality on `S_alpha` and the
enough-unitaries extension directly inside `A_alpha`.

