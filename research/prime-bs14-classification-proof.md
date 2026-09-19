---
rg: 2
id: prime-bs14-classification-proof
kind: route
title: Apply the minimal-degree table of PSL2 and construct the odd Weil packet
target: prime-bs14-packet-extension-classification
requires: []
---

Because the translation operator has order `p`, the five Iwahori relations
factor any nontrivial extension through `PSL_2(F_p)`.  The smallest
nontrivial complex representation degree is `(p+1)/2` when `p==1 mod 4`
and `(p-1)/2` when `p==3 mod 4`.  Since `4` is a square,
`m=ord_p(4)` divides `(p-1)/2`.  A representation containing the primitive
translation eigenvalue is nontrivial, so its dimension `m` is at least the
corresponding minimal degree.  The first congruence class is impossible;
in the second, divisibility and the lower bound force `m=(p-1)/2`.

The projective diagonal element which sends the translation character
`lambda^a` to `lambda^(4a)` has order `m` in `PSL_2(F_p)`.  Therefore its
matrix has `R^m=I`, forcing the cycle wrap scalar `v=1`.

Conversely, when `p==3 mod 4` and `ord_p(4)=(p-1)/2`, take the odd Weil
constituent of the standard Weil representation.  Its nonzero quadratic
residue characters form one orbit under multiplication by `4`; in the
corresponding eigenbasis the unipotent generator is
`diag(lambda,lambda^4,...,lambda^(4^(m-1)))`, while the diagonal generator
cyclically permutes that basis with wrap one.  The Weyl involution supplies
the remaining Iwahori generator and the Weil formulas verify the five
relations.  This constructs the required extension and completes both
directions.
