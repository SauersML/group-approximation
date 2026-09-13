---
rg: 2
id: sl3z-prime-level-invariant-witnesses-are-complete
kind: claim
title: Every nontrivial irreducible representation of SL_3(F_p) fixes a vector of the block SL_2 or of one of the three cube-class conjugates of the principal SL_2
artifacts:
  - research/artifacts/sl3z-prime-level-witness-completeness-2026-09-13.md
distinct_from:
  sl3z-has-no-invariant-vector-witnesses: that shows no finite family of subgroups of SL_3(Z) is a witness, using mixed levels; this shows that at a single prime level the block SL_2 and the principal SL_2 up to the diagonal outer automorphism already catch every nontrivial irreducible.
---

ESTABLISHED (unreviewed).  Let `p` be an odd prime, `B_2` the block
`SL_2(F_p)`, `Omega = Sym^2(SL_2(F_p))` and `Omega^(t) = d_t Omega d_t^(-1)` with
`d_t = diag(t,1,1)`.  The class of `Omega^(t)` up to `SL_3(F_p)`-conjugacy depends
only on `t mod (F_p^x)^3`.  Then every nontrivial irreducible `rho` of `SL_3(F_p)`
has a nonzero vector fixed by `B_2` or by some `Omega^(t)`:

1. if `rho` is not cuspidal, then `rho^(B_2) != 0`;
2. if `rho` is the irreducible restriction of a cuspidal `pi` of `GL_3(F_p)`,
   then `dim rho^(Omega^(t)) = 2` for all `t`;
3. if `pi|_(SL_3) = rho_1 (+) rho_2 (+) rho_3` (`p == 1 mod 3`, `pi`
   cubic-twist invariant), then `sum over the 3 cube classes c` of
   `dim rho_j^(Omega^(c))` equals `2` for each `j`.

Part 1 is Magee--de la Salle's Step 3 in rank 3, applied to the Jacquet module
for `P_(1,2)`.  Parts 2 and 3 combine the Deligne--Lusztig values with Clifford
theory.

Consequence: the only prime-level representations escaping both the block and
the principal `SL_2` (the four degree-96 representations of `SL_3(F_7)` in the
census of `sl3z-has-no-invariant-vector-witnesses`) are cubic-twist cuspidal
constituents.  Each of them has fixed vectors for another cube-class conjugate
of the principal `SL_2`.  At prime levels the mechanism behind
`sl3z-has-no-invariant-vector-witnesses` is used up.  What remains is
`sl3z-prime-level-sc-needs-cubic-chebotarev-primes`.

Proof: `sl3z-prime-level-invariant-witnesses-are-complete-proof`.
