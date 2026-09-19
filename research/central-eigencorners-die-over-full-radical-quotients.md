---
rg: 2
id: central-eigencorners-die-over-full-radical-quotients
kind: claim
title: Over a perfect group whose central quotient has full MF radical, every exact central eigencorner of a corona representation is fixed; so finite central kernels are invisible, and Thompson's T is full exactly when one rotation centralizer is
distinct_from:
  mf-group-with-order-two-center-has-mf-central-quotient: that goes from an MF group G to an MF quotient G/<c> for c of order two, by making the involution exact; this goes the other way at the level of radicals (full G/<c> gives full G), for c of any finite order, and in its item 1 for c of infinite order provided an exact eigencorner is handed over.
  commutant-projection-extraction: that asks whether the eigencorner exists at all; this assumes one and shows what it forces.
  lifted-thompson-t-mf-radical-dichotomy: that proves full T-bar gives full C_T(r_k) and full T; item 3 here proves the converse direction from T to C_T(r_k), which the dichotomy does not give.
---

**ESTABLISHED (written proof; not Lean-verified).**  Proof route:
`central-eigencorners-die-over-full-radical-quotients-proof`.

`Q` is a norm matrix corona `prod_n M_(k_n) / (+)_n M_(k_n)`, a *corona
representation* of a group is a homomorphism into `U(Q)`, and `Rad` is the MF
radical.  "`H` has full radical" means `Rad(H) = H`, that is, every corona
representation of `H` is trivial.

Let `G` be a countable **perfect** group, `c in Z(G)` a central element, and
suppose that `G/<c>` has full radical.

1. **(Eigencorner lemma.)**  Let `rho : G -> U(Q)` be a corona
   representation.  Let `P in rho(G)' ∩ Q` be a projection and `lambda in C`
   with `rho(c) P = lambda P`.  Then `rho(g) P = P` for every `g in G`.  In
   particular, if `P != 0` then `lambda = 1`.
2. **(Finite central kernels.)**  If `c` has finite order, then `G` has full
   radical.
3. **(Isolated spectrum.)**  For every corona representation `rho` of `G`,
   no point of `sp(rho(c)) \ {1}` is isolated in `sp(rho(c))`.  Moreover,
   `rho(c)` is a scalar only when `rho` is trivial.
4. **(Thompson's T.)**  For every `k >= 0`, the group `T` has full radical if
   and only if the rotation centralizer `C_T(r_k)` has full radical.  Here
   `r_k` is the rotation by `2^(-k)`.

## What this changes

- **Item 4 is new two-way information about Thompson's `T`.**  Consider a
  proof that `T` is not MF.  By item 4 it can be run in any single rotation
  centralizer `C_T(r_k)`, and conversely.  Now combine this with item 3 of
  `lifted-thompson-t-mf-radical-dichotomy`, which gives "`C_T(r_k)` MF for
  one `k` implies `T̄` MF".  Then the lifted group `T̄` differs from `T`
  only at the level where `rho(z)` has infinite order and its spectrum away
  from `1` is perfect.  Item 3 says this.
- **Item 1 isolates the whole remaining difficulty of the torsion-free seed
  `T̄`.**  That difficulty is the *existence* of an exact eigencorner of
  `rho(z)` in the relative commutant.  It is
  `lifted-thompson-t-centre-has-commutant-eigencorners`, an instance of
  `commutant-projection-extraction`.  See the route
  `lifted-thompson-t-not-mf-via-central-eigencorners`.
- The mechanism has no Kazhdan input.  It is the conjugate-tensor trick of
  `mf-group-with-order-two-center-has-mf-central-quotient-proof`, applied
  inside a corner instead of on a sign splitting.
