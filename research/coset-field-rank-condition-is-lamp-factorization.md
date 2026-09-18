---
rg: 2
id: coset-field-rank-condition-is-lamp-factorization
kind: claim
title: The coset-field rank condition is equivalent to no scalar lamp polynomial matrix factoring through a smaller free module over the Laurent lamp group ring
distinct_from:
  kun-thom-coset-field-crossed-product-has-the-rank-condition: that is the open question itself; this is an exact reformulation of it over the group ring of the Laurent lamp group, proved by a two-sided Ore clearing.
  rf-lamps-preserve-stable-finiteness-for-arbitrary-actions: that proves stable finiteness of the lamp group ring; this identifies the extra statement about scalar multiples w I_d that the localized ring needs and that stable finiteness does not give.
  finite-field-point-models-give-the-rank-condition: that is one sufficient certificate by point evaluation; this is an equivalence valid for every field, group and G-set.
---

Let `k` be a field, `G` a group acting on a set `H`, and put

    L = k[x_c^(+-1) : c in H],   K = Frac(L) = k(x_c : c in H),
    T = L semidirect G = k[Z wr_H G],   R = K semidirect G,

with `g . x_c = x_(gc)`. Then the following are equivalent for each `d > r >= 0`.

1. Some `d x r` matrix `A` and `r x d` matrix `B` over `R` have `AB = I_d`.
2. Some nonzero `w in L` and matrices `A_0` (`d x r`), `B_0` (`r x d`) over `T` have `A_0 B_0 = w I_d`.

Hence `R` has the rank condition if and only if no `w I_d`, with `w` a nonzero Laurent lamp polynomial,
factors through `T^r` for any `r < d`. In particular `R` has the rank condition as soon as there is a
unital ring map `phi : T -> M` into a ring with a normalized Sylvester matrix rank function under which
every nonzero `w in L` is full, `rk(phi(w)) = 1`.

The same holds with `H` replaced by `H x {1,...,m}` (m variables per coset). For the Kun--Thom pair,
`k = F_p` and `H = G/Gamma`, this turns `kun-thom-coset-field-crossed-product-has-the-rank-condition` into a
statement about the group ring of the lamp group `Z wr_(G/Gamma) G`, whose stable finiteness is already known.
