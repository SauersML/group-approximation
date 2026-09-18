---
rg: 2
id: parity-mark-lies-in-jacobson-monolith-closure-proof
kind: route
title: Kill an odd base element through its compressed image, then read the invariant corner through the central fixed projection
target: parity-mark-lies-in-jacobson-monolith-closure
requires:
  - parity-headed-compressor-kills-mark-in-exact-matrix-models
  - toeplitz-parity-compressor-candidate
  - binary-jacobson-mark-dichotomy-holds-from-rank-two
  - finitary-sign-sector-has-no-kazhdan-low-density
---

**Step 1 (PML1).** Let `p in Lambda` with `chi(p)=1`, and let `N=<<alpha(p)>>_H`. In `H/N` the relation
`t p t^-1=alpha(p)` becomes `t p t^-1=1`, so `p=1`. The relation `q p q^-1=J^(chi(p)) p=J p` then reads `1=J`.
Hence `J in N`.

**Step 2 (`c in L`).** By `toeplitz-parity-compressor-candidate-proof`, `c=s I_4 in EL_4(T)`, with
`s=1+e_00+e_11+e_10+e_01`. Here `s-1` lies in the finitary ideal `F`, so `c-I in M_4(F)` and the symbol of `c` in
`EL_4(F_2[z,z^-1])` is `I`. Thus `c in L`. Also `c != 1`, because `s` transposes the first two head coordinates.
Finally, `alpha(e)=(beta(1)c,0)=c` and `chi(e)=1`.

**Step 3 (PML2).** Let `1 != x in L`. The subgroup `<<x>>_(H_T) cap L` is normal in `L` and contains `x`. By
`binary-jacobson-mark-dichotomy-holds-from-rank-two` (1), `L` is simple, so this intersection is `L`, and it
contains `c`. Step 1 with `p=e` gives `J in <<c>> <= <<x>>`.

**Step 4 (PML3).** Let `pi(J) != 1`.
* By Step 3, `pi` is nontrivial on `L`. So `N_0=ker pi cap EL_4(T)` meets `L` in a proper normal subgroup of the
  simple group `L`, that is, trivially.
* Then `[N_0,L] <= N_0 cap L=1`, so `N_0 <= C_(EL_4(T))(L)=1`, by (2) of the same node.
* Put `N_1=ker pi cap Lambda`. Since `N_1 cap (EL_4(T) x 0)=1`, the projection of `N_1` to `C_2` is injective.
  If `N_1 != 1`, then `N_1={1,(g,1)}` is a normal subgroup of order two, so `(g,1)` is central in `Lambda`.
  Hence `g` is central in `EL_4(T)`, so `g in C(L)=1` and `e in ker pi`.
* Then `pi(c)=pi(t)pi(e)pi(t)^-1=1`, contradicting `pi(L) != 1`. So `pi` is injective on `Lambda`.

**Consequences.** A countable subgroup of `U(R^omega)`, or of `U(prod_omega M_(d_n))`, is hyperlinear. So a
`J`-seeing homomorphism embeds `EL_4(T)` into such a group. Contrapositively, if `EL_4(T)` is not hyperlinear,
every such homomorphism kills `J`.

**Step 5 (PML4).** By FSS6 of `finitary-sign-sector-has-no-kazhdan-low-density`, the generators of `H_T` are
comparable on `L`, so `e_inf` is central in `pi_tau(H_T)''`.
* Then `V_0=e_inf H_tau` is an `H_T`-invariant subspace on which `pi_tau(L)` acts trivially.
* The subrepresentation on `V_0` kills `<<L>>`, and therefore kills `J`, by Step 3. So `pi_tau(J)e_inf=e_inf`, and
  `P_- e_inf=0`.
* Since `e_inf` is central, `P_-` commutes with it and `P_- <= 1-e_inf`. Hence
  `tau((1-J)/2)=<P_- xi,xi> <= <(1-e_inf)xi,xi>`.
* For a general `G`, the same argument uses FSS6 for `G` and the hypothesis `J_G in <<L>>_G` in place of Step 3.

**Step 6 (PML5).**
* **The sector state.** Asymptotic multiplicativity and `J^2=1` give `||phi_n(J)^2-1||_2 -> 0`. On the unit circle,
  `|(1-z)/2-1_(Re z<0)(z)| <= C|z^2-1|`, so `||Z_n-(1-phi_n(J))/2||_2 -> 0`. Therefore
  `omega(g):=lim_n tr(Z_n phi_n(g))=tau(g(1-J)/2)` for every `g`, with no subsequence needed.
* **The limit value.** The projections `pi_tau(P_(F_m))` decrease strongly to the projection onto vectors fixed by
  `union_m F_m=L`, which is `e_inf`. So
  `omega(e_inf)=lim_m <pi_tau(P_(F_m))P_- xi,xi>=<e_inf P_- xi,xi>=0`, by Step 5.
* **The budget.** The limit form of FSS2 gives
  `limsup_n ||R_(Z_n)P_n||_2^2 <= tau(e_inf) omega(e_inf)=0`, and FSS2 states the equality of the right and left
  budgets.
* **Subspaces.** FSS3 converts this into `tr_ad(W_n)->0` for every one-sidedly sector-supported `W_n<=P_n`.

**Scope check.** Steps 1–4 are purely algebraic and use only the relations of `H(alpha,chi)` and the rank-`n`
monolith facts. Steps 5–6 use only FSS2, FSS3 and FSS6, whose hypotheses FSS5 and FSS6 verify for `H_T`.
