---
rg: 2
id: deligne-opnorm-sectors-empty-from-hs-defect-gap
kind: route
title: Operator-norm Maslov models are normalized-HS models, so the HS defect gap empties the operator sectors
target: deligne-nontrivial-maslov-opnorm-sectors-are-empty
requires:
  - maslov-mod3-projective-defect-gap
---

Suppose the operator gate fails for `alpha` (the `alpha^2` case is the same,
or follows by `maslov-inverse-sector-symmetry`). Then there are unitaries
`U_n(g)` in `U(d_n)` with

```text
||U_n(g)U_n(h)-alpha(g,h)U_n(gh)||_op -> 0      for every fixed pair g,h.   (OH1)
```

**Unit.** `U_n(e)U_n(e)-alpha(e,e)U_n(e)=U_n(e)(U_n(e)-I)` for normalized
`alpha`, and `U_n(e)` is unitary, so `||U_n(e)-I||_op -> 0`.

**Inverses.** `||U_n(s)U_n(s^-1)-alpha(s,s^-1)I||_op -> 0`, so
`U_n(s^-1)` is within `o(1)` of `alpha(s,s^-1)U_n(s)^*` in operator norm.

**Relators.** Fix the finite presentation `<s_1,...,s_k | r_1,...,r_m>` of
`Gamma=Sp_4(Z)` used in `maslov-mod3-projective-defect-gap`, with the
scalars `lambda_j` of its `alpha`-projective relations (the value of `r_j`
on the canonical unitaries of `C^*(Gamma;alpha)`). Put `X_(n,i)=U_n(s_i)`.
For a word `w=s_(i_1)^(e_1)...s_(i_L)^(e_L)`, induction on `L` with (OH1),
the unit estimate and the inverse estimate gives a scalar `lambda_w` of
modulus one, depending only on `w` and `alpha`, such that

```text
||w(X_n)-lambda_w U_n(ev(w))||_op <= C_w eps_n(w) -> 0,
```

where `eps_n(w)` is the maximum of the defects (OH1) over the finitely many
pairs met by the induction. For `w=r_j`, `ev(r_j)=e` and `lambda_(r_j)` is the
relation scalar `lambda_j`, because both are computed by the same product of
multiplier values that computes `r_j(u)` in the twisted algebra. Hence

```text
||r_j(X_n)-lambda_j I||_op -> 0       (j=1,...,m).
```

**Norm domination.** For every `d x d` matrix `Y`,
`||Y||_(2,tr_d)=(tr_d(Y^*Y))^(1/2) <= ||Y||_op`. So the maximal
normalized-HS relator defect of the unitary tuple `X_n` tends to zero as
`n -> infinity`. This contradicts the uniform positive lower bound `c`
asserted by `maslov-mod3-projective-defect-gap`, whatever the dimensions
`d_n`. Hence neither nontrivial Maslov sector has point-norm models.

**Consequence for the lane.** Through
`deligne-sector-gap-is-exactly-nonhyperlinearity`, the required claim is
equivalent to non-hyperlinearity of `E_3`. So non-hyperlinearity of `E_3`
implies `Rad_MF(E_3)=C_3` and that `E_3` is not MF. The MF-radical goal is
therefore at most as hard as the non-hyperlinearity problem for `E_3`.
Conversely, a proof of the operator gate whose refutation step still works
when operator-norm defects are replaced by normalized-HS defects proves
non-hyperlinearity of `E_3`. A proof that is genuinely easier than that must
use a feature of the operator norm that normalized-HS limits lose.

**Relation to nearby nodes.**

- `deligne-central-radical-from-opnorm-sector-emptiness`: that consumes operator-sector emptiness to put the centre in the MF radical; this supplies operator-sector emptiness from the tracial defect gap by norm domination.
- `deligne-sector-gap-equivalence-proof`: that proves the tracial gap is equivalent to non-hyperlinearity of E_3; this is the one-way transfer from the tracial gap to the operator-norm gate, and so shows non-hyperlinearity of E_3 already forces the MF-radical goal.
