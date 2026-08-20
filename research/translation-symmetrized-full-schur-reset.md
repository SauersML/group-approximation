---
rg: 2
id: translation-symmetrized-full-schur-reset
kind: claim
title: One finite translated-pencil group contains and resets the full Schur gate
distinct_from:
  translation-symmetrized-schur-child-reset: that symmetrizes only the Q child and attaches the full packet by an amalgam; this extends every translated copy by its missing P generator.
  schur-packet-head-actuator-generates-over-tail: that embeds one full packet across a head/tail boundary; this places the complete gate and reset in one finite head group.
---

The group `N_f` of `translation-symmetrized-schur-child-reset` admits a
finite extension `Nhat_f` obtained by adjoining, for every `a in F_2^k`, the
missing generator `p_*^(a)`. Copy `a` is then the full Schur packet for the
translated matrix

```text
M_f(x+a)=[[U_f(x+a),e_t],[e_s^T,0]].                    (TFS1)
```

The selector translations extend by

```text
tau_b(p_*^(a))=p_*^(a+b),                               (TFS2)
```

and every corrected branch flip `eta_a:q_*^(a)->Jq_*^(a)` continues to be an
automorphism fixing `p_*^(a)`. Consequently the same finite automorphism
group `W_f` defines a finite ordinary overgroup

```text
Rhat_f=Nhat_f semidirect W_f                            (TFS3)
```

which contains the original full packet `B_f=B_f^(0)`.

Let `D=2^N`. In every exact `J=-1` representation of `Rhat_f`, restriction
to `B_f` lies on the single ray

```text
f(x)=1:  m copies of the unique simple of dimension 2D,
f(x)=0:  m copies of each of the two simples of dimension D,     (TFS4)
```

for one common integer `m`. Conversely every type direction transverse to
this ray has dimension-independent normalized-HS payment after fixed-table
exactification and overlap alignment.

Thus the complete nonlinear gate/reset cell is finite and can be embedded in
one bounded Toeplitz head. The global obstruction is not local amalgam
compatibility: it is returning the scalar `m` through the one-sided tail
without allowing regular stationary flow.
