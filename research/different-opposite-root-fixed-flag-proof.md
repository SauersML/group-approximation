---
rg: 2
id: different-opposite-root-fixed-flag-proof
kind: route
title: Use the characteristic fixed flag to exclude a two-letter reverse-Hecke return
target: two-distinct-reverse-hecke-roots-cannot-return
requires:
  - one-nonnormal-dressing-cannot-preserve-moving-full-gram
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
---

Let `V` be the free rank-seven `R`-module on the actor coordinates.  For a
subgroup `K<=GL(V)`, set

```text
C_0(K)=0,
C_(r+1)(K)={v:(g-1)v in C_r(K) for every g in K}.       (DFP1)
```

This construction is intrinsic: if `nKn^(-1)=K`, induction on `r` gives
`nC_r(K)=C_r(K)`.  For `K=L_0`, the directed list `(DOR1)` gives

```text
C_1=<e_2,e_7>,
C_2=C_1+<e_4,e_8>,
C_3=C_2+<e_5,e_9>,
C_4=C_3+<e_6>.                                        (DFP2)
```

Indeed a vector is fixed at the first stage precisely when all coordinates
which occur as sources in `(DOR1)` vanish.  Applying the same test modulo
the preceding term successively gives `(DFP2)`.  The computation is over
`F_2`; scalar extension to `R` preserves the kernels and inverse images
because `R` is a free `F_2`-module.

Write `ell(j)` for the first index with `e_j in C_(ell(j))`.  Every edge
`s->t` in `(DOR1)` satisfies `ell(s)>ell(t)`.  Its bare reverse root
`Y_(s,t)(a)=I+aE_(s,t)` therefore sends

```text
e_t |-> e_t+a e_s.                                    (DFP3)
```

Take two distinct edges with `ell(t_1)<=ell(t_2)`, and let `Y` be
their product in either order.

Test `e_(t_1)` modulo `C_(ell(t_1))`.

* If `ell(t_1)<ell(t_2)`, the higher-target letter has no input coordinate
  at level `ell(t_1)`.  If it occurs first it fixes `e_(t_1)`; if it
  occurs second, the only possible cross term requires `t_2=s_1` and lies
  in the independent, still-higher coordinate `e_(s_2)`.  In either order
  the nonzero term `a e_(s_1)` survives above the tested filtration term.
* If the levels agree and `t_1!=t_2`, the second letter does not act on
  `e_(t_1)` in either order: its target is different, and it cannot target
  `s_1` because `ell(s_1)>ell(t_1)=ell(t_2)`.  Again
  `a e_(s_1)` survives.
* If `t_1=t_2`, then
  `Ye_(t_1)=e_(t_1)+a e_(s_1)+b e_(s_2)` in either order: neither source
  can equal the common lower-level target.  Distinct edges with the same
  target have distinct sources, so freeness of the basis forces `a=b=0`.

In the first two cases preservation of `C_(ell(t_1))` forces `a=0`.
Testing `e_(t_2)` after that forces `b=0`.  Thus a two-letter product made
by reversing two distinct displayed Hecke arrows preserves the
characteristic flag only when both letters are trivial.  Every normalizer
of `L_0` preserves that flag by `(DFP1)`, proving `(DOR6)`.

Finally, equality
`y e_(L_0,lambda_0)y^(-1)=e_(L_0,lambda_0)` implies equality of the finite
Fourier supports and hence `yL_0y^(-1)=L_0`.  The transporter torsor then
excludes the proposed bare-reverse correction at the full-Gram stage.  This
does not conflict with the external normalizers from
`signed-hecke-normalizer-has-eight-external-root-returns`, whose two
coefficient roots pass through a spare coordinate rather than reversing
two arrows in `(DOR1)`.

