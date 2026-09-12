---
rg: 2
id: two-distinct-reverse-hecke-roots-cannot-return
kind: claim
title: Two bare roots reverse to distinct Hecke arrows cannot return to the Hecke normalizer
invalidates:
  - two-bare-reverse-hecke-roots-cancel-whitehead-gauge
artifacts:
  - research/different-opposite-root-fixed-flag-proof.md
distinct_from:
  paired-critical-opposite-roots-return-only-trivially: that treats two coefficients in the same reverse root subgroup by root additivity and a two-by-two block calculation; this treats bare reverse roots for two distinct displayed Hecke arrows by the characteristic fixed-space filtration.
  signed-hecke-normalizer-has-eight-external-root-returns: that finds eight genuine external constant normalizers and realizes them as two-channel coefficient commutators through a spare coordinate; those coefficient roots are not a bare pair obtained by reversing two displayed Hecke arrows, which is the narrower menu fenced here.
  one-nonnormal-dressing-cannot-preserve-moving-full-gram: that proves one nonnormal relative correction cannot preserve the full Gram; this excludes the first two-letter correction made specifically from two bare reverse-Hecke roots.
---

**ESTABLISHED BARE-REVERSE TWO-EXIT NO-GO.**  Use the actor basis

```text
(2,4,5,6,7,8,9)
```

and orient the ten displayed roots of `L_0` by their action on basis
vectors:

```text
6->5, 5->4, 4->2, 8->2, 9->4,
9->2, 9->7, 5->7, 6->7, 6->8.          (DOR1)
```

The intrinsic fixed-space filtration of this action is

```text
F_1=<e_2,e_7>,
F_2=<e_2,e_7,e_4,e_8>,
F_3=<e_2,e_7,e_4,e_8,e_5,e_9>,
F_4=R^7.                                      (DOR2)
```

It is characterized recursively by

```text
F_(r+1)={v:(g-1)v in F_r for every g in L_0},          (DOR3)
```

after scalar extension from `F_2` to
`R=L_(F_2)(1,2)`.  Consequently every element normalizing `L_0` preserves
all four terms.

For a directed edge `s->t` in `(DOR1)`, its bare reverse root is

```text
y_(s,t)(a)=I+aE_(s,t),                                 (DOR4)
```

which sends `e_t` to `e_t+a e_s` and strictly raises filtration degree.
Let `e_1=(s_1->t_1)` and `e_2=(s_2->t_2)` be distinct displayed edges.
If

```text
y=y_(s_2,t_2)(b)y_(s_1,t_1)(a)                        (DOR5)
```

preserves `(DOR2)`, examine a basis vector at the least filtration level
among `t_1,t_2`.  If the levels differ, its first raised coordinate forces
the coefficient on the lower-level exit to vanish.  If the levels agree
but `t_1!=t_2`, the two letters affect different basis vectors.  If
`t_1=t_2`, their raised coordinates `e_(s_1),e_(s_2)` are distinct because
the edges are distinct.  In all cases the relevant coefficient vanishes;
then the other letter is tested in its own least filtration term and its
coefficient vanishes too.  Hence

```text
y in Norm(L_0)  implies  a=b=0.                        (DOR6)
```

Normalizer membership for the signed Reynolds projection
`Q=e_(L_0,lambda_0)` is stronger than normalizer membership for its Fourier
support `L_0`.  Thus no nontrivial two-letter word obtained by reversing
two distinct displayed Hecke arrows can provide the relative correction required by the
full-Gram transporter torsor.  It fails the label full-Gram condition
before reservoir typing is reached, so it cannot cancel the Whitehead
gauge.

This claim is deliberately narrower than the established eight external
root normalizers.  Those are realized by coefficient commutators through a
spare coordinate, not by multiplying two bare reverse-Hecke roots.  The
claim also does not cover two general nonnormal coefficient occurrences,
three or more exits, or a word with an intervening coefficient/Whitehead
factor.

No Property `(T)`, trace profile, approximation theorem, or
von-Neumann-algebra extension is used.

DERIVATION
different-opposite-root-fixed-flag-proof
