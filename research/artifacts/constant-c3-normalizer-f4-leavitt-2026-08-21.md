# The normalizer branch is an F4 Leavitt unit group

Under `R congruent M_2(R)`, the order-three constant unit is

```text
r=[[0,1],[1,1]],       r^2+r+I=0.
```

Solving `Xr=rX` for `X=[[a,b],[c,d]]` gives `c=b`, `d=a+b`.  Therefore the
centralizer ring is the quadratic scalar extension

```text
{aI+br:a,b in R} congruent R tensor_(F_2) F_4
                    congruent L_(F_4)(1,2).
```

Taking units gives the group centralizer.  The normalizer acts on the cyclic
group `<r>` through `Aut(C_3)=C_2`; a constant transposition realizes the
nontrivial automorphism and splits the action.  Hence

```text
N_(R^x)(<r>) congruent L_(F_4)(1,2)^x semidirect C_2.
```

This identifies the exact hardness of the normalizer-supported rank-five
case.  It does not collapse to a finite packet: the finite-field Leavitt
nonsoficity theorem applies over `F_4` as well.  Conversely, nonsoficity alone
does not decide direct finiteness of its `F_2` group algebra, so the
identification is a reduction and a warning, not an exclusion of `(5,7)`.
