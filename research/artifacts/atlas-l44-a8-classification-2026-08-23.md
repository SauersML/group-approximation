# Complete `A8<L4(4)` class and marking audit

The remote Sage/GAP audit uses the 85-point projective action of `GL4(4)` and
the CTblLib characteristic-two Brauer table of `A8`.  Its reproducible files
are:

```text
experiments/atlas_l44_a8_classification.py
experiments/atlas-l44-a8-classification.json
```

The exact output is:

```text
|L4(4)|=987033600,
|H|=20160,
|C_G(H)|=1,
|N_G(H)|=20160,
|H^G|=48960,
2-Brauer degrees of A8: 1,4,4,6,14,20,20,64,
the two degree-four characters are contragredient,
|Aut(A8)|=40320.
```

Because `PSL4(4)=SL4(4)`, every abstract `A8` subgroup supplies a faithful
four-dimensional `F4`-module.  The displayed Brauer degrees force it to be
one of the two irreducible degree-four modules.  They are the natural binary
module and its dual; inverse-transpose maps `GL4(2)` to itself, so both give
the same subgroup image.  Brauer--Nesbitt and descent give one conjugacy
class.  The normalizer computation is self-normalizing, so the outer
automorphism is not absorbed and there are exactly two relative marking
parities.

The pre-existing exact screen evaluates precisely those inner and graph
parities and returns zero survivors in each.  Hence it exhausts the `L4(4)`
equality endpoint; there are no additional class-pair screens to run.
