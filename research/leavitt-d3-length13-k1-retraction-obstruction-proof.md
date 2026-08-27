---
rg: 2
id: leavitt-d3-length13-k1-retraction-obstruction-proof
kind: route
title: Project the two effective carrier systems onto their three coefficient copies
target: leavitt-d3-length13-k1-retraction-obstruction
requires:
  - leavitt-d3-length13-five-seven-holonomy-template
---

Use the representative and slots `g0,...,g12` from the length-thirteen
five-seven template.  Exact normal form for the seven-syllable source corner
gives precisely four identity branches:

```text
I    g2=g4=g6=1,  g1 g3 g5 g7=1;
II   g3=g6=1, g4=g2^-1, g1 g5 g7=g2;
III  g2=g5=1, g6=g4^-1, g1 g3 g7=1;
IV   g3=g5=1, g2 g4 g6=1, g1 g7=g2.
```

The target corner is `h` exactly when

```text
g0=h,                         g12=h g1^-1.              (1)
```

After substituting these equations into the unary pivot and common-carrier
equality, branches I and III become the same system, and branches II and IV
become the same system.

For the first system put

```text
x=g1, a=g8, b=g9, c=g10, d=g11,
q=h x^-1, r=h a,
H=d_0 q_1 r_2 b_1 c_2.
```

The common-carrier equation is

```text
a_0 H b_2 H^-1 c_0 d_1 q_2
 = x^-1_0 a_1 b_0 c_1 d_2.                              (2)
```

Apply to `(2)` the three retractions of the free product onto coefficient
copies 0, 1, and 2.  They give respectively

```text
a c=x^-1 b,        d=a c,
r c b c^-1 r^-1 q=d.                                    (3)
```

The first two equations say `b=xac` and `d=ac`.  Substitute these and
`r=ha`, `q=hx^-1` into the third equation.  Its left side reduces to `hac`,
whereas its right side is `ac`.  Hence `h=1`, contrary to the target choice.

For the second system put `y=g2` and

```text
q=h x^-1,
H=d_0 q_1 h_2 y_1 a_2 b_1 c_2.
```

The common-carrier equation is

```text
a_0 H b_2 H^-1 c_0 d_1 q_2
 =H y^-1_2 H^-1 (x^-1 y)_0 a_1 b_0 c_1 d_2.             (4)
```

The same three retractions give

```text
a c=x^-1 y b,       d=a c,
(h a c)b(h a c)^-1q=(h a c)y^-1(h a c)^-1d.             (5)
```

Thus `b=y^-1xac`, `q=hx^-1`, and `d=ac`.  After substitution, the two sides
of the last equation in `(5)` reduce to

```text
h a c y^-1,
h a c y^-1 c^-1 a^-1 h a c.
```

Cancellation forces `1=c^-1 a^-1 h a c`, again implying `h=1`.
Both effective systems are impossible.  Since the four source branches were
exhaustive, the result is independent of coefficient length, generation,
and any finite search alphabet.
