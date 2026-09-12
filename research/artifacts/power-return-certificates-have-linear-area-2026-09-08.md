# Every nontrivial power-return cursor has a linear certificate-area cost

2026-09-08. This is an elementary free-group obstruction to bounded-area
terminal authentication. It applies even to commutator cursors with zero
free abelianization. It does not rule out an operator-norm estimate proved
by other analytic means, and does not prove a non-MF example.

## 1. Statement

Let `F=F(S)` be a free group on a finite alphabet, let `R` be a fixed
finite list of words, and let `w!=1` in `F`. Define `Area_R(g)` to be
the least number of conjugates of members of `R` or their inverses
whose product is `g`, or infinity if there is no such product. Free
reductions cost no area.

There are explicit constants `D>=1` and `M>=0`, depending only on `w,R`,
such that for every `a in F` and positive integer `m`,

```text
Area_R(a w a^-1 w^-m) >= (m-1-3D)/(M+3D).              (1)
```

In particular no nontrivial cursor, including a zero-exponent-sum
cursor, admits uniformly bounded-area conjugacy-to-power certificates.
This rules out a literal conjugate of one of finitely many fixed checks
as the *complete return discrepancy* for all exponents. Adding finitely
many auxiliary generators or relators does not avoid the conclusion:
apply the same argument in the enlarged free group.

## 2. A cyclic word is never a rotation of its inverse

Write `w=b v b^-1`, with `v` a nonempty cyclically reduced word of
length `L`. Suppose `v^-1` were a cyclic rotation of `v`. Indexing
the letters modulo `L`, some integer `k` would then satisfy
`v_i=(v_(k-i))^-1` for every `i`.

If the reflection `i -> k-i` has a fixed index, a letter equals its
own inverse, impossible in a free alphabet. Otherwise `L` is even
and `k` is odd. The congruence `2i=k-1 mod L` has a solution, giving
`v_i=(v_(i+1))^-1`, contrary to cyclic reduction. This also covers
adjacency across the cyclic end.

Every length-`L` window in `vvv...` is a cyclic rotation of `v`.
Consequently no copy of `v^-1` occurs in a positive power `v^m`.

## 3. A signed word count with bounded defect

For a reduced word `g`, let `c_v(g)` count all contiguous occurrences
of `v`, allowing overlap. Put

```text
q(g)=c_v(g)-c_(v^-1)(g),
D=max(1,3(L-1)),         M=max({|q(r)|:r in R} union {0}).
```

Reversal and inversion give `q(g^-1)=-q(g)`. In a reduced
concatenation `xy`, new occurrences must cross the join, at at most
`L-1` starting positions. At each such position at most one of the
distinct words `v,v^-1` occurs. Thus its signed count differs from
`q(x)+q(y)` by at most `L-1`.

For arbitrary multiplication write reduced words `x=ab`, `y=b^-1 c`
with maximal cancellation. The three concatenations `ab,b^-1 c,ac`
are reduced. Applying the preceding bound to these three joins and
cancelling `q(b)+q(b^-1)=0` proves

```text
|q(xy)-q(x)-q(y)| <= 3(L-1) <= D.                    (2)
```

Two applications give

```text
|q(t g t^-1)-q(g)| <= 2D.                           (3)
```

Also `q(v)=1`, while Section 2 gives

```text
q(v^m)=c_v(v^m) >= m.                               (4)
```

The occurrences at the displayed block boundaries suffice for (4).
No homogenization or limit of this count is used.

## 4. Compare the return word with its certificate

Conjugating by `b^-1` changes the return word to

```text
A v A^-1 v^-m,                  A=b^-1 a b.
```

Area is invariant under conjugation. Equations (2)--(4) give

```text
q(A v A^-1 v^-m) <= q(v)+2D-q(v^m)+D <= 1+3D-m.      (5)
```

If this word is a product of `N>=1` conjugates of relators or their
inverses, each factor has absolute count at most `M+2D` by (3).
Successive use of (2) yields

```text
|q(A v A^-1 v^-m)| <= N(M+2D)+(N-1)D <= N(M+3D).     (6)
```

Combining (5)--(6) proves (1). The empty product also obeys (1),
since (5) with a zero left side implies `m<=1+3D`. Infinite area
makes the inequality immediate when no decomposition exists.

## 5. What this rules out, and the terminal-word distinction

The earlier abelianization check only detects nonzero exponent
vectors. The signed count detects every nontrivial free word, so
choosing a commutator cursor does not repair a bounded-area
certificate for the complete return discrepancy.

There is a necessary distinction in the terminal-port proposal.
A separately named terminal word `c_m` could obey a one-cell
relation to `a_m w a_m^-1`, while its identification with `w^m`
uses arbitrarily many relators. Formula (1) does not exclude this
isolated one-cell port. It excludes a uniform bound on the *total*
relator certificate, including semantic authentication of `c_m`.

For a matrix tuple, an estimate on the first port alone controls
`||a_m(U)w(U)a_m(U)^*-c_m(U)||`. To obtain the desired estimate
against `w(U)^m`, one still needs a uniform bound for
`||c_m(U)-w(U)^m||`. If the first port is one relator conjugate,
this second bound cannot be paid for by a uniformly bounded
number of fixed relator conjugates: concatenating the certificates
would contradict (1).

The target `uniform-power-return-self-hash` only asks for a
dimension-independent operator-norm inequality. A bounded-area
certificate is sufficient for that estimate, but is not required
by its definition. No converse from a norm inequality to bounded
area is proved here. That analytic target remains open; its
spectral-recurrence endgame remains a valid conditional theorem.

## Verification and dependencies

The proof uses reduced free words, cyclic reduction, and the signed
count proved above. It imports no property-(T) estimate, spectral
gap, approximation theorem, or external quasimorphism theorem.
An independent mathematical review checked the counting argument
and the separation between a terminal port and its semantic
authentication. This is a written proof, not Lean verification.
