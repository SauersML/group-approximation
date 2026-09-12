# An exact lower bound for the Higman word-energy coefficient

2026-09-07. This obstructs small proposed coefficients; it proves neither
hyperlinearity nor nonhyperlinearity. No all-dimensions upper bound or
Lean verification is claimed.

Use the four-cycle convention already fixed in
`higman-hs-microstates-are-near-glued-exact-bs-cycles`:

\[
 r_0=aba^{-1}b^{-2},\quad r_1=bcb^{-1}c^{-2},\quad
 r_2=cdc^{-1}d^{-2},\quad r_3=dad^{-1}a^{-2}.
\]

For a unitary word v set `e_v=||v-I||_2^2`, with normalized HS norm.
Any coefficient C satisfying

\[
 e_a(U)\le C\sum_{j=0}^3 e_{r_j}(U)
 \quad\text{in every dimension on every unitary tuple}
 \tag{1}
\]

must satisfy

\[
 C\ge\frac{2748800041}{1512087866}>\frac95.\tag{2}
\]

## Two-dimensional calculation

Let `x^2+s^2=y^2+t^2=1` and put

\[
 A=\begin{pmatrix}x+is&0\\0&x-is\end{pmatrix},\quad
 B=C_0=I_2,\quad
 D=\begin{pmatrix}y&it\\it&y\end{pmatrix}.
\]

C_0 denotes the third generator matrix, not the coefficient. These
matrices are exactly unitary. The first two relators evaluate to I, and
the third to D^{-1}. Thus

\[
 e_a=2-2x,\quad e_{r_0}=e_{r_1}=0,\quad e_{r_2}=2-2y.
\]

Writing z=x+is, the normalized trace of the fourth relator is

\[
 \tfrac12\big((y^2z+t^2\bar z)\bar z^2
                 +(t^2z+y^2\bar z)z^2\big)
 =y^2 x+(1-y^2)(4x^3-3x)
 =x\big(4x^2-3+4(1-x^2)y^2\big).
\]

It is real. Consequently the total relator energy is exactly

\[
 E(x,y)=4-2y-2x(4x^2-3)-8x(1-x^2)y^2.\tag{3}
\]

Take `(x,s)=(-60/109,91/109)` and `(y,t)=(12/37,35/37)`.
The integer identities `60^2+91^2=109^2` and `12^2+35^2=37^2`
certify unitarity. Substitution gives:

| Quantity | Exact value |
| --- | --- |
| Marked energy e_a | 338/109 |
| First and second relator energies | 0, 0 |
| Third relator energy | 50/37 |
| Fourth relator energy | 628372082/1772894701 |
| Total relator energy | 3024175732/1772894701 |
| e_a / total relator energy | 2748800041/1512087866 |
| e_a - (9/5) total relator energy | 270418822/8864473505 |

The final entry is positive, proving (2). No numerical optimization is
a proof input. For a shorter control use `(x,s)=(-3/5,4/5)` and
`(y,t)=(0,1)`: then e_a=16/5, E=266/125, and the violation at
coefficient 3/2 is exactly 1/125.

## Exact replay and a bounded next attempt

The stronger witness is `higman-hs-word-coefficient-witness.json`.
Its verifier recomputes unitarity, words and energies over Q(i), ignoring
the recorded verification result:

```
python3 experiments/hs_word_certificate.py verify research/artifacts/higman-hs-word-coefficient-witness.json
python3 -m unittest discover -s experiments -p test_hs_word_certificate.py -v
```

The regression also checks (3) independently of word evaluation. The
next candidate sets C=2; the recorded finite replay is obtained by

```
python3 experiments/hs_word_certificate.py search research/artifacts/higman-hs-coefficient-two-candidate.json --max-tests 1000 --max-dimension 2 --max-height 2
```

Only the reported finite prefix of the rational Cayley enumeration is
tested. Finding no violation in that prefix proves neither validity on
all two-dimensional tuples nor validity in every dimension. No claim
that 2 is a valid coefficient is made.

## Boundary of the existence argument

A bound (1), combined with the known group-theoretic nontriviality of a,
would put a in the Higman hyperlinear radical and exclude a hyperlinear
embedding, by `hyperlinear-radical-has-linear-word-certificate`. The
present calculation supplies only a necessary lower bound on C.

These matrices have positive relator error. They are neither an exact
Higman representation nor a separating sequence with relator errors
tending to zero. Padding by m identity dimensions multiplies every
energy by `2/(m+2)`. Although this preserves the strict violation, it
also makes the marked energy tend to zero, so it supplies no separating
sequence. The four-seam gluing problem and `non-hyperlinear-group`
remain open.

Repository searches on 2026-09-07 found the Higman/BS gluing equivalence
and periodic-clock attacks, but no existing coefficient calculation of
this form. Rational Cayley enumeration is already used in the archive's
HS-Dehn argument. This is a concrete diagnostic for the current route,
without a claim of global mathematical novelty.
