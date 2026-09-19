---
rg: 2
id: operator-small-terminal-quartic-ledger-proof
kind: route
title: Factor pair remainders through the terminal square function and spend two odd factors
target: terminal-operator-smallness-gives-quartic-ledger
requires: []
---

Since every `O_i` is self-adjoint,

```text
sum_(i,j)||O_iO_j||_2^2
 =sum_(i,j)tau(O_j O_i^2 O_j)
 =sum_(i,j)tau(O_i^2 O_j^2)
 =L^2 tau(A^2).
```

Using `||C-D||_2^2<=2||C||_2^2+2||D||_2^2` for the commutator gives the
first inequality in `(OSQ2)`.  Positivity gives
`tau(A^2)<=||A||_op tau(A)=||A||_op D`, while
`O_i^2<=theta I` gives `A<=theta I`.

For a parity word of length `m`, the exact common-cut expansion contains
only nonempty even subsets of off-diagonal positions.  In every such term,
retain one `O` in Hilbert--Schmidt norm and bound a second `O` by
`sqrt(theta)` in operator norm; all other factors are contractions.  Thus
the square of that term is at most `theta` times one of the participating
boundary squares.  Cauchy--Schwarz over the at most `2^(m-1)-1` terms gives
the asserted `C_m` bound.  Bounded occurrence converts the sum over faces
to `O(theta D)`.

Finally the common-cut sign ledger gives
`||sgn(X_i)-X_i||_2^2<=tau(O_i^4)`, and
`O_i^2<=theta I` gives `(OSQ3)`.  Equality, parity, and pair sign
telescoping therefore all cost `O(theta D)`.  Combining a pair remainder
with the compressed original commutator by the squared triangle inequality
changes the constant `4` in `(OSQ2)` to at most `8` in the final energy,
which proves `(OSQ4)`.
