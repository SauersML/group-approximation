# STW I--XLIX high-impact hostile audit (2026-08-31)

Scope: Problems I--XLIX, excluding the separately assigned cluster
II, VII, IX, X, and XIII--XVI.  The primary status baseline was STW
arXiv:2506.10902v2.  Post-v2 primary sources checked were Toms
arXiv:2606.12188v2, Vaccaro arXiv:2604.24682v2, Kopsacheilis--Winter
arXiv:2508.04837v2, and Boldrini--Prasad arXiv:2607.01896.

## Root-status census

- **Established in the literature:** XX (Vaccaro: Villadsen algebras of the
  first type have uniform property Gamma).
- **Refuted in the literature:** XIX (Toms: a simple separable unital nuclear
  AH algebra without uniform property Gamma); XLVII in the sharp encoded form
  (Kopsacheilis--Winter: a Cantor-spectrum C-star-diagonal in the CAR algebra
  which is not an AF diagonal).
- **Refuted by a complete Cairn-internal proof:** XXII (the trace problem), by
  `stw22-projective-bundle-corona-counterexample-proof`.  This is a mathematical
  proof claim, not a literature or priority claim.
- **Still open at the encoded roots:** I, III--VI, VIII, XI--XII, XVII--XVIII,
  XXI, XXIII--XXXIX, XL--XLVI, XLVIII--XLIX.

Boldrini--Prasad's 2026 counterexample to dynamical comparison uses
`F_infinity`, so it does not refute XXXIII, whose acting group is amenable.
Kopsacheilis--Winter prove only countably many pairwise nonconjugate Cantor
diagonals; this resolves the sharp XLVII test but does not establish the
nonclassifiability assertion encoded at XLVIII.

## Independent hostile audit of the XXII endpoint

Let

```text
D_s = Gamma(End(1 + L_s^{+s})) over CP^(s^2),
B = direct_sum_s D_s,
A = unitization(B),
P = product_s D_s.
```

With `p_s` the trivial-line projection, `q_s` a tautological-line projection,
and `h_s=p_s-q_s`, one has

```text
||h_s||=1,    ||h_s||_(2,T(D_s))^2=2/(s+1).
```

The uniform tracial completion is `M=C1+J`, where `J` consists of uniformly
norm-bounded sequences whose supremal fibre `2`-norm tends to zero.  Thus
`h=(h_s)` lies in `J`, while its image modulo `B` is nonzero.

For a finite packet `z_1,...,z_ell in P`, write the `s`-th coordinate relative
to `1+L_s^{+s}` as

```text
z_(j,s) = [a_j b_j; c_j d_j].
```

Both `c_j` and `b_j^*` are sections of `L_s^{+s}`.  If `s>=2 ell`, their join
is a section of `L_s^{+(2s ell)}` with nonzero top Chern class in
`H^(4s ell)(CP^(s^2);Z)`.  It therefore vanishes at some `x`.  The trivial-line
vector state at `(s,x)` then satisfies

```text
omega(h)=1,
omega(z_j z_k)=omega(z_j)omega(z_k)  (j,k=1,...,ell).
```

The reason is stronger than vanishing of self-commutators: the common zero
makes the trivial line reducing for every member of the packet.

Given also finitely many elements of `B` and a tolerance, take `s` farther
out so their `s`-coordinates are small.  These coordinate states establish
the finite-intersection property for the weak-star closed conditions

```text
rho(h)=1,
rho(xy)=rho(x)rho(y)  (x,y in P),
rho|_B=0.
```

For a finite collection of multiplicativity constraints, include all left
and right factors in the Chern packet.  Each constraint is weak-star closed,
since both sides are continuous scalar-valued functions on `S(P)`.
Compactness gives a multiplicative state `rho`, hence a character of `P`.
It kills `B`, descends to a character of `P/B`, and takes value one on `h`.
For the tail truncations `h^(n)`,

```text
rho(h^(n))=1,
||h^(n)||_(2,T(A))=sqrt(2/(n+1)) -> 0.
```

This proves discontinuity directly and validates the refutation of XXII with
the stronger conclusion that the rogue trace is multiplicative.

## Remaining high-impact gates

No further root was closed in this pass.  The shortest live high-impact gates
remain:

1. XVIII is equivalent, in the present wiring, to the combination of XXVI
   with the comparison-to-divisibility half of XXVII.
2. XXI, XXVIII, and XXX share a centralization/selection obstruction; Toms's
   algebra decides XXI or XXVIII negatively only if it satisfies the added
   real-rank-zero-ultrapower or tracial-divisibility hypothesis, respectively.
3. XXXIII remains the commutative-dynamics gate into XXXII; currently known
   noncomparison examples use nonamenable acting groups.
4. XXXIX implies XXXVIII, but the missing step is equivariant CPoU over wild
   trace boundaries, not fibrewise equivariant McDuffness.
