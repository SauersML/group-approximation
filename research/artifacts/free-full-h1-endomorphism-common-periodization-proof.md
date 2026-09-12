# Common marked periodization of full-H1 free-group endomorphisms

## 1. The pro-p embedding

Fix a prime `p`.  The Magnus map over `F_p`,

```text
x_i |-> 1+X_i,
```

embeds the free group `F_n` in the units of the noncommutative formal power
series algebra `F_p<<X_1,...,X_n>>`.  If `1!=w in F_n`, its Magnus expansion
has a first nonzero positive-degree term.  Truncating above that degree sends
the generators into the finite `p`-group `1+I/I^k` and keeps the image of `w`
nonidentity.  Hence `F_n` is residually a finite `p`-group for every prime
`p`, and its canonical map into the free pro-`p` completion `P` is injective.

Every endomorphism of `F_n` extends continuously to `P`: send the free pro-`p`
basis to the images of the discrete basis and use the universal property.

## 2. The Frattini screen

For a pro-`p` group,

```text
Phi(P)=closure(P^p [P,P]),
P/Phi(P)=H_1(P;F_p)=H_1(F_n;F_p).
```

Let `f:P->P` be a continuous endomorphism whose map on `P/Phi(P)` is
surjective, and let `H` be the closed image of `f`.  Then `H Phi(P)=P`.  If
`H` were proper, closedness gives an open normal `N` with `HN!=P`; lift a
maximal subgroup of the finite `p`-group `P/N` containing `HN/N` to a maximal
proper open subgroup `M` containing `H`.  The quotient `P/M` is cyclic of
order `p`, so `Phi(P)<=M`.
This would imply `H Phi(P)<=M<P`, a contradiction.  Thus `f` is surjective.
This is the pro-`p` Burnside basis theorem in precisely the form needed here.

A topologically finitely generated profinite group is Hopfian.  Here is the
short argument.  For each `m`, it has finitely many open normal subgroups of
index `m`: continuous maps to `Sym(m)` are determined by finitely many
generator images.  If a continuous surjective endomorphism `f` had
`1!=x in ker(f)`, choose an open normal subgroup `N` of index `m` omitting
`x`.  Preimage under `f` injects the finite set of open normal subgroups of
index `m` into itself, hence permutes it.  Some `M` therefore satisfies
`f^(-1)(M)=N`, but `x in f^(-1)(M)`, a contradiction.  So `f` is injective.

Now let `phi_1,...,phi_r:F_n->F_n` induce integral matrices of nonzero
determinant on abelianization.  Choose a prime `p` avoiding all these
determinants.  The extensions `hat phi_i:P->P` are invertible on
`P/Phi(P)`, hence surjective by the preceding Frattini argument and injective
by Hopficity.  They are continuous automorphisms of `P`.

## 3. One characteristic marked quotient

For `1!=y in F_n<=P`, choose an open normal `U` of `P` with `y notin U`.
Put `m=[P:U]` and

```text
C = intersection {V<=P : V open and [P:V]<=m}.
```

There are finitely many intersectands by the same finite-action count used
above.  Hence `C` is open; it is contained in `U`; and every continuous
automorphism of `P` permutes the defining family, so `C` is characteristic.
It is therefore normal.  The quotient `Q=P/C` is a finite `p`-group, the
image of `y` is nonidentity, and every `hat phi_i` descends to an automorphism
`bar phi_i` of `Q`.

The image of the dense subgroup `F_n` in the finite discrete group `Q` is all
of `Q`.  Thus the assignments

```text
g |-> q(g),
t_i |-> bar phi_i
```

give a homomorphism from the multiple ascending HNN presentation to the
finite group `Q rtimes <bar phi_1,...,bar phi_r>`, with the marked word alive.

## Source check

Checked 2026-08-30: a current statement of residual `p`-finiteness for free
groups appears in Emmanouil, *Residually nilpotent groups of homological
dimension 1* (2025), and Reid, *On endomorphisms of profinite groups*,
arXiv:1112.3916, records both the bounded-open-subgroup condition for finitely
generated profinite groups and its Hopficity consequence.  The proofs above
are included so the route uses only the exact portions needed.
