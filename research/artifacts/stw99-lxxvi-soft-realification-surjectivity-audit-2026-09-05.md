# The soft part is already completely regular

## The abstract map theorem

Let S and T be pure Cu-semigroups satisfying (O5), and let
`phi:S->T` be a Cu-morphism. Assume the induced map

```text
theta:F(T)->F(S),  lambda |-> lambda composed with phi,
```

is a homeomorphism. It is automatically a cone isomorphism. We prove
that the restriction `phi:S_soft->T_soft` is a Cu-isomorphism.

Throughout this proof S_soft uses the functional-softness convention of
Antoine--Perera--Thiel: `x` is soft if for every `x'<<x` there is an
integer `k>=1` with `(k+1)x'<=kx`. A Cu-morphism preserves this property.

Antoine--Perera--Thiel, Corollary 7.5.10 of arXiv:1410.0483, gives
canonical isomorphisms

```text
S_soft ~= S_R,        T_soft ~= T_R.
```

Its hypothesis is precisely Cu(Z)-multiplication, equivalently purity
by their Theorem 7.3.11. In particular the soft parts here are themselves
Cu-semigroups. Proposition 7.5.9 identifies realification with the
corresponding real-valued rank functions. Under these isomorphisms a
soft element x is sent to its evaluation function
`hat(x):lambda|->lambda(x)`, not to an arbitrary abstract model.

Robert's Theorem 3.2.1 in arXiv:1102.1451 identifies

```text
S_R = L(F(S)),        T_R = L(F(T)).
```

Here L is the intrinsically defined ordered semigroup of suitable lower
semicontinuous linear functions on a topological cone. Its definition
uses addition, order, scalar multiplication, continuity on finite loci,
and increasing suprema, all of which a cone homeomorphism preserves.
Consequently precomposition with theta gives an order isomorphism

```text
theta^*: L(F(S)) -> L(F(T)),     f |-> f composed with theta.
```

For every soft x and every lambda in F(T),

```text
hat(phi(x))(lambda) = lambda(phi(x))
                    = hat(x)(theta(lambda)).
```

Thus the square formed by the two canonical rank identifications,
the specified map phi on the soft parts, and theta^* commutes. Its other
three arrows are isomorphisms, which proves the assertion for phi.

In particular this proves surjectivity, not merely reflection of order:
given soft y in T, transport its rank function through theta inverse,
realize it as a soft x in S using the canonical realification
isomorphism, and apply the commuting square. No independent
coefficientwise rank-selection or continuous-field gluing theorem is
being assumed in this realization.

## The full functional cone of first-factor inclusion

Put `S=Cu(A)` and `T=Cu(A tensor Z)`, where A is separable and pure.
S is pure by assumption, and T is pure by Z-stability. Both satisfy
(O5). It remains to verify the homeomorphism hypothesis for *all*
functionals, not just densely finite quasitraces on the whole algebra.

The established coarse-shadow theorem in this lane provides the
first-factor ideal-lattice isomorphism and the first-factor bijection
on densely defined lower semicontinuous 2-quasitraces, also for each
closed ideal I of A.

Every extended lower semicontinuous 2-quasitrace tau on A has a unique
maximal closed ideal I on which it is densely defined: I is the closure of its
finite domain. The quasitrace equals infinity on positive elements
outside I. Thus it is recovered by its densely defined restriction to
I and extension by infinity off I. The zero ideal is allowed; this
includes the functional that is infinite on every nonzero positive
element.

Extend the restriction on I through the first-factor bijection for I,
then extend by infinity from `I tensor Z` to `A tensor Z`. This produces
an extension of tau. Conversely any target extended quasitrace has a
finite-domain ideal J; write `J=I tensor Z` using the ideal-lattice
isomorphism. Its densely defined restriction comes from a unique
densely defined quasitrace on I. Therefore restriction by first-factor
inclusion is a bijection on all extended quasitraces.

The functional/quasitrace correspondence of Elliott--Robert--Santiago
is natural, so this proves bijectivity of

```text
F(Cu(A tensor Z)) -> F(Cu(A)).
```

The map is continuous because it is induced by a Cu-morphism. Functional
cones are compact Hausdorff in their standard Cu topology. A continuous
bijection between them is a homeomorphism. The abstract theorem now
applies to the actual first-factor map.

The idealwise extension is essential: merely identifying the densely
defined quasitraces of a nonsimple algebra would leave out functionals
whose finite domains are proper ideals.

## Independent short proof through the Razak--Jacelon algebra

There is also a proof avoiding the quasitrace-domain discussion entirely.
Let W denote the Razak--Jacelon algebra. APT Proposition 7.5.12,
combining Robert's tensor theorem with realification, gives natural
isomorphisms

```text
Cu(W tensor A) ~= Cu(A)_R,
Cu(W tensor A tensor Z) ~= Cu(A tensor Z)_R.
```

For pure source and target, APT Corollary 7.5.10 identifies the two
right-hand semigroups canonically with the respective soft parts.
Naturality identifies the map between these realifications with the
actual first-factor map `W tensor A -> W tensor A tensor Z`.
But W is Z-stable, so this map is approximately unitarily equivalent
to an isomorphism and hence induces a Cu-isomorphism. The commuting
diagram proves exactly the claimed soft first-factor isomorphism.

The identification of a soft class x with its realification is still
the evaluation map `x -> hat(x)`, so this argument also tracks the
specified map. It does not identify the full Cu tensor product with
`Cu(A tensor Z)`. The exceptional tensor theorem invoked here is the
published theorem for the W factor.

## Why this still does not solve all noncompact classes

For residually stably finite C*-algebras, functional softness agrees
with strong softness and with softness of a positive representative.
The latter means its hereditary subalgebra has no nonzero unital
quotient. Equivalently, in every quotient of the ambient algebra the
positive representative is zero or has spectrum accumulating at zero.
By the stable-finite compact/spectral-gap criterion, a nonsoft class
therefore has a nonzero compact image in some quotient.

For `A=C(X,D)` with D simple stably finite, all quotients are again
stably finite, and closed-subset restrictions are exactly those
quotients. Thus the only classes outside this theorem have a compact
restriction somewhere. They can nevertheless be globally noncompact:
a projection bundle on a closed part can join a soft or vanishing
section elsewhere. The circle-with-a-tail examples already force that
distinction in dimension one.

The all-base projection-corner theorem separately proves regularity
for compact restrictions when D is simple pure and real rank zero.
Knowing the soft isomorphism and these compact isomorphisms does not
by itself prove that the pieces glue to the same global Cu class.
Any subsequent complete higher-dimensional theorem must supply that
compatibility argument rather than identify noncompact with soft.

## Sources and correction to the previous boundary

- R. Antoine, F. Perera, H. Thiel, *Tensor products and regularity
  properties of Cuntz semigroups*, Corollary 7.5.10 and Proposition
  7.5.9; the independent proof uses Proposition 7.5.12. See also
  Theorems 7.3.11 and 7.5.4:
  https://arxiv.org/pdf/1410.0483 .
- L. Robert, *The cone of functionals on the Cuntz semigroup*, Theorem
  3.2.1 (and the canonical realification of Section 3.1):
  https://arxiv.org/pdf/1102.1451 .
- Schafhauser--Tikuisis--White, arXiv:2506.10902v2, proof of Lemma
  22(i), also explicitly uses Z-stability of `A tensor W` and the
  natural realification/W-tensor identification:
  https://arxiv.org/pdf/2506.10902v2 .
- M. A. Asadi-Vasfi, H. Thiel, E. Vilalta, *Ranks of soft operators in
  nowhere scattered C*-algebras*, Section 3 and Theorem 5.14:
  https://arxiv.org/pdf/2310.00663 . This newer paper gives a broader
  theory of strong softness and functional cones, but its retraction
  theorem is not needed for the proof above.
- H. Thiel and E. Vilalta, *Soft operators in C*-algebras*, Proposition
  3.6, Corollary 4.6, and Proposition 4.16 (arXiv numbering):
  https://arxiv.org/pdf/2304.11644 .

The earlier soft-comparison audit correctly established order reflection
under almost unperforation alone. Its statement that soft surjectivity
remained an unresolved ranks-realization issue for *pure* A is superseded:
canonical realification already provides the required realization. This
is an application of published structural theorems to the specified
first-factor map, not a new abstract realification theorem.
