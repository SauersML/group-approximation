---
rg: 2
id: kt-two-positive-compressors-generate-full-obstruction
kind: claim
title: Two explicit positive compressors already generate the full Kun--Thom obstruction
distinct_from:
  kun-thom-single-compressor-sofic-joint-nonsofic: That proves every one-compressor restriction is sofic but does not exhibit a minimal finite family whose joint actor is the full Kun--Thom group; this gives an explicit pair.
  amenable-multi-compressors-have-a-joint-hs-telescope: That treats the amenable Heisenberg pair u_13,u_32 and constructs a joint local HS telescope; this pair contains a cyclic normalizer and generates the full nonamenable SL_3(Z) actor, so its joint canonical permutation model is already impossible.
  kt-wreath-relative-canonical-actor-exactification: That asks for a unitary-HS actor correction theorem; this proves only the sharp permutation incompatibility and identifies the exact two-compressor locus where that still-open upgrade must occur.
---

**ESTABLISHED.**  Use the Kun--Thom Theorem E pair with `d=3`, and put

```text
Gamma=EL_r(F_q[x_1,x_2,x_3]),
G=EL_r(F_q[x_1^(+-1),x_2^(+-1),x_3^(+-1)]) rtimes SL_3(Z).
```

Let `C` be the positive cyclic permutation matrix satisfying
`C e_i=e_(i+1)` modulo three, and set

```text
B=I+E_12,                  A=C B.                      (KTP1)
```

Then `A,B` are two positive strict compressors and

```text
<Gamma,A,B>=G.                                         (KTP2)
```

Consequently each of the two one-compressor coset actions

```text
<Gamma,A> action <Gamma,A>/Gamma,
<Gamma,B> action <Gamma,B>/Gamma                       (KTP3)
```

is sofic, but their canonical finite permutation models cannot be
amalgamated on one common actor map while satisfying all joint actor and
coset tables.  Equivalently, the two canonical one-compressor binary-wreath
models cannot share one actor restriction and all cross-compressor lamp
tables.  There is a finite joint table and a dimension-independent positive
defect floor for every attempted permutation amalgamation.

## Proof

Both matrices in `(KTP1)` lie in `SL_3(Z) intersect M_3(N)`.  The monomial
image of `B` is proper: on exponent columns,

```text
B(n_1,n_2,n_3)=(n_1+n_2,n_2,n_3),
```

so, for example, `e_2` is not in `B N^3`.  Since `C` permutes `N^3`, the
image `A N^3=C B N^3` is proper as well.  Thus conjugation by either matrix
maps `Gamma` properly into itself.

On the other hand `C=A B^(-1)` belongs to `<A,B>`.  Conjugating `B` by `C`
and `C^2` gives

```text
I+E_23,                    I+E_31.
```

Their Steinberg commutators give the remaining three elementary directions:

```text
[I+E_12,I+E_23]=I+E_13,
[I+E_23,I+E_31]=I+E_21,
[I+E_31,I+E_12]=I+E_32.                                (KTP4)
```

Hence `<A,B>` contains every elementary integral transvection and equals
`SL_3(Z)`.

It remains only to check the Laurent elementary factor in `(KTP2)`.  Every
Laurent exponent `z in Z^3` has the form `z=L(n,0,0)` for some
`L in SL_3(Z)` and `n>=0`: take `n` to be the gcd of the coordinates and
complete the primitive vector `z/n` to an integral unimodular basis (the
zero exponent is already polynomial).  Thus every Laurent monomial is an
`SL_3(Z)`-translate of a polynomial monomial.  Root additivity then says
that the conjugates of `Gamma` by `<A,B>=SL_3(Z)` generate
`EL_r(F_q[x_1^(+-1),x_2^(+-1),x_3^(+-1)])`.  This proves `(KTP2)`.

The individual actions in `(KTP3)` are sofic by
`monomial-ascending-hnn-coset-action-sofic`.  If their finite models admitted
common refinements satisfying every prescribed finite joint multiplication
and coset-incidence table with error tending to zero, a diagonal exhaustion
would be a sofic approximation of the action `G action G/Gamma`, contrary to
`coordinate-action-not-sofic` and `(KTP2)`.  Negating the definition of a
sofic action gives one finite table and a positive uniform defect floor.
The same argument with the common root lamp and its finite conjugate tables
uses `kun-thom-nonsofic-wreath` and proves the binary-wreath formulation.

## Exact consequence for the HS route

This is the minimal **global** compressor family: one compressor is too
small, while the pair `(A,B)` already contains the cyclic triple of strict
directions in `(KTP4)` and the whole actor.  It does not prove
`kt-wreath-relative-canonical-actor-exactification`.  The obstruction above
is a permutation/action obstruction, and arbitrary unitary microstates need
not preserve the coordinate masa.

Nor does the pair create a Pimsner--Popa rank contradiction in an exact
tracial model.  In the canonical Clifford model every strict positive
compressor has infinite commutant growth index, so

```text
lambda(A)=lambda(B)=infinity.
```

The relation `A=C B` with normalizer `C` merely reads
`infinity=1*infinity`.  Since the growth index is not continuous in
normalized Hilbert--Schmidt distance, it supplies no dimension-uniform
inequality for almost-representations.  The exact remaining gate is therefore
to turn this explicit two-compressor **canonical permutation** incompatibility
into actor exactification or active-Cartan recovery for arbitrary canonical
unitary-HS microstates.

DERIVATION
kt-two-positive-compressors-generate-full-obstruction-proof
