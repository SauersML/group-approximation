# Nested commutators canonically recover the paired translations

Date: 2026-08-14

## 1. Outcome

The finite paired-radical quotients do not have to be reconstructed from an
arbitrary regular-representation gauge.  On each long-root character
sector, the actual middle-root commutators already act as translations of
the two outer-root character PVMs.  Their translation labels are exactly the
left and right pairing functionals

```text
a |-> ell(a b),              b |-> ell(a b).          (NPT1)
```

Consequently their kernels are exactly the two radicals of

```text
b_ell(a,b)=ell(ab).                                  (NPT2)
```

In an exact finite matrix model, the spectral support is a union of full
cosets of the resulting paired translation groups, with constant
multiplicity on each coset.  No choice of extension-character
representatives or scalarization of a commutant multiplicity is needed to
recover the **label translation graphs**.  Internal unitaries between
equal-multiplicity blocks remain, but they do not alter those graphs.

There is also a dimension-free approximate version: averaged nested-
commutator error is exactly twice the total Hilbert--Schmidt mass outside the
prescribed character-shift graph.  Thus this recovery is stable at the
correct total-error scale.

This is not yet the nonhyperlinearity proof.  A growing finite packet need
not be closed under `a |-> a t_i` and `b |-> s_j b`.  The remaining gate is
now only to make those four algebraic transports act on the same recovered
finite translation groups with vanishing boundary leakage.

## 2. Exact left translation

Work in a finite-dimensional tracial representation of one finite
four-root packet.  Use the commuting outer roots

```text
X(a)=x_12(a),                 Y(b)=x_34(b),           (NPT3)
```

the middle root `H=x_23(1)`, and the central long root

```text
Z(c)=x_14(c).
```

Fix a character `ell` of the finite additive long-root packet and compress
to its central spectral projection `p_ell`, so

```text
Z(c)p_ell=(-1)^(ell(c)) p_ell.                       (NPT4)
```

The long root commutes with the whole packet, so every operator below
preserves this sector.  Define

```text
D_b=[H,Y(b)].                                        (NPT5)
```

The four-root Steinberg identity gives

```text
[X(a),D_b]=Z(ab).                                    (NPT6)
```

With the commutator convention `[u,v]=uvu* v*`, equations `(NPT4)--(NPT6)`
become

```text
X(a)D_b=(-1)^(ell(ab)) D_b X(a).                    (NPT7)
```

Let `(P_chi)` be the character PVM of the exact finite `X`-representation.
Put

```text
Phi_R(b)(a)=ell(ab).                                 (NPT8)
```

Fourier expansion of `P_chi` and `(NPT7)` give the exact shift law

```text
D_b P_chi D_b* = P_(chi+Phi_R(b)).                  (NPT9)
```

The map `Phi_R` is linear and

```text
ker(Phi_R)={b:ell(ab)=0 for every a}=rightRad(b_ell). (NPT10)
```

Therefore the distinct physical translations supplied by the `D_b` are
canonically indexed by the right radical quotient.  Since every `D_b` is a
unitary, `(NPT9)` also proves

```text
tau(P_chi)=tau(P_(chi+Phi_R(b))).                    (NPT11)
```

The character support is consequently invariant under the entire finite
translation group `im(Phi_R)` and has constant multiplicity on each of its
orbits.

## 3. Exact right translation

The other parenthesization supplies the symmetric construction.  Put

```text
C_a=[X(a),H].                                        (NPT12)
```

Then the same four-root identity reads

```text
[C_a,Y(b)]=Z(ab).                                    (NPT13)
```

On the `ell` sector,

```text
C_a Y(b)=(-1)^(ell(ab)) Y(b) C_a.                   (NPT14)
```

If `(Q_psi)` is the character PVM of the `Y`-root representation and

```text
Phi_L(a)(b)=ell(ab),                                 (NPT15)
```

then, up to the immaterial sign convention for translating a binary
character,

```text
C_a Q_psi C_a* = Q_(psi+Phi_L(a)).                  (NPT16)
```

Its kernel is the left radical of `b_ell`.  Thus both point-separating
quotients used by `FinitePairedQuotientObstruction.lean` occur as concrete
translation groups on the two commuting outer spectral spaces.

This is stronger than merely observing the scalar commutator table.  It
identifies the unitaries which implement every row and column translation
and proves flat multiplicity along their orbits.

## 4. Total-error stability by Fourier Parseval

The exact shift law has a cardinality-free stable form.  Let `A` be a finite
elementary abelian group, let `X:A->U(M)` be an exact representation with
character PVM `(P_chi)`, let `D` be unitary, and fix a character `eta`.  Set

```text
e(D,eta)^2
 =(1/|A|) sum_a
   ||X(a)D-(-1)^(eta(a))D X(a)||_2^2.                (NPT17)
```

Expanding `D` into the orthogonal blocks `P_psi D P_chi` and applying
character orthogonality gives

```text
e(D,eta)^2
 =2 sum_(psi != chi+eta)||P_psi D P_chi||_2^2.       (NPT18)
```

Equivalently, if

```text
Q_eta(D)=sum_chi P_(chi+eta) D P_chi,                (NPT19)
```

then

```text
||D-Q_eta(D)||_2=e(D,eta)/sqrt(2).                   (NPT20)
```

This is the homogeneous-shift specialization of homomorphism twirling.  It
has no factor depending on the root-window size, number of characters, or
matrix dimension.  Applying it to `(D_b,Phi_R(b))` and
`(C_a,Phi_L(a))` shows that averaged nested-commutator defects recover the
two paired translations with total wrong-shift mass tending to zero.

## 5. What this removes

The following parts of the paired-quotient decoder are now intrinsic:

1. the two radical quotients are the images of `Phi_L` and `Phi_R`;
2. their points separate by construction after quotienting the kernels;
3. their regular translation actions are implemented by named group words
   `C_a` and `D_b`;
4. character multiplicities are flat along every exact translation orbit;
5. approximate wrong-translation mass has the uniform Parseval bound
   `(NPT18)`.

In particular, an arbitrary unitary on a Pauli multiplicity space cannot
change these translation graphs while preserving the mixed nested
commutators.  This avoids the one-gauge countermodel in
`FALSE_ONE_COPRODUCT_GAUGE_DOES_NOT_SCALARIZE_THE_MULTIPLICITY.md`: the
recovered objects are the actual family of middle-root commutators, not the
coefficient PVM of one unrelated compressor gauge.

## 6. Exact remaining boundary

For the binary Leavitt ring, the algebraic maps

```text
R_i:[a] |-> [a t_i],          L_j:[b] |-> [s_j b]    (NPT21)
```

are well-defined on the two radical quotients and satisfy

```text
b_ell(R_i[a],L_j[b])=delta_(ij)b_ell([a],[b]).       (NPT22)
```

The finite obstruction is immediate once `(NPT21)` acts on one finite
recovered pair.  But a finite coefficient window in a matrix microstate is
not invariant under all four maps.  Equations `(NPT9)` and `(NPT16)` give
the translations present inside the selected window; they do not make the
window closed under `(NPT21)`.

The live theorem has therefore narrowed to:

> **Paired-translation closure estimate.**  Choose growing left and right
> root packets so that the translation groups recovered by `(NPT18)` retain
> positive total long-root negative-sector trace, and prove that the four
> raw/comb compressor transports in `(NPT21)` have vanishing normalized
> boundary leakage on those same groups.

Once this is obtained, `(NPT22)` feeds directly into the existing robust
`1/36` finite paired-quotient floor or the `2-sqrt(3)` contraction floor.
The extension-fiber branch PVM is no longer the primary object; it is enough
to synchronize the named paired translations under the four transports.

No local computation or build was run for this note.
