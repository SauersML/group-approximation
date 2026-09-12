# A uniform twisted-innerness gap in the actual lamp vertex

Date: 2026-08-12

## 1. Outcome

The edge shear from `FALSE_EDGE_DUAL_SHEAR_SPATIALIZATION.md` is spatial
in a Connes-embeddable over-algebra.  The most direct attempt to extend that
spatialization to a vertex, however, is impossible for a quantitative
reason.

Let `Gamma<K<J` be the edge and vertex groups in the one-orbit clutching
model, let `z` be the central involution, and let

```text
epsilon:K->F_2,
chi(k)=(-1)^(epsilon(k)),
p=(1-u_z)/2.                                             (TVG1)
```

In the negative corner put

```text
M=pL(J),       P=pL(K),       w_k=pu_k.                 (TVG2)
```

For the explicit characteristic-two Kun--Thom vertex there are a finite
set `S subset Gamma` and a constant `c>0`, independent of `m`, such that
every unitary `V in M_m(M)` satisfies

```text
max_(k in S union {q})
 ||V(1_m tensor w_k)V^*-chi(k)(1_m tensor w_k)||_2 >= c, (TVG3)
```

where `q` is any lamp of odd `O_0`-parity.  Thus the clutching automorphism
is not even asymptotically inner in any sequence of matrix amplifications of
the canonical vertex factor.

The proof uses no finite-dimensional computation.  It combines:

1. a relative FC-centre calculation for the actual Laurent vertex;
2. Fourier support in the lamp group factor; and
3. the Kazhdan gap of `Gamma`.

This does **not** rule out a nonregular Connes-embeddable correspondence or
an embedding of the vertex that changes its tracial position.  It proves
that such a genuinely external object is necessary.  In particular the
exact edge spatialization cannot be completed by tensoring or matrix
amplifying the canonical regular vertex.

## 2. Abstract twisted conjugation gap

We first isolate the operator-algebraic statement.

**Theorem 1 (twisted relative-FC gap).**  Let `Gamma<K<J` be countable
groups.  Suppose:

- `Gamma` has property `(T)`;
- `z in Z(J)` has order two and belongs to `K`;
- `chi:K->{-1,1}` is a character with `chi|Gamma=1` and `chi(z)=1`;
- the identity coset is the only finite `Gamma`-conjugacy orbit in
  `J/<z>`;
- some `q in K` satisfies `chi(q)=-1`.

Let `p=(1-u_z)/2`, `M=pL(J)`, and `w_k=pu_k`.  Choose a finite symmetric
Kazhdan set `S` for `Gamma` and `kappa>0` such that, for every unitary
representation `pi` of `Gamma`,

```text
dist(x,H^Gamma)
 <= kappa^(-1) max_(s in S)||pi(s)x-x||.                (TVG4)
```

Then for every `m>=1` and every unit vector
`xi in L^2(M_m(M))`,

```text
max_(k in S union {q})
 ||chi(k) Ad(1_m tensor w_k)(xi)-xi||_2
 >= 2kappa/(kappa+4).                                  (TVG5)
```

Consequently every unitary `V in M_m(M)` obeys `(TVG3)` with

```text
c=2kappa/(kappa+4).                                    (TVG6)
```

**Proof.**  Define a unitary representation of `K` on `L^2(M_m(M))` by

```text
rho(k)(xi)=chi(k)(1_m tensor w_k)xi(1_m tensor w_k)^*. (TVG7)
```

On `Gamma` this is ordinary conjugation.  The Fourier basis of `pL(J)` is
indexed by `J/<z>`: the two representatives satisfy

```text
pu_(zj)=-pu_j.                                         (TVG8)
```

If a vector is fixed by conjugation with `Gamma`, the absolute values of
its Fourier coefficients are constant on `Gamma`-conjugacy orbits.
Square summability kills every infinite orbit.  The relative-FC hypothesis
therefore gives

```text
L^2(M)^Gamma=Cp,
L^2(M_m(M))^Gamma=M_m(C) tensor Cp.                    (TVG9)
```

Let `E` be the orthogonal projection onto the second space in `(TVG9)` and
put

```text
d=max_(k in S union {q})||rho(k)xi-xi||_2,
delta=||xi-E xi||_2.                                  (TVG10)
```

Equation `(TVG4)` gives `delta<=d/kappa`.  Conjugation by `w_q` is trivial
on `M_m(C) tensor Cp`, while `chi(q)=-1`; hence

```text
rho(q)E xi=-E xi.                                      (TVG11)
```

The triangle inequality now yields

```text
 d >= ||rho(q)xi-xi||_2
   >= 2||E xi||_2-2||xi-E xi||_2
   >= 2-4delta
   >= 2-4d/kappa.                                      (TVG12)
```

Rearranging proves `(TVG5)`.

Finally, for a unitary `V`, normalized tracial `2`-norm gives

```text
||rho(k)V-V||_2
 =||V(1_m tensor w_k)V^*
       -chi(k)(1_m tensor w_k)||_2.                    (TVG13)
```

Apply `(TVG5)` to `V`, whose normalized `2`-norm is one.  End proof.

The theorem is a relative and character-twisted form of the usual
property-`(T)` spectral-gap argument.  The point relevant here is that the
relative FC calculation makes the `Gamma`-fixed space exactly scalar, so
the odd character has nowhere to hide.

## 3. Relative FC-centre of the Laurent Kun--Thom ambient

We verify the group hypothesis in the explicit characteristic-two model.
Fix `n>=2`, `d=2n`, and `r>=d+3`, and put

```text
R_+=F_2[x_1,...,x_d],
R=F_2[x_1^(+-1),...,x_d^(+-1)],
Gamma=EL_r(R_+),
N=EL_r(R),
Q=Sp_(2n)(Z),
G=N semidirect Q.                                      (TVG14)
```

The action of `Q` on `R` is the faithful monomial action on Laurent
exponents.  The pair `Gamma<G` is the symplectic Kun--Thom pair recorded in
`NOTEPAD.md`; in particular `Gamma` is infinite and has property `(T)`.

**Lemma 2 (relative FC-centre).**  Every nonidentity element of `G` has an
infinite conjugacy orbit under `Gamma`.

**Proof.**  Suppose `g=(v,A) in N semidirect Q` has finite `Gamma`-orbit.
Then `C_Gamma(g)` has finite index in `Gamma`.  For `i!=j`, let

```text
V_ij={a in R_+: e_ij(a) commutes with g}.              (TVG15)
```

The quotient of the root subgroup `U_ij(R_+)` by its intersection with
`C_Gamma(g)` injects into the finite coset space
`Gamma/C_Gamma(g)`.  Thus `V_ij` has finite additive codimension in `R_+`.
Commutation in the semidirect product gives

```text
v^(-1)e_ij(a)v=e_ij(Aa),       a in V_ij,              (TVG16)
```

and hence, in matrices over `Frac(R)`,

```text
a v^(-1)E_ij v=A(a)E_ij.                               (TVG17)
```

Choose nonzero `a in V_ij`.  It follows that

```text
v^(-1)E_ij v=c_ij E_ij                                (TVG18)
```

for a scalar `c_ij`.  Fix any nonzero `s in R_+`.  The two finite-codimension
subspaces

```text
V_ij,
s^(-1)V_ij={b in R_+:sb in V_ij}                       (TVG19)
```

have a nonzero common element `b`.  Apply `(TVG17)` to `b` and `sb`.
Using `(TVG18)` and cancelling in the domain gives `A(s)=s`.  Hence `A`
fixes every polynomial generator and therefore acts trivially on the
Laurent ring.  Faithfulness of the monomial action gives `A=1`.

Returning to `(TVG17)`, the matrix `v` commutes with every off-diagonal
matrix unit.  It is scalar.  Since `v in EL_r(R)`, its scalar is a torsion
unit of the Laurent ring.  Over `F_2` the Laurent unit group has no
nontrivial torsion, so `v=1`.  Thus `g=1`.  End proof.

This is the relative version of the ICC calculation already used for the
same ambient group.  Notice that finite index is required only inside the
polynomial subgroup `Gamma`; the root-subgroup argument still forces the
whole Laurent-semilinear element to be trivial.

## 4. Relative FC-centre of the actual lamp vertex

Let `Y` be a free `G`-set, possibly a disjoint union of regular orbits, and
put

```text
A=directSum_Y C_2,
J=C_2 z times (A semidirect G).                         (TVG20)
```

This is exactly the vertex form `(CPM34)` in
`FALSE_COINDUCED_PARITY_MODEL.md`.

**Lemma 3.**  The identity coset is the only finite `Gamma`-conjugacy orbit
in `J/<z>`.

**Proof.**  Let the coset of `(a,g)` have finite `Gamma`-orbit.  Its
projection `g in G` then has finite `Gamma`-orbit, so Lemma 2 gives `g=1`.
It remains to consider a finite lamp `a`.

If `a!=0`, its support is a nonempty finite subset of `Y`.  A finite orbit
would make its stabilizer `Gamma_a` finite index in `Gamma`.  The action of
`Gamma_a` on `supp(a)` has finite image.  Its kernel fixes every point of
that support.  Since the `G`-action on `Y` is free, this kernel is trivial.
Thus `Gamma_a` is finite, contradicting that it has finite index in the
infinite group `Gamma`.  Therefore `a=0`.  Modulo the central factor
`<z>`, only the identity remains.  End proof.

## 5. Application to the one-orbit clutching automorphism

Use the vertex splitting and the single orbit `O_0` from
`(CPM37)--(CPM45)`.  The common edge is

```text
K=A_s semidirect Gamma,                                (TVG21)
```

and the difference between the two edge embeddings is measured by

```text
epsilon(c,g)=sum_(y in O_0)c_y,
chi(c,g)=(-1)^(epsilon(c,g)).                           (TVG22)
```

This character is trivial on `Gamma` and on the central involution `z`.
Choose one lamp `q` in `O_0`; then `chi(q)=-1`.  Lemma 3 verifies the last
group hypothesis of Theorem 1.  Consequently `(TVG3)` holds for the actual
vertex factor with the explicit uniform constant `(TVG6)`.

In particular there is no sequence

```text
V_m in U(M_m(pL(J)))                                   (TVG23)
```

which implements the parity shear asymptotically on even one fixed
Kazhdan set together with one odd lamp.  This obstruction survives every
finite direct sum, tensoring with a matrix algebra, and passage to larger
matrix sizes.

## 6. Exact remaining extension gate

The present calculation and the edge duality theorem fit together as
follows.

```text
negative edge P
    |-- has an exact CE spatialization (edge crossed product)
    |
    `-- has no spatialization inside matrix amplifications
        of the canonical regular vertex pL(J).
```

Therefore the remaining FALSE theorem cannot say merely that the edge
automorphism is approximately inner after stabilization.  It must construct
one of the following genuinely new objects:

1. a Connes-embeddable tracial over-algebra containing a nonregular copy of
   the vertex and the edge implementer;
2. a Connes-embeddable `pL(J)`--`P` correspondence whose `Gamma`-central
   vectors are larger than the regular Fourier sector; or
3. compatible norm-corona embeddings of the two vertices whose restrictions
   to the edge agree but are not obtained from their canonical regular
   traces by finite amplification.

The first item is already sufficient by
`FALSE_ONE_VERTEX_SPATIALIZATION_CERTIFICATE.md`: one faithful vertex plus
one external edge implementer produces a hyperlinear image of the
Kun--Thom free-lamp group in which its standard sofic-radical word survives.
Thus items 2 and 3 are possible construction methods, not additional gates.

The theorem also explains why residual finiteness of each vertex does not
by itself resolve the amalgam.  Exact compatible finite-quotient models
kill `z`, while the canonical regular vertex factor and all of its finite
matrix amplifications have the uniform twisted gap `(TVG3)`.  A successful
asymptotic model would have to create new relative multiplicity in its
ultralimit; the present theorem does not rule that out.

The local edge amplifier is therefore complete.  The minimal live endpoint
is Connes embeddability of the one-sided amalgam
`pL(J) *_P (P crossed_alpha C_2)`: an external-correspondence construction,
not another clock block, cyclic homology calculation, or internal matrix
stabilization.
