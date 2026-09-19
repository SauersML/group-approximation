# Property (T) makes the dual Heisenberg operator sector sterile

Date: 2026-08-12

## 1. Result

Let `Gamma<G` be the fixed Kun--Thom pair.  Thus `Gamma` has property
`(T)`, and there are elements `s in G` and `gamma in Gamma` such that

```text
s Gamma s^(-1) subset Gamma,
s^(-1) gamma s notin Gamma.                          (DHS1)
```

The second condition says that the left cosets `sGamma` and
`gamma sGamma` are distinct.

The dual Heisenberg envelope in
`FALSE_DUAL_HEISENBERG_ENVELOPE.md` suggested an operator-norm endpoint:
an asymptotic representation of `G` together with primal and dual seed
involutions whose translates realize the coset-incidence Weyl signs.  The
endpoint is not merely difficult.  It is impossible.

**Theorem 1 (Kazhdan--stable-finite coset-Weyl obstruction).**  There do
not exist dimensions `d_n`, pointwise operator-norm asymptotic unitary
representations

```text
U_n:G -> U(d_n),                                      (DHS2)
```

and self-adjoint involutions `X_n,Z_n in M_(d_n)` such that, on putting

```text
X_(n,h)=U_n(h)X_nU_n(h)^*,
Z_(n,g)=U_n(g)Z_nU_n(g)^*,                            (DHS3)
```

one has, for every fixed `g,h in G` and `delta in Gamma`,

```text
||Z_(n,g delta)-Z_(n,g)||_op -> 0,                    (DHS4)

||Z_(n,g)X_(n,h)Z_(n,g)^*
  -(-1)^(1_(h in gGamma))X_(n,h)||_op -> 0.           (DHS5)
```

No commutation assumptions among the `X`-family or among the `Z`-family
are needed for the contradiction.

Consequently:

1. the negative projective sector `(DHE36)--(DHE37)` of the dual
   Heisenberg envelope does not exist;
2. every homomorphism from that envelope `E` to a norm matrix
   ultraproduct kills its central involution `z`; and
3. `E` is not weak MF, hence is not operator-MF.

This closes the operator-norm route proposed in the envelope note.  It does
**not** close the tracial route: Connes embeddability of the negative corner
`pL(E)` remains a sufficient condition for a hyperlinear nonsofic group.

## 2. The stably finite Kazhdan lemma

We isolate the mechanism.  Let `K_n` be finite-dimensional Hilbert spaces,
let

```text
C=product_omega B(K_n)                                (DHS6)
```

be their norm ultraproduct, and let

```text
pi:G -> U(C)                                          (DHS7)
```

be a unitary representation.  Let `P in C` be the image under
`pi|_Gamma` of the Kazhdan projection of `Gamma`.  In the Hilbert
ultraproduct, `P` is the orthogonal projection onto the subspace of
`Gamma`-invariant vectors.

**Lemma 2 (one-sided normalization becomes equality).**  Under `(DHS1)`,

```text
pi(s)^* P pi(s)=P.                                    (DHS8)
```

In particular `pi(s)` preserves the `Gamma`-invariant subspace.

**Proof.**  Put `V=pi(s)`.  If `xi` is `Gamma`-invariant, then for every
`delta in Gamma`,

```text
pi(delta)V^*xi
 =V^* pi(s delta s^(-1))xi
 =V^*xi,                                              (DHS9)
```

because `s delta s^(-1) in Gamma`.  Hence `V^*` maps the invariant
subspace into itself, and therefore

```text
V^*PV <= P.                                          (DHS10)
```

The norm ultraproduct `C` is stably finite.  Indeed, if `x^*x=1` in a
matrix amplification of `C`, choose matrix representatives `x_n`.  On an
`omega`-large set, `x_n^*x_n` is invertible and its polar correction

```text
u_n=x_n(x_n^*x_n)^(-1/2)
```

is unitary with `||x_n-u_n||->0` along `omega`.  Thus `x` itself is unitary.
The same argument works in every matrix amplification.

Now `V^*PV` is unitarily equivalent to `P` and is a subprojection of `P`.
Finiteness forbids a projection from being equivalent to a proper
subprojection.  Hence equality holds in `(DHS10)`, proving `(DHS8)`.  End
proof.

The lemma is the exact point at which operator norm enters.  It packages
the adjoint actions into a representation in a **norm** ultraproduct of
finite matrix algebras, where the Kazhdan projection and stable finiteness
are simultaneously available.

## 3. Proof of the coset-Weyl obstruction

Assume `(DHS2)--(DHS5)`.  Fix a free ultrafilter `omega`.  Give

```text
K_n=M_(d_n)                                           (DHS11)
```

its normalized Hilbert--Schmidt inner product.  Conjugation defines
unitaries on `K_n`.  Pointwise operator-norm multiplicativity of `U_n`
and the estimate

```text
||Ad(u)-Ad(v)||_(B(K_n)) <= 2||u-v||_op               (DHS12)
```

give an exact representation

```text
pi(g)=[Ad(U_n(g))]_omega
  in U(product_omega B(K_n)).                         (DHS13)
```

Let

```text
xi=[Z_n]_omega                                        (DHS14)
```

in the Hilbert ultraproduct of the `K_n`.  Taking `g=1` in `(DHS4)` shows
that `xi` is `Gamma`-invariant.  Lemma 2 shows that `pi(s)xi` is also
`Gamma`-invariant.  Therefore

```text
pi(gamma)pi(s)xi=pi(s)xi.                             (DHS15)
```

Using `(DHS2)` to identify products in the ultraproduct, `(DHS15)` is
exactly

```text
lim_(n->omega)||Z_(n,gamma s)-Z_(n,s)||_2=0.          (DHS16)
```

Choose

```text
y in sGamma symmetric_difference gamma sGamma.       (DHS17)
```

The two instances of `(DHS5)` with `(g,h)=(s,y)` and
`(g,h)=(gamma s,y)` have opposite signs.  If the first sign is
`epsilon in {+1,-1}`, they give

```text
Ad(Z_(n,s))(X_(n,y))       ->  epsilon X_(n,y),
Ad(Z_(n,gamma s))(X_(n,y)) -> -epsilon X_(n,y)        (DHS18)
```

in normalized Hilbert--Schmidt norm.  Since `X_(n,y)` is unitary, the two
targets in `(DHS18)` have distance exactly `2`.  On the other hand,

```text
||Ad(Z_(n,s))(X_(n,y))-Ad(Z_(n,gamma s))(X_(n,y))||_2
 <=2||Z_(n,s)-Z_(n,gamma s)||_2 -> 0                 (DHS19)
```

along `omega`, by `(DHS16)`.  This contradicts `(DHS18)`.  Theorem 1 is
proved.

## 4. Application to the dual Heisenberg envelope

Recall

```text
E=H(A,T) semidirect G,
z=(0,0,1) in Z(E),                                    (DHS20)
```

and the negative multiplier on `Q=E/<z>`:

```text
sigma((a,t,g),(a',t',g'))=(-1)^(t(g dot a')).         (DHS21)
```

An operator-norm asymptotic projective representation with multiplier
`sigma` supplies the two seed lamps `X_n,Z_n` and all of
`(DHS2)--(DHS5)`.  Theorem 1 therefore proves that the sufficient
certificate `(DHE36)--(DHE37)` is empty.

More generally, suppose a homomorphism

```text
rho:E -> product_n M_(k_n) / direct_sum_n M_(k_n)     (DHS22)
```

does not kill `z`.  Since `z` is a central involution, the nonzero central
projection

```text
q=(1-rho(z))/2                                        (DHS23)
```

cuts out a negative corner.  Lift `q` to projections, pass to a subsequence
on which the corner is nonzero, and polar-correct the compressed lifts of
the fixed group elements.  This produces `(DHS2)--(DHS5)` on the corner,
contradicting Theorem 1.  Hence every `(DHS22)` kills `z`.

Because `z!=1`, the group `E` cannot embed in a norm matrix ultraproduct.
Equivalently, it is not weak MF or operator-MF.

## 5. What survives

The proof does not apply to a merely tracial asymptotic representation.
If

```text
||U_n(g)U_n(h)-U_n(gh)||_2 -> 0,                      (DHS24)
```

then the adjoint maps need not be asymptotically multiplicative in
operator norm on `M_(d_n)` with its normalized Hilbert--Schmidt norm.  A
defect supported on `o(d_n)` dimensions is small in `(DHS24)` but its
conjugation superoperator can still have norm two.  Thus `(DHS13)` is
unavailable, and the Kazhdan projection cannot be placed in the stably
finite norm ultraproduct used above.

Accordingly the exact live endpoint for this envelope is

```text
pL(E) is Connes embeddable,                            (DHS25)
```

or an explicit tracial model of the same negative Heisenberg action.  The
kernel corner is decomposed in
`FALSE_DUAL_HEISENBERG_CENTER_PAULI_DECOMPOSITION.md` as
`L(K) tensor R_(G/Gamma)`.  That note proves that the classical center
action is already sofic and Connes embeddable and gauges away the
center-valued sign exactly; only coherent tracial transport of the Pauli
fibers remains.  The three-moment induced-Schreier proposal is also tracial
and is not decided by
Theorem 1.  No actual transversals proving its three limits have yet been
constructed; that is a separate open calculation.

## 6. Relation to the earlier Clifford obstruction

Proposition 8 of `PERFECT_CORE_KUN_THOM_WREATH.md` used the same
Kazhdan--stable-finite mechanism for an even Clifford cover.  The present
theorem is its bilinear coset-Weyl form.  It is sharper for this application:
it needs neither a Clifford support calculation nor commutation inside the
two lamp families.  One `Gamma`-fixed dual seed, one strict compressor, and
one pair of opposite incidence signs already force the contradiction.
