# The one-vertex target is a central group corner and a two-sheeted cover

Date: 2026-08-12

## 1. Outcome

The one-sided algebra isolated in
`FALSE_ONE_VERTEX_SPATIALIZATION_CERTIFICATE.md` has an exact discrete-group
model.  It is the negative central corner of one explicit amalgamated group,
and that group has the original twisted double as an index-two subgroup.

Consequently the canonical one-sided and two-sided von Neumann targets are
Connes embeddable simultaneously.  The one-vertex certificate remains a
real logical simplification for an arbitrary ambient algebra: one faithful
vertex and one edge spatializer suffice to produce a hyperlinear nonsofic
image.  But the *canonical* one-sided amalgam automatically regenerates the
second vertex by conjugation and is not an easier CE algebra than the
canonical twisted double.

The same calculation produces an explicit nonsofic group `H_theta` whose
negative central corner is exactly the outstanding algebra.  If that corner
is CE, then `H_theta` itself—not only a quotient image—is hyperlinear and
nonsofic.

## 2. The discrete group

Let `K<J` be countable groups, let `z` be a central involution of `J`
contained in `K`, and let

```text
theta:K->K,       theta^2=id,       theta(z)=z          (OGC1)
```

be an automorphism.  Put

```text
B_theta=K semidirect_theta C_2,
H_theta=J *_K B_theta,                                  (OGC2)
```

where `v` denotes the generator of the displayed `C_2`.  Thus

```text
v^2=1,       vkv=theta(k),       k in K.               (OGC3)
```

The element `z` is central in `H_theta`: it is central in `J`, and `(OGC1)`
shows that it also commutes with `v`.  Define

```text
p=(1-u_z)/2,
M=pL(J),       P=pL(K).                                (OGC4)
```

On `P`, the group automorphism `theta` induces the trace-preserving
automorphism

```text
alpha(pu_k)=pu_(theta(k)).                              (OGC5)
```

In the parity application, `theta(k)=z^(epsilon(k))k`, and hence `(OGC5)` is
the dual grading action `alpha(pu_k)=(-1)^(epsilon(k))pu_k`.

## 3. Exact central-corner identity

**Theorem 1.**  With normalized corner traces,

```text
pL(H_theta)
  isomorphic M *_P (P crossed_alpha C_2).              (OGC6)
```

### Proof

The group normal-form theorem gives the standard trace-preserving identity

```text
L(H_theta)=L(J) *_L(K) L(B_theta).                     (OGC7)
```

Indeed, an alternating word centered over `L(K)` is a linear combination of
reduced group words and has zero identity coefficient.  Thus the canonical
map from the reduced von Neumann amalgam to `L(H_theta)` preserves the
faithful trace and is injective.

The projection `p` is central in all three algebras in `(OGC7)`.  Compressing
an alternating centered word by `p` leaves it alternating and centered for
the normalized corner expectations.  Conversely the compressed factors
generate `pL(H_theta)`.  Hence

```text
pL(H_theta)=pL(J) *_pL(K) pL(B_theta).                 (OGC8)
```

Inside the last corner, `pu_k`, `k in K`, and `pv` satisfy

```text
(pv)^2=p,
(pv)(pu_k)(pv)=pu_(theta(k)).                          (OGC9)
```

Their Fourier coefficients show that the resulting crossed-product map is
trace preserving and onto.  It is therefore injective, and

```text
pL(B_theta) isomorphic P crossed_alpha C_2.            (OGC10)
```

Combining `(OGC8)--(OGC10)` proves `(OGC6)`.  End proof.

Thus the algebra called `N_one` is not only analogous to a group corner; it
is exactly one.

## 4. The two-sheeted twisted-double cover

There is a split epimorphism

```text
q:H_theta->C_2,       q(J)=0,       q(v)=1.            (OGC11)
```

Let `D_theta=ker(q)`.  Bass--Serre covering theory, or a direct normal-form
calculation, gives

```text
D_theta isomorphic J *_(id,theta) J.                  (OGC12)
```

The two vertex groups are `J` and `vJv`.  If the second copy is identified
with `J` by `j |-> vjv`, then its edge element `k` is identified with
`vkv=theta(k)` in the first copy, which is precisely `(OGC12)`.  Moreover

```text
H_theta=D_theta semidirect C_2.                        (OGC13)
```

Since `v` fixes `z`, the action in `(OGC13)` preserves `p`.  Put

```text
N_twist=pL(D_theta).
```

Equations `(OGC6)` and `(OGC13)` imply

```text
N_one isomorphic N_twist crossed C_2.                 (OGC14)
```

**Corollary 2.**

```text
N_one is CE  iff  N_twist is CE.                      (OGC15)
```

### Proof

One implication follows because `N_twist` is a von Neumann subalgebra of
`N_one`.  Conversely, for any trace-preserving involutive action `beta` on
a finite algebra `N`, the regular covariant representation

```text
x |-> diag(x,beta(x)),
v |-> [[0,1],[1,0]]                                   (OGC16)
```

embeds `N crossed_beta C_2` trace preservingly in `M_2(N)`.  Matrix
amplification preserves Connes embeddability.  Apply this to `(OGC14)`.
End proof.

Corollary 2 is the exact scope correction to the phrase “a second vertex is
not needed.”  A second vertex need not be supplied independently, but the
canonical algebra generates it automatically.

## 5. The group itself is an explicit nonsofic target

Now specialize to the characteristic-two Kun--Thom construction.  Thus
`Gamma<G` is the fixed infranormal pair, `t in G` is a strict compressor,
and `gamma in Gamma` satisfies

```text
t^(-1) gamma t notin Gamma.                            (OGC17)
```

Use the split lamp vertex and edge

```text
J=C_2 z times (A semidirect G),
K=C_2 z times (A semidirect Gamma),                   (OGC18)
```

and the one-orbit shear `theta(k)=z^(epsilon(k))k`.  It is the identity on
`Gamma`.  In `H_theta`, put

```text
omega=[t v t^(-1),gamma].                             (OGC19)
```

**Theorem 3.**

```text
1!=omega in Rad_sof(H_theta).                          (OGC20)
```

### Proof

Kill `A` and `z`.  The quotient of `(OGC2)` is

```text
G *_Gamma (Gamma times C_2),                          (OGC21)
```

and `(OGC19)` becomes the standard reduced Kun--Thom free-lamp word.
Bass--Serre normal form and `(OGC17)` show that its image is nonidentity.
Hence `omega!=1`.

There is also a retraction

```text
r:H_theta->G                                           (OGC22)
```

which kills `A`, `z`, and `v` and is the identity on the displayed copy of
`G`.  Let `phi:H_theta->S` be a homomorphism to a sofic group.  If
`phi(omega)!=1`, combine `phi` and `r` and let `Q` be the image of

```text
(phi,r):H_theta->S times G.                            (OGC23)
```

The group `Q` is sofic and its copy of `G` is faithful.  The image of `v`
centralizes `Gamma`, because `theta|Gamma=id`.  Kun--Thom
centralizer-normalization says that its centralizer is normalized by `G`.
Therefore the image of `tvt^(-1)` also centralizes `Gamma`, so its commutator
with `gamma` is trivial.  This contradicts `phi(omega)!=1`.  Hence every
sofic-target homomorphism kills `omega`, proving `(OGC20)`.  End proof.

Finally, the negative-corner group representation

```text
lambda_-:H_theta->U(pL(H_theta)),       h |-> pu_h      (OGC24)
```

is injective.  If `pu_g=pu_h`, expansion of

```text
p(u_g-u_h)=0                                           (OGC25)
```

in the group Fourier basis forces either `g=h`, or a cancellation with
`h=zg`; the latter gives `pu_h=-pu_g`, not equality.  Thus only `g=h` is
possible.

**Corollary 4 (exact group endpoint).**  If `N_one` is CE, then the explicit
group `H_theta` is hyperlinear and nonsofic.

This is slightly stronger than merely extracting some hyperlinear image:
Theorem 3 supplies nonsoficity of the fixed group, while `(OGC24)` and
Theorem 1 supply its faithful hyperlinear representation.

## 6. What remains

The exact unresolved statement is still `(OGC15)`.  Each factor of
`N_one` is CE, but the common edge `P` is nonamenable.  The quantitative
twisted-innerness gap rules out realizing `(OGC6)` inside a finite matrix
amplification of the regular vertex.  The group-corner and cover
identifications remove ambiguity about the target, but do not prove its
Connes embeddability.

They also show that no proof should count one-sided and two-sided CE as two
independent gates: they are the same gate under the finite cover `(OGC14)`.
