# The augmentation-corner endgame does not require normality

2026-09-08. This extends the existing finite-normal-subgroup endgame
to an arbitrary finite subgroup. The existing
`agent-leavitt-not-torsion-corner-noce-forces-mf-radical` already
contains its cyclic special case, including noncentral involutions.
No property `(T)` or infinite-subgroup invariant-vector estimate occurs.
The extension supplies an endgame, not the missing group-ring map.

## 1. Any surviving matrix-corona corner has a CE trace

Write

```text
Q_d=(product_n M_(d_n)(C))/(norm-null sequences).
```

Let `p` be a nonzero projection of `Q_d`. It lifts to projections
`p_n`: take a self-adjoint lift, whose idempotence defect tends to
zero, and cut its spectrum at `1/2`. Put
`S={n:rank(p_n)>0}` and `r_n=rank(p_n)` on `S`. This set is
infinite since the quotient projection is nonzero. Compression gives a
unital isomorphism

```text
pQ_dp ~= (product_(n in S) M_(r_n)(C))/(norm-null sequences). (1)
```

Indeed, an element `pap` has representatives `p_n a_n p_n`, every
bounded corner sequence represents an element of `pQ_dp`, and
the norm-null condition is exactly the ambient one for those
compressed matrices. Omitting coordinates with `p_n=0` changes
none of these assertions.

For a free ultrafilter on `S`, further quotienting gives a unital
star homomorphism from (1) to the tracial matrix ultraproduct

```text
product_omega (M_(r_n)(C),tr_(r_n)),                       (2)
```

because `||A_n||_(2,tr_(r_n))<=||A_n||`. Thus every unital star
algebra mapping to `pQ_dp` has a Connes-embeddable tracial state,
obtained by pulling back the trace of (2). No lower bound on
`r_n/d_n` is needed. This is the corner part of
`matrix-corona-projection-ideal-and-corner-calculus`.

## 2. General group-ring corner annihilation

Let `B` be a unital star algebra with no CE tracial state, let `G`
be countable, and let `q=q^*=q^2` belong to `C[G]`. Suppose

```text
Phi:B -> qC[G]q,                Phi(1)=q                 (3)
```

is a unital star homomorphism. Then every norm-corona homomorphism
`theta:G->U(Q_d)` kills `q` under its linear extension.

For if `p=theta(q)!=0`, compose (3), the linear extension of
`theta`, and (2). This is a unital star homomorphism from `B` to
a tracial matrix ultraproduct, and gives the forbidden CE trace.
Hence

```text
theta(q)=0 for every theta.                              (4)
```

There is no centrality condition on `q`. In terms of coordinate
lifts, one compresses only the fixed algebra images `Phi(b)=qPhi(b)q`.
One does not compress the whole group representation. Therefore
no estimate for `[p_n,U_n(g)]` with arbitrary `g` is required.
All products of the compressed algebra images agree in the quotient
by their own corner identities.

Finite presentation of `B` is not needed for this implication.
For the BCS application it makes the proposed diagram finite and
explicit. Its finitely many projection generators also make all
boundedness requirements immediate.

## 3. Authentication by an arbitrary finite subgroup

For a finite subgroup `K<=G`, define

```text
e_K=|K|^-1 sum_(k in K)k,           q_K=1-e_K.              (5)
```

The finite average is a self-adjoint idempotent, and
`k e_K=e_K` for every `k in K`. These identities do not require
normality of `K` in `G`.

If (3) holds with `q=q_K`, (4) says `theta(e_K)=1`. For each
`k in K`, applying `theta` to `k e_K=e_K` gives

```text
theta(k)=theta(k)theta(e_K)=theta(e_K)=1.                 (6)
```

Thus

```text
K <= Rad_MF(G).                                         (7)
```

In particular, `K!=1` supplies any named nonidentity `k in K` as
a nontrivial element killed by every norm-corona homomorphism.
This proves that `G` is non-MF in the weak group sense used here.
It does not assume that a weak MF embedding is hyperlinear.

For cyclic `K=<z>` of order `m`, (5) is precisely the full
nontrivial spectral projection used in the existing torsion-corner
theorem. For an involution `J`, it is `(1-J)/2`, without any
centrality assumption on `J`.

The full augmentation complement matters. A selected irreducible
type `z_sigma` of a larger finite group may be killed while other
nontrivial types survive. By contrast, killing (5) forces every
element of `K` to be killed by (6), independently of which finite
representation types occur in the matrix models.

## 4. Consequence for the actual construction problem

For the fixed no-CE BCS `B_loop`, it suffices to construct a
countable group `G`, an explicitly embedded nontrivial finite
subgroup `K`, a named nonidentity `k in K`, and finite group-ring
expressions giving

```text
A(B_loop) -> (1-e_K) C[G] (1-e_K),        1 |-> 1-e_K.     (8)
```

The group can be recursively presented; the finite expressions
must satisfy the BCS identities exactly. Centrality of an
involution and normality of a larger finite subgroup are optional
additional restrictions, not requirements of the endgame.

This is a real distinction at the local matrix-packet level.
An involution's full negative corner in a finite group algebra
admits a unital matrix algebra only with power-of-two width, as
shown by `finite-involution-corner-width-is-power-of-two`.
The full augmentation complement of a larger finite additive
group admits the affine-field matrix packets of arbitrary desired
matrix width. The corresponding concrete construction is recorded
separately; it supplies local projection partitions but does not
make their cross-context marginals equal.

The central-sign construction remains a valid sufficient special
case. Its unique-product, persistent-central-extension, and
torsion-free-quotient obstructions continue to apply when that
extra centrality is imposed. They do not silently impose a central
quotient on the unrestricted finite-subgroup target (8).

The complete non-MF existence goal is still open: no map (8) for
the fixed no-CE BCS is constructed by this note. The proof here is
written mathematics, with its assumptions explicit; Cairn graph
validation is not Lean proof-kernel verification.
