# A large irreducible block need not be a gapped core

2026-09-20. Proof-only follow-up to
`hrf-stability-next-gap-rounding-2026-09-20.md`. No computation was
run, and no concurrent canonical file was edited. The proposed
partition estimate was supplied by the parent research agent; the
pruning theorem used below is Jihao Liu's, not a new theorem here.

## 1. The reducing-partition estimate is valid

Use normalized trace `tau=Tr/d` and its Hilbert--Schmidt norm.
For a six-unitary tuple `T`, write

```
E_T(X)=sum_(t=1)^6 ||[T_t,X]||_2^2.
```

Suppose `E_W(X)>=24c ||X-tau(X)I||_2^2` and
`delta^2=sum_t ||W_t-V_t||_2^2`. If `P_i` is any common reducing
partition for `V`, then

```
24c (1-sum_i tau(P_i)^2)
 <= sum_(i,t) ||[W_t,P_i]||_2^2
 <= 2 delta^2.                                      (1)
```

Indeed `[W_t,P_i]=[W_t-V_t,P_i]`. For any matrix `D`, orthogonality
of its blocks gives the exact identity

```
sum_i ||[D,P_i]||_2^2
 =2 sum_(i != j) ||P_i D P_j||_2^2 <=2||D||_2^2.
```

The left inequality follows by summing the gap bound and using
`sum_i tau(P_i)=1`. For a partition into irreducible reducing
subspaces, `sum_i tau(P_i)^2<=max_i tau(P_i)`. Hence an irreducible
block has weight at least `1-delta^2/(12c)`. Multiplicities cause
no difficulty: choose an orthogonal decomposition into irreducible
unitary modules, not merely the isotypic decomposition.

This controls the exact commutant but says nothing about the
positive eigenvalues of the commutator Laplacian inside that block.
Section 3 shows that this distinction is necessary even after
nearest-seventh-root rounding in the actual GHB7 setting.

## 2. A constructive modified core already follows from Liu

Duplicate search found the established claim
`defective-block-expansion-prunes-to-doubled-gaps`, its proof route,
and Section D of
`liu-analytic-leaves-proof-acceptance-2026-09-20.md`. These give the
needed pruning and quantum Cheeger estimate; there is no reason to
introduce another conditional pruning node.

For every projection `p` of trace at most `1/2`, put
`D_t=W_t-V_t`. The single-projection block identity gives
`sum_t ||[D_t,p]||_2^2<=2delta^2`. Consequently

```
E_V(p) >= (1/2)E_W(p)-sum_t ||[D_t,p]||_2^2
       >= 12c tau(p)(1-tau(p))-2delta^2,
E_V(p)/24 >= (c/4)tau(p)-delta^2/12.             (2)
```

Apply Liu Lemma 5.4 to the single original block `P=I`, with
`h=6`, `theta=c/4`, `xi=delta^2/12`. We may take `c<=1`, as follows
already from the commutator upper bound. If
`delta^2<=3c/8`, the initial block is not discarded. The theorem
constructs one nonzero core `R`, and twelve unitaries
`Z_t^+,Z_t^-` reducing `R` and `I-R`, such that

```
tau(I-R) <= 8delta^2/(21c),
E_V(R)/24 <= delta^2/84,
sum_(t,sign) ||Z_t^sign-V_t||_2^2 <= 8delta^2/7. (3)
```

In the core's own normalized trace, the twelve-unitary tuple has
scalar gap at least

```
(1/48)sum_(t,sign)||[Z_t^sign|R,X]||_(2,R)^2
 >= (c^2/1024)||X-tau_R(X)R||_(2,R)^2.           (4)
```

For completeness, the mechanism being imported is precise. Remove
half-size projections of small compressed boundary energy until
none remains. A first-crossing argument and (2) charge the entire
discarded mass and final boundary to `xi`, not once per cut.
The terminal compressed contractions have projection expansion
`theta/8`. Layer-cake, Cauchy--Schwarz, and a median decomposition
give their paired commutator gap `theta^2/64`. Each contraction
`a=v|a|` is the average of the two unitaries
`v(|a| +/- i sqrt(I-|a|^2))`, so convexity transfers that gap to
the doubled list. Orthogonal boundary blocks give the edit cost
in (3). The full proof, including complex rather than just
self-adjoint test matrices, is in the cited accepted artifact.

Thus a dimension-uniform, delta-controlled *modified doubled core*
does exist. Also
`sum_(t,sign)||Z_t^sign-W_t||_2^2<=44delta^2/7` by the triangle
inequality in squared form. Neither this construction nor its
Cheeger step preserves exact seventh powers. Its conclusion is
not an exact reducing core of `V`, not six unchanged generators,
and not the missing finite-order-preserving pruning theorem.

## 3. Exact finite-order irreducibility does not rescue the gap

We strengthen the previous artifact's counterexample: the rounded
tuple can have scalar commutant and still have gap tending to zero.
In that situation it has no proper nonzero common reducing core.

Use the sequence from that artifact:
`Pi_n=pi_n direct-sum chi_n`, with `pi_n` an irreducible GHB7
representation of dimension `d_n -> infinity`, and `D_n=d_n+1`.
Relabel the three generators if necessary so that `pi_n(a)` is
not scalar; at least one is nonscalar in any irreducible module of
dimension greater than one. Choose distinct eigenvalues `lambda_n`
and `mu_n` of `pi_n(a)`, and choose the character with
`chi_n(a)=lambda_n`, `chi_n(b)=chi_n(c)=1`.

Let `e_n` be the added-line vector, `v_n` a lambda-eigenvector,
and `f_n` a mu-eigenvector. The original construction uses the
self-adjoint rank-two exchange `H_n` between `e_n,v_n` and a fixed
`0<theta<pi/7`:

```
W_a^+/-=Pi_n(a) exp(+/- i theta H_n),
W_b^+/-=Pi_n(b),  W_c^+/-=Pi_n(c).
```

It has a scalar gap `c_0>0` independent of `n`. Its exact proof
and the existence of the growing irreducibles are supplied in the
previous artifact, using property (T) and CCKW Corollary 7.19.
Relabeling generators does not change its uniform constants.

Now let `H'_n` exchange `e_n,f_n`, and take
`0<epsilon_n<pi/4`, with `epsilon_n -> 0`. Put

```
Q_+/-=exp(+/- i epsilon_n H'_n),
Wtilde_a^+/-=Q_+/- W_a^+/- Q_+/-^*,
V_a^+/-=Q_+/- Pi_n(a) Q_+/-^*.
```

For b,c leave all copies equal to `Pi_n(b),Pi_n(c)`. Nearest-root
functional calculus is equivariant under unitary conjugation, and
there are no spectral ties in the old construction. Thus

```
q7(Wtilde)=V,       (V_t)^7=I for all six t.       (5)
```

The maximum operator-norm distance between `Wtilde_t` and `W_t`
is at most `2epsilon_n`. The operator-norm gap estimate proved in
the preceding artifact therefore gives

```
gap(Wtilde) >= (sqrt(c_0)-2epsilon_n)_+^2
            >= c_0/4
```

eventually. Moreover conjugation invariance of HS norm gives

```
sum_t ||Wtilde_t-V_t||_2^2
 =16 sin(theta/2)^2/D_n -> 0.                    (6)
```

All copies of both tuples remain `O(D_n^-1/2)` close to the
genuine `Pi_n` in normalized HS norm (the conjugations change only
a two-dimensional plane). Hence all fixed defining relators and
copy-equality defects tend to zero. This is an actual GHB7
approximate-model example, not just unrelated unitaries.

We verify irreducibility of `V` explicitly. Suppress `n`, and set
`P=projection onto span(e,f)`, `s=sin(epsilon)`,
`k=cos(epsilon)`. On that plane `Pi(a)=diag(lambda,mu)` and
`Q_+/-=[[k,+/- is],[+/- is,k]]`. Outside that plane `V_a^+` and
`V_a^-` both equal `Pi(a)`. Their difference satisfies

```
(V_a^+-V_a^-)^2
 =4s^2 k^2 (lambda-mu)^2 P.                    (7)
```

Its coefficient is nonzero, so `P` belongs to the generated
unital matrix algebra. For `M=(V_a^++V_a^-)/2`,

```
PMP=cos(2epsilon) P Pi(a)P+s^2(lambda+mu)P.
```

Since `cos(2epsilon) != 0`, this reconstructs `P Pi(a)P` inside
the algebra; outside `P`, `M` already agrees with `Pi(a)`.
Thus `Pi(a)`, and hence all of `Pi(G)`, belong to that algebra.
Its commutant is consequently contained in the two block scalars
of `pi direct-sum chi`. The nonzero e--f off-diagonal entry of
`V_a^+` forces those two scalars to agree. The commutant is scalar;
because the generators are unitary, the tuple is irreducible.

Nevertheless the added-line projection `P_e` has

```
E_V(P_e)=4|lambda-mu|^2 s^2 k^2/D,
||P_e-I/D||_2^2=(D-1)/D^2.
```

Its Rayleigh quotient therefore gives

```
gap(V) <= |lambda-mu|^2 s^2 k^2 D/[6(D-1)]
        <= (4/3)epsilon_n^2 -> 0.               (8)
```

The only nonzero reducing core is `I`, so *no* extraction of an
exact common reducing subspace can produce a positive uniform gap
for these rounded tuples. In particular the large-irreducible-block
conclusion of (1), even when its block has weight exactly one,
does not supply the finite-order/gap preprocessing step.

## 4. Scope and provenance

The positive result (3)--(4) is a quantitative one-block application
of Jihao Liu, *Nonhyperlinear groups exist*, Lemma 5.4, as fully
reconstructed in the existing acceptance artifact. The primary URL
`https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf`
was retried in this pass but the web tool returned inaccessible;
no new primary-source reading or independent novelty claim is
asserted. We use the repository's full proof, not a search snippet.

The negative result (5)--(8) is an explicit refinement of the
preceding GHB7 counterexample. It does not refute modifications
on `o(D)` dimensions, doubled-unitary pruning, or flexible HS
stability. It rules out *unchanged exact reducing-core extraction*,
including the tempting largest-irreducible-block shortcut. The
remaining finite-order-preserving modified-core question is not
settled. Neither result supplies the later noncentral relator
correction or a non-residually-finite hyperbolic group.

Read-only duplicate inspection included the Liu pruning claim and
proof, `large-scalar-blocks-from-repair-and-resolvents`, Section D
of the acceptance artifact, the preceding gap-rounding artifact,
and the wave-two matching artifact's finite-order/pruning barrier.
No new canonical node, local code execution, or MSI job was used.
