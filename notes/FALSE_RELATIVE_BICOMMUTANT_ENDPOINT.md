# The radical double reduces to one relative-bicommutant escape

Date: 2026-08-12

## 1. Outcome

Let `Gamma<G` be countable groups, let `h in G`, and put

```text
D=G *_Gamma G,
w=i_2(h)i_1(h)^(-1).                                  (RBE1)
```

The usual FALSE endpoint asks for two homomorphisms of `G` into one
Connes-embeddable finite algebra which agree on `Gamma` but disagree at
`h`.  After one `2 by 2` amplification, this is equivalent to a strictly
smaller one-representation problem:

> Find a homomorphism `pi:G->U(M)` into a Connes-embeddable finite von
> Neumann algebra such that `pi(h)` does not commute with the relative
> commutant `pi(Gamma)' intersect M`.

Equivalently,

```text
pi(h) notin (pi(Gamma)' intersect M)' intersect M.    (RBE2)
```

For the framed Kun--Thom pair in
`FALSE_FULLY_FRAMED_AMENABLE_CONJUGACY_ORBIT.md`, the word `w` in `(RBE1)`
is nontrivial and belongs to `Rad_sof(D)`.  Hence one instance of `(RBE2)`
would give a hyperlinear nonsofic group immediately.

This formulation also identifies the exact limitation of the new amenable
conjugacy orbit.  Its stabilizer `C_G(h)` is amenable, but it does not contain
`Gamma`.  It therefore supplies finite transport charts for the conjugacy
label, but not the `Gamma`-fixed anchor which the relative-commutant
criterion requires.

## 2. The exact equivalence

All finite von Neumann algebras below carry a faithful normal trace.  Say
that `(D,w)` has a **CE separating representation** if there are a
Connes-embeddable finite von Neumann algebra `M` and a homomorphism

```text
Psi:D->U(M)                                             (RBE3)
```

such that `Psi(w)!=1`.

**Theorem 1 (relative-bicommutant endpoint).**  The following are
equivalent.

1. `(D,w)` has a CE separating representation.
2. There are a Connes-embeddable finite von Neumann algebra `N`, a
   homomorphism `pi:G->U(N)`, and a unitary

   ```text
   v in pi(Gamma)' intersect N                         (RBE4)
   ```

   such that

   ```text
   [v,pi(h)]!=1.                                      (RBE5)
   ```
3. There are `N` and `pi` as in (2) satisfying `(RBE2)`.

### Proof

Assume (2).  Define two homomorphisms of `G` by

```text
pi_1(g)=pi(g),
pi_2(g)=v pi(g) v^*.                                  (RBE6)
```

Equation `(RBE4)` says that their restrictions to `Gamma` are identical.
The universal property of the amalgam gives a homomorphism

```text
Psi=pi_1 *_Gamma pi_2:D->U(N).                        (RBE7)
```

Its marked value is

```text
Psi(w)=v pi(h)v^* pi(h)^*.                            (RBE8)
```

This is nonidentity exactly when `(RBE5)` holds.  Thus (2) implies (1).

Conversely, assume (1), and write

```text
rho_j(g)=Psi(i_j(g)),       j=1,2.                    (RBE9)
```

In `N=M_2(M)` put

```text
pi(g)=diag(rho_1(g),rho_2(g)),
v=[[0,1],[1,0]].                                      (RBE10)
```

Because `rho_1` and `rho_2` agree on `Gamma`, the flip `v` commutes with
`pi(Gamma)`.  Moreover

```text
v pi(h)v^*=diag(rho_2(h),rho_1(h)).                   (RBE11)
```

Thus `[v,pi(h)]=1` if and only if `rho_1(h)=rho_2(h)`.  But

```text
Psi(w)=rho_2(h)rho_1(h)^*,                            (RBE12)
```

so `(RBE12)` is nonidentity precisely when `(RBE5)` holds.  Matrix
amplification preserves Connes embeddability, proving (1) implies (2).

Finally, a von Neumann algebra is generated linearly and strongly by its
unitaries.  Therefore `pi(h)` commutes with `pi(Gamma)' intersect N` if and
only if it commutes with every unitary in that relative commutant.  This is
exactly the equivalence of (2) and (3).  End proof.

No faithfulness assumption on `pi` or `Psi` is present.  Only survival of
the one marked word matters.

## 3. The FALSE consequence

**Corollary 2.**  Suppose

```text
1!=w in Rad_sof(D).                                    (RBE13)
```

If any of the equivalent conditions of Theorem 1 holds, then there exists
a hyperlinear nonsofic group.

### Proof

Let `L=Psi(D)`.  Since `M` is Connes embeddable, its countable subgroup
`L` is hyperlinear.  If `L` were sofic, the quotient homomorphism
`Psi:D->L` would kill every element of `Rad_sof(D)`, contradicting
`Psi(w)!=1`.  End proof.

For the fully framed pair, `(RBE13)` is already proved.  Consequently the
remaining theorem can be stated with one representation and one relative
commutant, rather than two unrelated vertex microstate families.

## 4. Classical pmp actions give the commutant geometrically

The criterion has a transparent classical specialization.  Let

```text
G curvearrowright (X,mu)                               (RBE14)
```

be a probability-measure-preserving action, put

```text
M=L^infinity(X) crossed G,                             (RBE15)
```

and denote the canonical group unitaries by `u_g`.  Every unitary in the
fixed-point algebra

```text
L^infinity(X)^Gamma                                   (RBE16)
```

commutes with `u_Gamma`.  If `(RBE16)` contains a unitary `v` which is not
fixed by `h`, then

```text
[v,u_h]!=1.                                           (RBE17)
```

Thus, if the crossed product `(RBE15)` is Connes embeddable, Corollary 2
applies.

For a transitive `G`-set `G/K`, the generalized Bernoulli action on

```text
X=X_0^(G/K)                                            (RBE18)
```

has an especially explicit anchor.  If

```text
Gamma<=K,       h notin K,                            (RBE19)
```

then the coordinate at `K` is fixed by `Gamma` and moved by `h`.  A
nonconstant circle-valued function of that coordinate is a unitary
satisfying `(RBE17)`.  Hence CE of the corresponding generalized Bernoulli
crossed product would already prove FALSE.

This recovers, in one line, why the natural coset action `G/Gamma` is the
canonical tracial target and why its approximation is difficult.  The
condition `Gamma<=K` is load bearing.

## 5. Why the amenable conjugacy orbit is not yet the endpoint

The three-tag theorem gives a sofic action

```text
G curvearrowright G/C_G(h)                            (RBE20)
```

because `C_G(h)` is amenable.  However `Gamma` is a nonamenable Kazhdan
group, so

```text
Gamma not<=C_G(h).                                    (RBE21)
```

The distinguished coordinate of the generalized Bernoulli action over
`(RBE20)` is therefore not `Gamma`-fixed.  Averaging it over its infinite
`Gamma`-orbit loses the marked coordinate in normalized trace, exactly as
the Kazhdan trace-gap theorem predicts.

More generally, if `K` did satisfy `(RBE19)` and the action `G curvearrowright
G/K` admitted a sofic generalized-wreath realization, the base lamp at `K`
would centralize `Gamma` but not `h`.  It would give a homomorphism from the
Kun--Thom free-lamp group to a sofic group retaining its radical word, an
impossibility.  Thus amenable-stabilizer transport and a `Gamma`-fixed
anchor cannot be combined by an ordinary sofic orbit construction.

The remaining escape is genuinely tracial or noncommutative:

```text
find CE M and pi:G->U(M) with
pi(Gamma)' intersect M not contained in pi(h)' intersect M. (RBE22)
```

This is the exact one-vertex version of the paired nonliftable-fiber gate.
It is also the natural relative-commutant form of a co-hyperlinear but
non-co-sofic action.

## 6. Relation to the finite-dimensional barrier

For an honest finite-dimensional representation of the compressor pair,
`FINITE_REPRESENTATION_MATCHING_BARRIER.md` proves that the relevant
relative commutant is normalized strongly enough to make the inverse
predecessor invisible.  Condition `(RBE22)` therefore cannot be obtained
from exact finite-dimensional representations and a limiting choice of
commutant unitaries.

In a tracial matrix ultraproduct, however, the relative commutant contains
classes of asymptotically central matrices.  The finite-dimensional
Kazhdan projection controls them only after an exact correction; a
distinguished commutant unitary can remain on a normalized-rank seam.  Thus
`(RBE22)` pinpoints the required nonliftability without introducing an
auxiliary clock, phase gauge, or independent fiber representation.

The next constructive question is consequently precise: realize one
nontrivial `Gamma`-central unitary in a CE representation of `G` whose
conjugate by the inverse predecessor is not `Gamma`-central.  Any such
realization completes the proof of FALSE by Corollary 2.

There is now one further scope restriction.  The relative algebra
`pi(Gamma)''` cannot be amenable.  Property `(T)` makes every amenable
factorial `Gamma`-trace finite-dimensional and local rigidity makes the
resulting type-I center atomic.  The compressor then acts by a
trace-preserving endomorphism of an atomic finite algebra, which is
automatically onto; hence `pi(h)` belongs to `pi(Gamma)''`.  The complete
argument, including the otherwise-valid hyperfinite-amalgamation shortcut,
is in `FALSE_AMENABLE_RELATIVE_CORE_NO_GO.md`.

The matching positive construction for a single compressor is recorded in
`FALSE_COSET_TOWER_AUTOMORPHIC_DILATION.md`.  Its nonamenable Bernoulli core
has an exact relative wall, and its automorphic dilation is CE whenever one
explicit generalized Bernoulli crossed product is CE.  What prevents this
from closing the present endpoint is not an operator-algebraic defect: the
ascending one-compressor subgroup need not inherit the full Kun--Thom
infranormal sofic-radical theorem, and the representation has not yet been
extended to all of `G`.

## 7. Finite form: one almost-central wall

The one-representation endpoint has an equally exact matrix form.

**Theorem 3 (one-map matrix criterion).**  A CE separating representation
of `(D,w)` exists if and only if there are dimensions `d_n`, normalized-
Hilbert--Schmidt asymptotic homomorphisms

```text
pi_n:G->U(d_n),                                        (RBE23)
```

and unitaries `v_n in U(d_n)` such that, for every fixed
`gamma in Gamma`,

```text
||[v_n,pi_n(gamma)]-1||_2->0,                          (RBE24)
```

while

```text
liminf_n ||[v_n,pi_n(h)]-1||_2>0.                     (RBE25)
```

### Proof

Given `(RBE23)--(RBE25)`, define

```text
phi_(1,n)=pi_n,
phi_(2,n)=Ad(v_n)pi_n.                                 (RBE26)
```

Both families are asymptotic homomorphisms.  Equation `(RBE24)` says that
they agree asymptotically on `Gamma`, while `(RBE25)` says that they
disagree at `h`.  Evaluation on fixed amalgam normal forms gives an
asymptotic homomorphism of `D` retaining `w`.  Passage to the tracial
matrix ultraproduct proves one direction.

Conversely, start with paired matrix representatives
`phi_(1,n),phi_(2,n)` of a CE separating representation.  On the doubled
space put

```text
pi_n(g)=diag(phi_(1,n)(g),phi_(2,n)(g)),
v_n=[[0,1],[1,0]].                                    (RBE27)
```

The same block calculation as `(RBE10)--(RBE12)` gives `(RBE24)--(RBE25)`.
End proof.

Thus the finite construction has only one vertex microstate family and one
almost-`Gamma`-central wall.  Two independent fiber maps are a coordinate
choice, not extra mathematical data.  In particular, the real finite
endgame can be searched or attacked as

```text
pi_n is HS-asymptotically multiplicative on G,
v_n asymptotically centralizes Gamma,
v_n does not asymptotically centralize h.              (RBE28)
```

If every `pi_n` were an honest finite-dimensional representation, the
finite-representation matching theorem would force `(RBE25)` to fail.
Hence the single map in `(RBE23)` must itself be genuinely nonliftable.

The rate-sensitive finite refinement is
`FALSE_ONE_NUMBER_RELATIVE_COMMUTANT_CRITERION.md`.  It shows that one does
not need to construct `v_n` by hand: Haar averaging over the exact finite
commutant chooses it automatically.  It is enough that the squared
normalized-Hilbert--Schmidt distance of the predecessor matrix from the
current `Gamma`-algebra dominates the multiplication defect.  Tensor
averaging then upgrades that possibly vanishing seam to the fixed positive
gap required in `(RBE25)`.
