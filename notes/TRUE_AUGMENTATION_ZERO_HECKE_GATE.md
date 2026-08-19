# The augmentation-zero gate for algebraic Hecke compilers

Status: exact obstruction, exact replacement target, and exact local finite
group construction; not a nonhyperlinear-group proof.

## 1. The subgroup-average target has a hidden classical character

Let `Gamma` be a group.  The augmentation

```text
epsilon : C[Gamma] -> C,
epsilon(sum_g a_g g)=sum_g a_g
```

is a unital `*`-homomorphism.  If `q=q^*=q^2` is an algebraic projection,
then `epsilon(q)` is a self-adjoint idempotent scalar, hence belongs to
`{0,1}`.

If `epsilon(q)=1`, restriction gives a unital character

```text
epsilon_q : q C[Gamma] q -> C,
```

where the unit of the corner is `q`.  This elementary observation rules out
the subgroup-average version of the BCS corner compiler.

Indeed, for every finite subgroup `K<=Gamma`,

```text
p_K=|K|^(-1) sum_(k in K) k
```

satisfies `epsilon(p_K)=1`.  Therefore `p_K C[Gamma] p_K` always has the
augmentation character.

> **Augmentation obstruction.**  Let `B` be the universal algebra of a
> classically unsatisfiable BCS.  There is no unital `*`-homomorphism
>
> ```text
> B -> p_K C[Gamma] p_K
> ```
>
> for any group `Gamma` and finite subgroup `K<=Gamma`.

The statement is stronger than non-embeddability.  If algebraic Hecke
operators `V_x in p_K C[Gamma] p_K` merely satisfied all BCS relations,
the universal property would give such a homomorphism.  Composing with
augmentation would send every self-adjoint involution `V_x` to a sign and
every forbidden joint spectral atom to zero.  Those signs would be a
classical satisfying assignment, a contradiction.

Consequently the canonical `p_K` target in
`TRUE_BCS_PREDICATES_ARE_LOCAL_FINITE_GROUP_CORNERS.md` cannot possibly
groupify any of the non-Connes-embeddable BCS witnesses: those witnesses have
no finite-dimensional representation, in particular no character.

This obstruction is specifically algebraic.  It does not exclude operators
in the von Neumann corner `p_K L(Gamma) p_K` that do not belong to the group
ring, because augmentation need not extend continuously to the reduced
completion.

## 2. Every viable algebraic corner must kill augmentation

The same proof gives the general design rule.

> **Augmentation-zero necessity.**  If a unital `*`-algebra with no
> characters embeds unitally into `q C[Gamma] q`, for an algebraic
> projection `q`, then
>
> ```text
> epsilon(q)=0.
> ```

Thus a successful finite-word compiler cannot use a trivial-representation
subgroup average as its unit.  It must use either

1. an algebraic projection in a nontrivial finite representation sector; or
2. genuinely analytic operators outside `C[Gamma]`.

The first alternative preserves the finite-presentation character of the
program and has a canonical positive group trace.

## 3. Signed Hecke corners

Let `K<=Gamma` be finite, and let `rho` be a nontrivial irreducible complex
representation of `K`, of dimension `d_rho`, with character `chi_rho`.  Its
central block projection is

```text
z_rho=(d_rho/|K|) sum_(k in K) chi_rho(k^(-1)) k in C[K].
```

Character orthogonality gives

```text
z_rho=z_rho^*=z_rho^2,
epsilon(z_rho)=0,
tau_Gamma(z_rho)=d_rho^2/|K|>0.                 (AZH1)
```

The corner

```text
z_rho C[Gamma] z_rho
```

is the natural nontrivial-type, or signed, Hecke algebra.  Unlike the
trivial-type corner `p_K C[Gamma] p_K`, its unit is invisible to
augmentation.

There is a useful stronger firewall.  Every scalar group character
`eta:Gamma->T` induces a `*`-homomorphism `epsilon_eta:C[Gamma]->C`.  If
`d_rho>1`, then `eta|_K` is one-dimensional and character orthogonality gives

```text
epsilon_eta(z_rho)=0.                            (AZH2)
```

Thus choosing a higher-dimensional irreducible type kills not just the
ordinary augmentation, but every character of the ambient group arising
from a scalar group representation.

## 4. Arbitrary predicates also have character-free local blocks

The augmentation gate does not reinstate the affine restriction.  Every
finite Boolean predicate has an exact local realization in a
higher-dimensional irreducible finite-group block.

Let `R subseteq {+1,-1}^k` be nonempty and put `r=|R|`.  First suppose
`r>=2`, and act on `V=C^R` with its basis `(delta_a)_(a in R)`.  Let

```text
d_j delta_a=a_j delta_a
```

and let `P_R` be the full permutation-matrix group of this basis.  Define

```text
K_R=<d_1,...,d_k,P_R> <= {signed permutation matrices on C^R}.   (AZH3)
```

This is a finite group, and its defining representation `rho_R` has
dimension `r`.  It is irreducible: the joint spectral projections of the
`d_j` are the rank-one diagonal projections onto the `delta_a`, because the
coordinate strings distinguish the elements of `R`; conjugating these
projections by `P_R` supplies all matrix units.  Hence the algebra generated
by `K_R` is `M_r(C)`.

Let `z_R` be the central block projection for `rho_R`.  Then

```text
z_R C[K_R] z_R = M_r(C).                         (AZH4)
```

Moreover the predicate coordinates are represented by genuine group
elements, not merely by linear combinations:

```text
Z_j=z_R d_j z_R,
Z_j delta_a=a_j delta_a.                         (AZH5)
```

The `Z_j` are commuting self-adjoint involutions relative to the corner unit
`z_rho`, and their joint spectrum is exactly `R`.  The normalized restriction
of the canonical group trace to the block is the normalized matrix trace, so
it assigns weight `1/r` to every allowed assignment.

For `r=1`, take `K_R=C_2 times S_3` and the tensor product of the nontrivial
character of `C_2` with the standard two-dimensional representation of
`S_3`.  Represent a positive coordinate by the identity and a negative
coordinate by the central generator of `C_2`.  Again every coordinate is a
genuine group element in a higher-dimensional irreducible block, and the
unique joint spectral value is the sole member of `R`.

Therefore:

> **Character-free local predicate theorem.**  Every nonempty finite Boolean
> predicate is realized exactly by commuting involutions in a positive
> canonical-trace finite-group corner `z_rho C[K] z_rho`, where `rho` can be
> chosen irreducible of dimension greater than one.  The involutions can be
> chosen as the images of actual elements of `K`, and every scalar group
> character annihilates the corner unit.

This replaces the earlier allowed-atom corner by a local packet which cannot
collapse to a classical assignment through augmentation.

## 5. A scalar central phase is still too coarse

The full irreducible-type projection is essential.  It cannot in general be
replaced by one scalar central phase.

Let `Z<=Z(K)` be finite, let `chi` be a character of `Z`, and let `p_chi` be
its central spectral projection.  Suppose first that the `chi`-sector of
`C[K]` is one full matrix block, with unique irreducible representation
`rho`.  If `D<=K` is abelian and contains `Z`, then every character
`psi:D->T` extending `chi` occurs in `rho|D`.  Indeed,

```text
Ind_D^K(psi)
```

is nonzero and belongs entirely to the `chi`-sector.  Every irreducible
constituent is therefore `rho`, and Frobenius reciprocity puts `psi` in
`rho|D`.

The same induction argument, without the uniqueness hypothesis, says that
every extension `psi` occurs somewhere in the whole `p_chi` sector.  Thus a
scalar central phase cannot delete an arbitrary subset of the joint
characters of commuting Boolean group elements.  In the unique-block case
it cannot do so even inside that one matrix block.

This applies directly to extraspecial/Clifford packets: the negative central
sign selects their unique spin representation, but that spin block contains
every Boolean character compatible with the sign.  The fixed `M_16` packet
in the eight-lamp reduction is therefore not a universal nonlinear predicate
selector.  It may carry coefficient or holonomy data, but the predicate
selection itself must retain a fuller nonabelian type such as `z_R` from
Section 4.

## 6. Single compressed group elements collapse to the stabilizer

There is a second exact boundary on the form of the global operators.

> **Unitary-compression lemma.**  Let `q` be a projection and `u` a unitary
> in a `C*`-algebra.  Then `quq` is a unitary in the corner `qAq` if and only
> if `u` commutes with `q`.

Indeed, corner unitarity gives

```text
q u^* q u q=q,
q u q u^* q=q.
```

Subtracting from `q u^*u q=q` and `q uu^*q=q` shows

```text
((1-q)u q)^*((1-q)u q)=0,
(q u(1-q))(q u(1-q))^*=0.
```

Hence `(1-q)uq=qu(1-q)=0`, so `uq=qu`.  The converse is immediate.

Apply this to `u=lambda_Gamma(g)`.  If a proposed BCS involution has the
single-double-coset form

```text
V_x=q g_x q,
```

then it is a corner unitary and therefore `g_x q g_x^(-1)=q`.  All such
group elements lie in the stabilizer

```text
H_q={g in Gamma:gqg^(-1)=q}.                    (AZH6)
```

When `q` is supported on a finite subgroup, its finite support is permuted
by `H_q`; the subgroup generated by that support is finite and normal in the
group generated by it and `H_q`.  Thus the algebra generated by
single-compressed group elements lives in a finite-normal representation
sector.  In the invariant irreducible case, Clifford theory identifies that
sector with a fixed matrix algebra tensored with a scalar-twisted group
algebra of the quotient.  This is precisely the projective coefficient gate
already exposed by the eight-lamp spin normal form.

Therefore a signed-Hecke compiler has two genuinely different possible
endpoints:

1. **projective/central-extension endpoint:** use only group elements
   stabilizing `q` and prove the resulting twisted quotient trace non-CE; or
2. **nonnormal Hecke endpoint:** use operators with at least two double-coset
   terms, so cancellation rather than an invariant subspace makes them
   corner unitaries.

A single compressed group element cannot exploit nonnormal Hecke geometry.
The local signed-permutation construction in Section 4 is still useful, but
global transport between its blocks cannot consist solely of compressed
stable letters.

## 7. The corrected nonhyperlinear target

Choose a finitely presented BCS algebra `B` which has a tracial state but no
Connes-embeddable tracial state.  It is enough to construct:

1. a finitely presented group `Gamma`;
2. a finite subgroup `K<=Gamma` and a higher-dimensional irreducible
   representation `rho` of `K`;
3. a unital `*`-homomorphism

```text
B -> z_rho C[Gamma] z_rho.                       (AZH7)
```

No injectivity hypothesis and no prescribed trace matching are needed.
Indeed, let `tau_q` be the normalized canonical trace of the positive corner
and put

```text
sigma=tau_q after phi.                              (AZH8)
```

This is a tracial state on `B`.  If `Gamma` were hyperlinear, then
`z_rho L(Gamma) z_rho` would be Connes embeddable.  The GNS von Neumann
algebra of `(B,sigma)` is the von Neumann algebra generated by `phi(B)` in
that corner: faithfulness of `tau_q` says that the kernel of `phi` is exactly
the `sigma`-null ideal.  Hence `sigma` would be a Connes-embeddable tracial
state on `B`, contrary to the choice of `B`.

Thus `(AZH7)` would produce an explicit finitely presented nonhyperlinear
group.  Concretely, it is enough to exhibit self-adjoint corner involutions
which satisfy the finite BCS context-commutation and forbidden-atom
relations.  The canonical corner trace then supplies the contradiction
automatically.

This is an exact reduction, not the missing construction.  The global
problem is still to identify the different context blocks while retaining
one common corner unit.  Ordinary Bass--Serre gluing over amenable subgroups
cannot do this, because it remains hyperlinear.  The new information is that
the local packets should be nontrivial representation types, that no
separate trace decoder is required, and that any compiler using the trivial
`K`-type is algebraically impossible before one reaches the
Connes-embedding question.

## 8. Audited endpoint

The finite-subgroup Hecke program now has a clean dichotomy:

```text
trivial K-type p_K:
    impossible algebraically, by augmentation;

nontrivial type z_rho, dim(rho)>1:
    arbitrary local predicates remain exact and all scalar characters vanish;
    one global algebraic representation is the sole remaining gate;

single compressed group elements:
    stabilize the selector and collapse to finite-normal/projective data;

genuinely nonnormal Hecke route:
    at least one variable must combine multiple double cosets.
```

The relevant object is therefore not an ordinary spherical Hecke corner but
a matrix-valued signed Hecke corner.  This aligns the game route with the
fixed spin/Pauli packets already present in the atlas program: the finite
matrix packet must carry the local predicate, while genuinely
higher-dimensional holonomy must perform the global identifications.

`TRUE_PIECEWISE_SIGNED_HECKE_COMPILER.md` gives the first constructive
normal form for that holonomy.  Orthogonal subprojections of the selected
finite type are transported by different group words and summed.  The sum
is a corner unitary exactly when the initial and range pieces both partition
the corner unit; pairing the arrows with their inverses makes it a
self-adjoint involution.  Two pieces already evade the stabilizer collapse.
