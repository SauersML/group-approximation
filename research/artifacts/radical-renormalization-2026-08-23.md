# Radical renormalization from one-sided compression

Date: 2026-08-23

Status: new relative to the supplied repository/Cairn graph; internally audited
mathematics, not externally refereed, and no literature-priority claim is made.
A web/arXiv search on 2026-08-23 did not locate this exact formulation, but that
is not an exhaustive novelty search.

## 1. The abstract automorphization lemma

Let `C` be any class of target groups and put

```text
Rad_C(G) = intersection { ker(phi) : phi : G -> H, H in C }.
```

Let `R : G -> G` be a surjective endomorphism and assume

```text
ker R <= Rad_C(G).                                           (1)
```

Then every `C`-valued homomorphism `phi : G -> H` factors uniquely through
`R`.  Indeed `(1)` gives `ker R <= ker phi`, and surjectivity defines
`phi_1(R(g)) = phi(g)`.  Since `phi_1` is again a homomorphism from `G` to the
same target `H in C`, `(1)` applies again.  Inductively,

```text
phi = phi_n o R^n                 for every n >= 1.          (2)
```

Consequently

```text
K_infty(R) := union_n ker(R^n) <= Rad_C(G).                  (3)
```

Equivalently, every `C`-representation sees only the **automorphization** of
`R`: on `G/K_infty(R)` the induced endomorphism is bijective.  Among quotients
through which `R` descends, this quotient is maximal with that property,
because injectivity of the descended map forces the quotient to kill every
`ker(R^n)`.

For the MF radical this can also be read directly from the already formalized
`UniversalFactorization.coronaMFResidual_eq_comap`: under `(1)`,

```text
Rad_MF(G) = R^{-1}(Rad_MF(G)),
```

and iteration gives `(3)`.

If in addition `G/K_infty(R)` is MF, then

```text
Rad_MF(G) = K_infty(R).                                    (4)
```

This is the basic **radical-renormalization principle**: one radical kernel of
a surjective self-map forces all finite renormalization scales into the
radical, and an MF automorphization computes the radical exactly.

## 2. A canonical self-cover attached to every compressor

Let `Gamma <= G` and let `s in G` satisfy

```text
s Gamma s^{-1} <= Gamma.                                   (5)
```

On the left coset space `X = G/Gamma` define

```text
r_s(g Gamma) = g s^{-1} Gamma.                             (6)
```

This is well-defined: if `g' = g gamma`, then

```text
g gamma s^{-1} Gamma
 = g s^{-1} (s gamma s^{-1}) Gamma
 = g s^{-1} Gamma
```

by `(5)`.  It is visibly `G`-equivariant and is surjective, since
`r_s(g s Gamma)=g Gamma`.  Its iterates are

```text
r_s^n(g Gamma) = g s^{-n} Gamma.                           (7)
```

The fibre over the base point is exactly the compression orbit

```text
r_s^{-1}(Gamma) = Gamma . (s Gamma),                       (8)
```

and, when the index is finite, its size is
`[Gamma : s Gamma s^{-1}]`.

Put

```text
Gamma_infty = union_{n>=0} s^{-n} Gamma s^n.               (9)
```

The groups in `(9)` form an increasing chain, hence `Gamma_infty` is a
subgroup.  Two sites `g Gamma,h Gamma` are eventually merged by `r_s` iff

```text
r_s^n(g Gamma)=r_s^n(h Gamma) for some n
  iff h^{-1} g in s^{-n} Gamma s^n for some n
  iff g Gamma_infty = h Gamma_infty.                       (10)
```

Thus the eventual quotient of the self-cover is canonically
`G/Gamma_infty`.  No affine coordinates and no separate self-similarity lemma
are needed: **one-sided compression itself is a self-similarity.**

## 3. Abelian torsion lamps: one local collapse determines all scales

Let `A` be a countable abelian torsion group and

```text
W_A = A^(G/Gamma) semidirect G.
```

The equivariant map `r_s` induces the surjective endomorphism

```text
R_s : W_A -> W_A,
R_s(f,g) = ((r_s)_* f, g),                                 (11)
```

where `(r_s)_*` is finite-support pushforward, i.e. the sum of lamp values in
each fibre.

Assume now that `Gamma` has property `(T)`.  For any `a in A`, take the lamp
`a_(s Gamma)`.  Its order is finite, it is centralized by
`s Gamma s^{-1}` because that subgroup fixes `s Gamma`, and its `Gamma`-orbit
consists of commuting coordinate lamps.  The established
`compression-torsion-collapse` theorem therefore identifies all lamps
`a_(gamma s Gamma)` in every norm-matrix-corona representation.  By
`G`-conjugacy the same is true in every fibre of `r_s`.  Fibrewise pair
differences generate `ker R_s`, so

```text
ker R_s <= Rad_MF(W_A).                                    (12)
```

Apply Section 1:

```text
union_n ker(R_s^n) <= Rad_MF(W_A).                         (13)
```

The repository's formalized lamp-pushforward limit lemma identifies the left
side using `(10)`:

```text
union_n ker(R_s^n)
 = ker( A^(G/Gamma) semidirect G
        -> A^(G/Gamma_infty) semidirect G ).               (14)
```

Therefore

```text
ker q_infty <= Rad_MF(W_A),                                (15)
```

where `q_infty` is the canonical fibre-sum map over
`G/Gamma -> G/Gamma_infty`.  If the target of `q_infty` is MF (for example,
residually finite), then equality holds in `(15)`.

This gives an exact radical theorem from **one** compressor, rather than from a
family of all compressor powers.

## 4. Torsion-generated nonabelian lamps

Let `K` be countable, generated by torsion elements, and assume the compression
is strict.  The same local collapse identifies equal torsion labels across
every first fibre.  Since a fibre has at least two sites, the existing
fibre-abelianization argument then forces the image of each coordinate copy of
`K` to be abelian.  Hence every MF representation factors through

```text
Q_1 : K^(G/Gamma) semidirect G
      -> K_ab^(G/Gamma) semidirect G,
Q_1(k_x) = kbar_(r_s(x)),                                  (16)
```

and `ker Q_1 <= Rad_MF`.

Now `K_ab` is an abelian torsion group, so Section 3 applies to the target of
`Q_1`.  Iteration gives the canonical limiting factor

```text
Q_infty : K^(G/Gamma) semidirect G
          -> K_ab^(G/Gamma_infty) semidirect G.             (17)
```

Every MF representation factors through `(17)`.  If its target is MF, then

```text
Rad_MF(K^(G/Gamma) semidirect G) = ker Q_infty.             (18)
```

This recovers the repository's compression-wreath radical formula, but now as
an automorphization/renormalization theorem attached canonically to a single
compressor.

## 5. Affine commuting lamps: exact radical and the missing self-similarity

For the affine quotient in the repository,

```text
X = Z x D,                 D=(Z[1/2]/Z)^3,
tau(n,y) = (n+1,y),
(v,A)(n,y) = (n,2^{-n}v + Ay).
```

Formula `(6)` for `s=tau` becomes, in these coordinates,

```text
r(n,y) = (n-1, 2y).                                      (19)
```

Indeed it is `V`-equivariant, and each fibre has eight sites.  Its iterates are

```text
r^m(n,y) = (n-m, 2^m y).                                  (20)
```

Because every element of `D` has finite 2-power order, the eventual-equivalence
classes in `(10)` are exactly the height levels.  Thus `(14)` is precisely the
level-even lamp subgroup `L_0`.  The quotient

```text
Wbar/L_0 = (directSum_Z C_2) semidirect V
```

is already proved residually finite in the repository.  Therefore

```text
Rad_MF(Wbar) = L_0.                                       (21)
```

This closes `commuting-lamp-mf-radical-is-level-even` and identifies the
universal MF quotient explicitly.

There is also a strict scale filtration.  Choose `delta_m in D` of exact order
`2^(m+1)` and put

```text
f_m = e_(0,0) + e_(0,delta_m).
```

Then `f_m` is not in `ker(R^m)` but lies in `ker(R^(m+1))`.  Hence

```text
ker R < ker R^2 < ker R^3 < ...,
union_m ker R^m = L_0.                                    (22)
```

The exact radical therefore carries a genuine unbounded finite
renormalization-depth hierarchy, even though the repository's stronger
all-compressors closure can collapse the same subgroup in fewer inference
rounds.

## 6. Kun--Thom commuting lamps are not weak MF

Let `Gamma<G` satisfy Kun--Thom Theorem A's hypotheses: `Gamma` is infranormal
but not normal and both groups have property `(T)`.  The repository has the
elementary lemma that some `s` in the compression semigroup is strict;
otherwise the whole compression semigroup would lie in the normalizer and,
because it generates `G`, `Gamma` would be normal.

Take

```text
W = (directSum_(G/Gamma) C_2) semidirect G.
```

The first fibre of `r_s` contains at least two sites.  By `(12)`, every
norm-matrix-corona representation kills each two-lamp difference inside that
fibre.  Such a difference is nontrivial in `W`.  Therefore no corona
representation is injective:

```text
W is not weak MF.                                           (23)
```

This closes `kun-thom-wreath-weak-mf` negatively.  Combined with the existing
free-lamp positive theorem and Clifford-lamp negative theorem, it also closes
the Cairn route `nonsofic-mf-classification-by-lamp-type`:

```text
free lamps       : weak MF,
commuting C_2    : not weak MF,
Clifford lamps   : not weak MF.
```

The compressor is shared; the operator-norm verdict is controlled by the lamp
relations.

## 7. Construction principle

The reusable architecture is now:

1. **Produce** a local radical kernel analytically (property `(T)` compression,
   normal-Kazhdan defect, finite-spectrum collapse, etc.).
2. **Renormalize** it through a radical-kernel surjective self-map; all stable
   kernels are forced automatically.
3. **Saturate** further by a quotient/router if desired (normal generation can
   turn one defect into full radical).
4. **Separate** by proving the terminal quotient MF; this upgrades a lower
   bound to an exact radical computation.

The central-sign, sign-free lamp, normal-Kazhdan, and full-radical router
constructions are different **producers/detectors**, but the algebra after a
radical relation is known is governed by the same factorization principle.
The new self-cover observation puts one-sided compression itself on the
amplifier side as well as the producer side.
