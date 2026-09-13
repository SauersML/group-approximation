# Constructing the quotientless witness from a finite-simple restriction

Date: 2026-09-12. The implications below are proved construction criteria.
No group meeting their unproved input restriction is asserted to exist.
The word **non-elementary** in the input hypotheses is essential.

## 1. The common-quotient construction

Let `H` be a non-elementary word-hyperbolic group. Suppose that there is a
nontrivial finite simple group `A` such that no finite simple quotient of
`H` contains a subgroup isomorphic to `A`. Then there is an infinite
word-hyperbolic group with property (T) and no nontrivial finite quotient.

Here cyclic groups of prime order count as finite simple groups.

**Proof.** Put `J=A*A*A`. This is non-elementary hyperbolic. Fix any
non-elementary hyperbolic Kazhdan group `K`. Apply the common-quotient
form of the Olshanskii theorem to `H,J,K`. It gives a non-elementary
hyperbolic group `P` and epimorphisms from each of the three inputs to
`P`. Property (T) passes from `K` to `P`.

Suppose `P` has a nontrivial finite quotient `F`. Choose a maximal proper
normal subgroup of `F`; the resulting quotient `S` is finite simple.
The epimorphism `H -> P -> F -> S` makes `S` a finite simple quotient of
`H`. The epimorphism `J -> S` cannot kill every free factor. Its
restriction to at least one copy of `A` is nontrivial and hence injective,
because `A` is simple. Thus `S` contains a subgroup isomorphic to `A`,
contrary to the hypothesis. Therefore `P` has no nontrivial finite
quotient. Its non-elementarity guarantees infiniteness.

For completeness, the common-quotient import applies without imposing
trivial finite radical on the original `H` or `K`: first quotient each
input by its maximal finite normal subgroup. These are still
non-elementary hyperbolic groups. In their free product, each factor has
trivial ambient finite radical. Indeed, a finite subgroup normalized by
an infinite factor fixes a unique vertex of the Bass--Serre tree unless
trivial; that vertex must be the factor vertex, so the finite subgroup
would be normal in that factor. The simultaneous subgroup-surjection
theorem therefore gives the common quotient. Maps from the original
inputs follow by composition. The same argument was checked in
`hyperbolic-quotientless-kazhdan-proof-2026-09-11.md`.

The geometric import is the existing
`olshanskii-g-subgroup-quotient-theorem`, sourced through Minasyan,
[*On residualizing homomorphisms preserving quasiconvexity*](https://arxiv.org/abs/math/0406126).

## 2. Three usable input restrictions

Each of the following is consequently sufficient for the same output:

1. There is a prime `ell` which divides the order of no finite simple
   quotient of `H`. Use `A=C_ell`. Cauchy's theorem gives exactly the
   needed forbidden-subgroup condition.
2. There are only finitely many isomorphism types of finite simple
   quotients of `H`. Choose a prime `ell` not dividing their orders and
   use the first condition.
3. For some integer `m>=5`, no finite simple quotient of `H` contains
   `Alt(m)`. Use `A=Alt(m)`.

The second condition does **not** require a bound on the orders of all
finite quotients. Arbitrarily large nonsimple finite quotients would not
invalidate the argument. If `H` has finite abelianization, it is enough
to establish finiteness of the nonabelian simple quotient types, since
there are then only finitely many cyclic simple quotient types. An
infinite Kazhdan hyperbolic input satisfies both the non-elementarity
and finite-abelianization requirements.

Replacing non-elementarity with infiniteness would be wrong: the
infinite dihedral group is hyperbolic and has only `C_2` as a finite
simple quotient, but the common-quotient theorem does not apply to that
elementary input.

## 3. What the explicit triangle-group input currently gives

The primary candidate source is Caprace--Conder--Kaluba--Witzel,
[*Hyperbolic generalized triangle groups, property (T) and finite simple
quotients*](https://jlupub.ub.uni-giessen.de/server/api/core/bitstreams/163d9999-b75e-4eee-a519-dbc103924f17/content).
Its Theorem 1.2 supplies `H31,H109`; Corollary 7.10 supplies
`SL_3(F_(p^e))` quotients, for all `e>=3`, of the six hyperbolic KMS
groups. Proposition 7.14 bounds the simple sections of a particular
block-matrix family, not all representations. These statements leave
no finite-spectrum certificate for the KMS inputs.

Indeed, their projective `PSL_3(F_(p^e))` quotients give infinitely many
simple quotient types. Their orders meet every prime: the defining
prime divides them, and for any other prime `ell`, choose arbitrarily
large `e` with `p^e=1 mod ell`. The factors in
`q^3(q^3-1)(q^2-1)/gcd(3,q-1)` then retain a factor of `ell`, also when
`ell=3` because both displayed factors supply one before the denominator.
Thus neither the finite-spectrum condition nor the prime-avoidance
condition holds for these inputs. This does not decide the
`Alt(m)`-avoidance condition for every KMS family.

For `Hq`, with `q=31` or `109`, the local subgroup generated by `a,b` is
`PSL_2(q)` and the remaining generator `c` has order five. Hence any
nonabelian finite simple quotient of `Hq` contains `PSL_2(q)`: otherwise
the simple local group is killed, so the entire image is generated by
the image of `c` and is cyclic. This is a necessary inclusion condition,
not an upper bound on the finite simple quotient types. Large finite
simple groups can contain that fixed local group.

No proof has been obtained that the finite simple quotients of `H31`
or `H109` exclude any fixed finite simple subgroup. In particular, a
list of low-order images, or emptiness of representation varieties in
finitely many dimensions, cannot serve as the hypothesis of Section 1.

## 4. Relation to the Rips-kernel criterion

If `1 -> N -> G -> Q -> 1` has finitely generated `N` and quotientless
`Q`, the finite-simple extension theorem in
`hyperbolic-image-compression-kernel-2026-09-12.md` identifies the
nonabelian finite simple spectra of `G` and `N`. If the kernel is
perfect, finiteness of its simple spectrum therefore supplies the
second input condition for a non-elementary hyperbolic total group.

This is a precise weaker input than requiring the kernel to have no
finite quotients at all. It still must be proved for the actual kernel;
property (T), normal generation, and the quotientless base alone do not
provide that restriction.
