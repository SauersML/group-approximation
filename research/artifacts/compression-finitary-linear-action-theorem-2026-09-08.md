# The finitary linear action theorem without adjoined points

Date: 2026-09-08. Supersedes the configuration of
`research/artifacts/finitary-linear-vs-permutation-kazhdan-criterion-2026-09-08.md`
by removing its two adjoined fixed points, and adds the exact defect
identity, the permanence package, and the canonical ascending-HNN family.

The only analytic input is **(P)**: if `L <= H` has property (T) and a
finite central `A <= H` lies in `D_H(L)`, every homomorphism from `H` to
an MF group kills `A`. In this archive that is the finite-central case of
the established, kernel-checked `normal-kazhdan-defect-non-mf`. A finite
group has property (T): averaging a unit vector displaced by less than
one by every element gives a nonzero invariant vector. **No new analytic
argument is used anywhere below**, and in particular nothing from the
commuting-conjugate criterion landed earlier today.

`[g,h] = ghg^-1h^-1`. `T_(pq) = I + E_(pq)` over `F_2`, so `T_(pq)^2 = I`.

## 1. The action theorem

**Theorem 1.** Let a countable `V` act on a countably infinite `X`, put

```text
K = GL_fin(F_2^(X)),   G = K x| V,   pi : G -> V,
```

with finitary meaning equal to the identity outside a finite square block
of the displayed basis, and `V` acting by permutation of that basis.
Suppose

```text
L <= V has property (T),   uLu^-1 <= L,
x in X^L,                  ux not in X^L.                          (1)
```

Then every homomorphism from `G` to an MF group kills `K`, and

```text
Rad_MF(G) = pi^-1(Rad_MF(V)),      D_G(L) = pi^-1(D_V(L)).         (2)
```

So `G` is not MF, and if `V` is residually finite both groups in (2)
equal `K`.

**Proof.** Put `x_i = u^i x`. Every `x_i` with `i <= 0` is `L`-fixed,
because `u^-1 X^L` is contained in `X^L`: for `y` in `X^L` and `ell` in
`L`, `ell u^-1 y = u^-1 (u ell u^-1) y = u^-1 y`, using `uLu^-1 <= L`.
They are pairwise distinct: `u^-i x = u^(-i-m) x` with `m > 0` gives
`x = u^-m x`, so `ux = u^(1-m) x` lies in `X^L` because `1 - m <= 0`,
contradicting (1). Choose `ell` in `L` with `ell ux != ux`, and set

```text
a = x_(-1),   b = x_(-3),
p = (x_(-1) x_(-2))(x_(-3) x_(-4)) in K,      v = up.
```

The permutation matrix `p` centralizes `L`, since `L` fixes each of the
four transposed points, so conjugating `p` by `ell` in `L` permutes the
same pairs. Consequently `v L v^-1 = u L u^-1 <= L`. Acting on the basis,
`v` is `u` composed with the transposition product, so

```text
v a = a,     v b = b,     v x = ux,
```

the last because `x_0` is distinct from `x_(-1), ..., x_(-4)`. **No point
has been adjoined to `X`.** This is the whole simplification.

Put

```text
c = T_(xb),   y = T_(a,ux),   z = T_(ab),   H = <L, v, c, y>.
```

Then `c` is in `C_H(L)`, because `x` and `b` are `L`-fixed. Direct
multiplication gives

```text
d = [v c v^-1, ell] = T_(ux,b) T_(ell ux, b)^-1,     [y, d] = z.    (3)
```

For (3), `v c v^-1 = T_(vx, vb) = T_(ux, b)`, and conjugating by `ell`
fixes the column `b` and moves the row to `ell ux`. With
`A = E_(a,ux)` and `B = E_(ux,b) + E_(ell ux, b)`,

```text
A^2 = B^2 = BA = 0,      AB = E_(ab),
```

and every product of length three vanishes, so
`[y,d] = (I+A)(I+B)(I+A)(I+B) = I + AB = z`. All the indices involved are
distinct: `ux` and `ell ux` are not `L`-fixed, whereas `a` and `b` are,
and `a != b`.

`d` is a defect generator of the configuration `(L, v, c)` in `H`, so
`d` lies in `D_H(L)`, which is normal in `H`, so `z` lies in `D_H(L)`.
The matrix `z` commutes with `L` and `v` because `a, b` are fixed by
both, and with `c` and `y` because `E_(ab)E_(xb) = E_(xb)E_(ab) = 0` and
`E_(ab)E_(a,ux) = E_(a,ux)E_(ab) = 0`; and `z^2 = I`. So `<z>` is a
finite central subgroup of `H` inside `D_H(L)`, and (P) applies **to
`H`**: every homomorphism from `H` to an MF group kills `z`. Restricting
any `G -> M` with `M` MF to `H` kills `z`.

Finitary permutation matrices conjugate `z = T_(ab)` to `T_(pq)` for
every ordered pair of distinct points, and those generate `K`: Gaussian
elimination over `F_2` uses row additions and swaps, and a swap is three
row additions. So every MF homomorphism of `G` kills `K`, and
`K <= D_G(L)`.

Every MF homomorphism therefore factors through `pi`, which gives the
radical identity in (2). For the defect identity, a defect generator of
`D_G(L)` projects to one of `D_V(L)`, since `pi` is the identity on `L`
and carries compressors to compressors and `C_G(L)` into `C_V(L)`; and
the canonical copy of `V` in `G` gives `D_V(L) <= D_G(L)`. So
`pi(D_G(L)) = D_V(L)`, and `K = ker pi` is contained in `D_G(L)`, which
is exactly the second identity.

Finally, every finite quotient kills compression defects: the finite
images of `L` and of a conjugate `vLv^-1 <= L` have equal cardinality, so
the inclusion is equality and the conjugated centralizer still
centralizes the image. So residual finiteness of `V` gives `D_V(L) = 1`,
and it also gives `Rad_MF(V) = 1`, because regular representations of
finite quotients separating successive finite sets are MF models and a
detected element moves a basis vector to an orthogonal one, at operator
distance at least `sqrt 2`. QED

So MF-ness of this linear extension would force every compressor of every
Kazhdan subgroup to preserve its fixed-point set.

## 2. Permanence, independent of hypothesis (1)

**Soficity.** Suppose `N` is normal in `V` and sofic, `V/N` is amenable,
and every finitely generated subgroup of `N` has finite orbits on `X`.
Then `G` is sofic. A finite subset of `K x| N` lies in
`GL(F_2^O) x| N_0` with `N_0 <= N` finitely generated and `O` a finite
`N_0`-invariant union of the matrix supports. With
`rho : N_0 -> Sym(O)` the action,

```text
(A, h) |----> ((A, rho(h)), h)
```

is an injective homomorphism into the product of the **finite** group
`GL(F_2^O) x| rho(N_0)` with `N_0`. Soficity is closed under products,
subgroups, directed unions and extensions with amenable quotient
(Elek--Szabo, *On sofic groups*, Theorem 1), which finishes it. If `N_0`
is residually finite the displayed embedding is residually finite, so
finite-quotient regular actions separate every nonidentity element,
including those inside the matrix subgroup.

**No nontrivial finite normal subgroup**, provided every nonidentity
element of `V` moves infinitely many points. First, `K` has no nontrivial
finite quotient: in a finite quotient pick distinct `r, s` outside
`{i,j}` whose transvections `T_(ir), T_(is)` have equal images, which is
pigeonhole on infinitely many `r`; then

```text
[T_(ir) T_(is)^-1, T_(rj)] = T_(ij)
```

has trivial image, and conjugation kills every transvection. A finite
normal `F <= G` is therefore centralized by `K`, because `K ->
Aut(F)` has finite image. The representation `(A,v) |-> A P_v` on
`F_2^(X)` is faithful under the infinite-motion assumption, since
`A P_v = I` makes `P_v` finitary. Commuting with every off-diagonal
matrix unit forces an operator to be scalar, and the only invertible
scalar over `F_2` is one, so `F = 1`.

**Finite generation.** If `V` is finitely generated and transitive, so is
`G`: for a finite symmetric generating set `S`, the transvections in both
directions between `x_0` and each `s x_0 != x_0`, together with their
`V`-conjugates, are the directed edges of a connected graph on `X`, and
`[T_(ij), T_(jk)] = T_(ik)` along simple paths produces every
transvection.

**The kernel is simple.** `K` is the directed union of the `GL_n(F_2)`,
each simple for `n >= 3` over `F_2`, along injective maps, so a
nontrivial normal subgroup meets some `GL_n(F_2)` nontrivially, contains
it, and then contains every later stage. So `K` is an infinite, locally
finite, **simple** group.

## 3. Ascending HNN extensions

**Theorem 2.** Let `L` be a finitely generated Kazhdan group and
`alpha : L -> L` injective with `1 < [L : alpha(L)] < infinity`. Put
`V = <L, u | u l u^-1 = alpha(l)>`, `X = V/L`, let `B` be the kernel of
the coset action and `Q = V/B`. Then

```text
GL_fin(F_2^(V/L)) x| Q
```

is finitely generated, sofic, not MF, and has no nontrivial finite normal
subgroup, and (2) holds with `Q, bar L` in place of `V, L`. **No residual
finiteness of `L` is assumed.**

**Proof.** Build the HNN extension explicitly, avoiding a normal-form
citation. Let `N` be the direct limit of `L --alpha--> L --alpha--> ...`,
with elements `[l,j] = [alpha(l), j+1]`, multiplication in a common
stage, each stage embedded by injectivity. Then `[l,j] |-> [alpha(l), j]`
is an automorphism with inverse `[l,j] |-> [l,j+1]`; let `u` implement it
and `V = N x| <u>`. This has the displayed presentation, because in any
group satisfying those relations `[l,j] |-> u^-j l u^j` is well defined
and inverts the universal map. So `L_j = u^-j L u^j` increase with union
`N`.

`L` is commensurated by `L` and by `u`, hence by `V`; transitivity of
commensurability follows from
`[A : A cap C] <= [A : A cap B][B : B cap C]` and its mirror. So every
`L_j`-orbit on `V/L` is finite, of size `[L_j : L_j cap gLg^-1]`.

`B` is normal and contained in every conjugate of `L`, so `B <= L <= L_j`
and each `L_j/B` acts faithfully on `X` with finite orbits: finite orbit
actions separate its nonidentity elements, so it is residually finite,
hence sofic. Every finitely generated subgroup of `N/B` lies in some
`L_j/B` and has finite orbits, and `Q/(N/B)` is `Z`, which is amenable.
Section 2 gives soficity.

`bar L` is Kazhdan, being a quotient of `L`. Compression stays proper:
`B <= uLu^-1`, so the image of `uLu^-1` is `alpha(L)/B`, of index
`[L : alpha(L)] > 1` in `bar L`. The coset `L` is `bar L`-fixed and `uL`
is not, since `ell uL = uL` would put `ell` in `uLu^-1`; take `ell` in
`L` outside `uLu^-1`. Theorem 1 applies. Transitivity and finite
generation of `Q` give finite generation of the extension.

For infinite motion, `tau(gL) = gu^-1L` is well defined by
`uLu^-1 <= L`, surjective, and `Q`-equivariant, and the height
homomorphism `V -> Z` descends to heights on `X` that `tau` decreases. If
an element moves `x` it moves every `y` with `tau^m(y) = x`, by
equivariance, and surjectivity of `tau` supplies such `y` at every height
above `x`. So the faithful `Q`-action has infinite motion, and Section 2
excludes finite normal subgroups. QED

These are the coset actions of ascending HNN extensions; the Bass--Serre
tree has this vertex set and parent map, but no tree-action theorem is
needed.

**Arithmetic instance.** Take `L = Z^3 x| SL_3(Z)`, whose property (T)
is the established `affine-semidirect-sl3-source-has-property-t`, and
`alpha(b,A) = (mb, A)` for any `m >= 2`, of index `m^3`. Then
`V = Z[1/m]^3 x| (SL_3(Z) x Z)`, faithfully represented by the affine
matrices `[[m^k A, b],[0,1]]` since the upper-left determinant fixes `k`,
and residually finite by reduction modulo primes not dividing `m`.
Identifying `gL` with `g Z^3`, the stabilizer of `Z^3` is exactly `L`,
and `B = 1`: an affine map fixing every `v + m^j Z^3` has scale zero, and
then `(A-I)v + b` lies in the intersection of the `m^j Z^3`, which is
zero, for every `v`, forcing `A = I` and `b = 0`. So `Q = V` and

```text
D_G(L) = Rad_MF(G) = GL_fin(F_2^(V/L)),
```

with `G` finitely generated, sofic, not MF, and with no nontrivial finite
normal subgroup. The same runs for `Z^d x| SL_d(Z)`, `d >= 3`, given
property (T) of that group -- standard, and cited by the supplying note
to Cornulier, Proposition 1.1 -- but only the rank-three case is
established in this archive, so only it is claimed here.

## 4. Scope, and what this does not settle

The mechanism is **criterion (P) inside a subgroup, then ambient normal
closure**. The finite central witness is normal in `H`, not in `G`; its
ambient normal closure is infinite, locally finite and simple. This
settles the locally finite defect question for these displayed radicals
and **not** for arbitrary locally finite normal subgroups, so
`locally-finite-defect-subgroup-dies-in-every-corona` stays open.

The linear kernel is not a convenience. If `V` is MF,
`P = Sym_fin(X) x| V`, `H <= P`, and `A` is a normal Kazhdan subgroup of
`H` lying in a Kazhdan compression defect in `H`, then `A = 1`:
projection to `V` is an MF homomorphism, so it kills `A`, placing `A` in
the locally finite `Sym_fin(X)`; a Kazhdan group there is finitely
generated hence finite; its support union is finite and `H`-invariant, so
restriction is a homomorphism to a finite, hence MF, group that is
injective on `A` and must also kill it. That is
`kazhdan-criterion-is-inert-on-finitary-permutation-extensions`, already
established here. Characteristic two is what supplies an involution, and
a finitary permutation cannot play that role.

The reduced C*-algebra is neither simple nor uniquely tracial. Exhausting
`K` by finite subgroups `K_j`, the vector states of
`|K_j|^(-1/2) 1_(K_j)` converge on group elements to `1_K`, which is a
conjugation-invariant positive-definite function because `K` is normal,
so it is a trace distinct from the canonical one. Its closed trace-null
ideal is proper and contains `lambda(k) - 1 != 0` for `k != 1` in `K`.

## 5. Delta against what this archive already had

`finitary-linear-extension-kazhdan-defect-kills-kernel` already carries
the same configuration and the same subgroup-then-normal-closure
mechanism, and already cites `normal-kazhdan-defect-non-mf`. What is new:

1. **The two adjoined `V`-fixed points are gone.** The earlier statement
   needs `Y = X u {a,b}` with `a, b` fixed by `V`; this one runs inside
   the original action, using a finite permutation of the compressor's
   backward orbit. That is what makes canonical objects such as
   `GL_fin(F_2^(V/L)) x| Q` accessible, rather than an enlargement of
   them. The earlier claim is the special case `Y` of this one, so no
   second route into it is wired -- two routes proving one target by one
   argument is a defect, not extra support.
2. **The defect identity `D_G(L) = pi^-1(D_V(L))`**, which the earlier
   claim does not state at all, and the radical identity in the general
   form `pi^-1(Rad_MF(V))` rather than only `Rad_MF(G) = K` under an MF
   hypothesis on `V`.
3. **Soficity is proved.** The earlier claim explicitly declines it
   ("no soficity claim for (FL1) is made here").
4. **Finite generation, and a proof that there is no nontrivial finite
   normal subgroup.** The earlier claim asserts the latter as an aside
   without proof.
5. **The canonical HNN family with no residual finiteness hypothesis on
   `L`**, obtained by passing to the faithful quotient `Q`, and the
   arithmetic instance for every `m >= 2` rather than the single dyadic
   base.

Against the ordinary-wreath line landed earlier today
(`affine-perfect-lamp-wreath-has-locally-finite-mf-radical`,
`Rad_MF = A_5^(H/L)`), this family is better on four axes and not worse
on any that were claimed: the radical is **simple** as well as locally
finite; residual finiteness of the base is not needed; there are no
nontrivial finite normal subgroups; and the proof consumes only the
Lean-checked finite-central criterion instead of the commuting-conjugate
analysis. The wreath line keeps one thing this does not have, namely a
radical that is a restricted direct sum of copies of a prescribed finite
perfect group.

## 6. Provenance

The mathematics is a user-supplied note of 2026-09-08 revising an earlier
supplied finitary-linear argument, itself already landed here. The
transcription adds the archive comparison of Section 5, the simplicity of
`K`, the recheck below, and the restriction of the arithmetic instance to
the rank already established here.

Every displayed identity was recomputed rather than read: the four
products `A^2, B^2, BA, AB` and the vanishing of all length-three
products; `[y,d] = I + AB`; the four centrality checks for `z`; the
distinctness of the backward orbit; `[T_(ir)T_(is)^-1, T_(rj)] = T_(ij)`;
`[T_(ij),T_(jk)] = T_(ik)`; the action of `v = up` on `a, b, x`; both
inclusions of both identities in (2); the direct-limit automorphism and
its inverse; well-definedness and equivariance of `tau`; and `B = 1` in
the arithmetic instance. All check.

Elek--Szabo Theorem 1 is used as a citation for sofic permanence, as the
existing `dyadic-perturbation-soficity-proof` does for the same purpose;
this file does not independently verify that paper. Cornulier
Proposition 1.1 is **not** relied on: the arithmetic instance is stated
only at the rank whose property (T) is already established here. No Lean
declaration corresponds to Theorems 1 or 2; Cairn validates the
dependency graph, not these proofs.
