# Strong Atiyah over Qbar(z) off a countable set of transcendental numbers

Lane `ex-atiyah-torsion-free`, 2026-09-12. Supports the claim
`atiyah-base-change-holds-off-a-countable-set`.

The base change from `Qbar` to `C` is open outside sofic groups
(`strong-atiyah-base-change-algebraic-to-complex`). The graph's live route needs
Galois invariance of kernel dimensions
(`strong-atiyah-base-change-via-galois-invariance`). This note proves, for every
torsion-free group with Strong Atiyah over `Qbar`, that one transcendental
coefficient can fail only at countably many values. It also shows that
one-variable Galois invariance is exactly the emptiness of that countable set.
The proof uses no approximation of the group. It uses the division ring
`D_(Qbar[G])`, Jacobson's normal form over `D[x]`, and the linear independence of
eigenspaces in `U(G)`.

## 0. Conventions

* `U(G)` is the ring of operators affiliated to `N(G)`, with Lueck's dimension
  function on `U(G)`-modules. It is additive on direct sums and monotone on
  submodules, and `dim U(G)^n = n`.
* For a matrix `M` over `U(G)`, `dim ker M` means the dimension of the kernel of
  `M` acting on columns. For `M` over `C[G]` this is the von Neumann dimension of
  the `l^2`-kernel. Changing the side changes kernels of non-square matrices by
  the integer `m - n` and leaves integrality untouched.
* **Linnell's criterion** (Schick, arXiv:math/0001101v3, Lemma 3.4, as quoted in
  `atiyah-passes-to-torsion-free-elementary-amenable-extensions`): a torsion-free
  `G` satisfies Strong Atiyah over `K`, with `K` closed under complex
  conjugation, iff the division closure `D_(K[G])` of `K[G]` in `U(G)` is a skew
  field.
* `G` is torsion-free and satisfies Strong Atiyah over `Qbar`. Put
  `D = D_(Qbar[G])`, a skew field. Complex scalars are central in `U(G)`.

## 1. Theorem 1

For `A(x) in M_(m x n)(Qbar[G][x])`, let `r(A)` be the rank of `A(x)` over the
Ore skew field `D(x)` of the central polynomial ring `D[x]`, and put

```text
E_A = { z in C \ Qbar : dim ker A(z) != n - r(A) },       E_G = union over all A of E_A.
```

1. `E_A` is countable. Hence `E_G` is countable, since `Qbar[G][x]` is countable.
2. Let `z in C \ (Qbar ∪ E_G)`. Then `x -> z` extends to an embedding
   `D(x) -> U(G)`, whose image is the division closure of `Qbar(z)[G]`. So every
   matrix over `Qbar(z)[G]` has integral kernel dimension, and that dimension
   does not depend on which such `z` is used.
3. The following are equivalent:
   - **one-variable Galois invariance**: `dim ker A(z) = dim ker A(z')` for all
     `A` over `Qbar[G][x]` and all transcendental `z, z'`;
   - `E_G` is empty.
4. **Several variables.** Define `Sigma_s ⊂ C^s` as the set of `z` at which some
   `A` over `Qbar[G][x_1..x_s]` has `dim ker A(z) != n - r(A)`, with `r(A)` the
   rank over `D(x_1..x_s)`. It is a Borel set.
   - Over every tuple of algebraically independent `(z_1..z_(s-1))` outside
     `Sigma_(s-1)`, its section in the last coordinate is countable.
   - So `Sigma_s` is Lebesgue-null and meagre.
   - Outside `Sigma_s`, on algebraically independent tuples, `D(x_1..x_s)` embeds
     as the division closure of `Qbar(z_1..z_s)[G]`.

## 2. Proof of items 1-3

**Normal form.** `D[x]`, with `x` central and `D` a skew field, is a left and
right Euclidean domain, since leading coefficients are invertible. So every
matrix over it is equivalent to a diagonal one (Jacobson's normal form):

```text
P A(x) Q = diag(f_1, ..., f_r) (+) 0,     P in GL_m(D[x]),  Q in GL_n(D[x]),  f_i != 0.
```

Here `r = r(A)`, since `P` and `Q` stay invertible over `D(x)`.

**Specialization.** For `z in C`, evaluation `ev_z: D[x] -> U(G)`, `x -> z`, is
a ring homomorphism, because `z` is central. It maps `GL(D[x])` into `GL(U(G))`,
so

```text
dim ker A(z) = (n - r) + sum_i dim ker f_i(z).
```

**Countability (item 1).**
* **Reduce to a monic polynomial.** Write `f_i = c_i g_i` with `c_i in D^x` the
  leading coefficient and `g_i` monic of degree `l_i`. The companion matrix
  `C_i in M_(l_i)(D)` satisfies `g_i (+) I = E (x I - C_i) E'` with `E, E'` in
  `GL(D[x])`; the usual elementary operations use only that `x` is central. So
  `dim ker f_i(z) = dim ker (z I - C_i)`.
* **Eigenspaces are independent.** Let `z_1..z_p` be distinct. If
  `sum_j v_j = 0` with `v_j in ker(z_j - C_i)`, applying
  `prod_(j != 1) (C_i - z_j)` gives `prod_(j != 1)(z_1 - z_j) v_1 = 0`, so
  `v_1 = 0`. The kernels are therefore independent submodules of `U(G)^(l_i)`, and
  `sum_j dim ker(z_j - C_i) <= l_i`.
* **Conclusion.** Only countably many `z` give a nonzero kernel. So `E_A` lies
  in a countable union of countable sets.

**Item 2.** Let `z` be transcendental and outside `E_G`, and let `0 != f in D[x]`.
* **Linear representation.** Every element of the division closure has a linear
  representation `d = u B^-1 v`, with `B` square over `Qbar[G]` and invertible in
  `U(G)`, and `u, v` over `Qbar[G]`. Taking block sums over the coefficients of
  `f` gives `f(x) = U(x) B^-1 V`, with `B, V` over `Qbar[G]` and `U(x)` over
  `Qbar[G][x]`.
* **Schur complement.** Put `M(x) = [[B, V], [U(x), 0]]`. Since `B` is invertible
  in `U(G)` and in `D(x)`, the Schur complement gives
  `dim ker M(z) = dim ker f(z)` and `r(M) = size(B) + 1`, the last because `f` is
  invertible over `D(x)`. As `z` is not in `E_M`, `dim ker M(z) = 0`.
* **Consequences.** So `f(z)` is injective, hence invertible in `U(G)`, and in
  particular nonzero. Thus `ev_z` is injective on `D[x]` and sends nonzero
  elements to units. By the universal property of Ore localization it extends to
  `D(x) -> U(G)`.
* **The image.** It is a skew field containing `Qbar(z)[G]`. It is generated by
  `D` and `z`, both of which lie in the division closure of `Qbar(z)[G]`. So it
  equals that division closure.
* **Ranks.** Ranks over it are ranks over `D(x)` transported by an isomorphism:
  integers, independent of `z`.

**Item 3.** Assume invariance and let `z` be transcendental. For each `A`, choose a
transcendental `z'` outside the countable set `E_A`. Then
`dim ker A(z) = dim ker A(z') = n - r(A)`, so `z` is not in `E_G`. Conversely, if
`E_G` is empty, item 2 makes every transcendental value `n - r(A)`.

## 3. Proof of item 4

* **Borel.** `dim ker A(z)` is the decreasing limit of
  `tau(phi_k(A(z)^* A(z)))` for continuous `phi_k` decreasing to the indicator of
  `{0}`. So it is a Borel function of `z`, and a countable union gives a Borel set.
* **Induction.** Let `z' = (z_1..z_(s-1))` be algebraically independent and outside
  `Sigma_(s-1)`. By induction, `D_(s-1) = D(x_1..x_(s-1))` embeds in `U(G)` as a
  skew field. Rerun Section 2 with `D_(s-1)` in place of `D`, for the families
  `A(z', x_s)`. The rank over `D_(s-1)(x_s) ≅ D(x_1..x_s)` is `r(A)`, so the
  section of `Sigma_s` over `z'` is countable.
* **Size.** Algebraically dependent tuples lie in countably many proper
  subvarieties, a null meagre set. Fubini and Kuratowski--Ulam then make
  `Sigma_s` null and meagre. The embedding statement is Section 2 at the last step.

## 4. Consequences

* **Complex Strong Atiyah failures are rare.** Let `G` satisfy Strong Atiyah over
  `Qbar`. A matrix over `C[G]` whose coefficients lie in a purely transcendental
  extension `Qbar(z_1..z_s)` has integral kernel dimension unless `z` lies in
  the null meagre set `Sigma_s`. With one transcendental coefficient, the
  exceptions form the countable set `E_G`, which depends only on `G`.
* **The Galois-invariance hypothesis, located.** For one variable,
  `vn-rank-galois-invariant-for-torsion-free-groups` is equivalent to `E_G`
  being empty. Invariance asserts no integrality, but for these groups it is
  exactly the absence of countably many exceptional transcendental numbers.
* **Symmetries of `E_G`.** `E_G` is closed under preimages by nonconstant
  polynomial and Moebius maps with algebraic coefficients: substitute them into
  the family and clear denominators.
* **Not covered: algebraic extensions.** A field `F` algebraic over
  `Qbar(z_1..z_s)` needs `D(x_1..x_s) (x) F` to stay a skew field inside `U(G)`.
  That is Jaikin-Zapirain--Lopez-Alvarez's Conjecture 3 (arXiv:1810.12135v4, p. 35)
  for this `G`. The Riemann--Roch step of `galois-invariance-base-change-proof`
  uses invariance under the conjugate embeddings of `F`, which countability
  arguments do not provide.
* **Under the determinant conjecture.** `E_G` contains no algebraically Liouville
  number, and each point of `E_G` is badly approximable by algebraic numbers of
  every bounded degree. See `determinant-conjecture-excludes-liouville-atiyah-exceptions`
  and `research/artifacts/atiyah-liouville-base-change-2026-09-12.md`.

## 5. Model tests

* **The hypothesis matters.** For `G = Z/2` and `A(x) = x (1 + s)/2`,
  `dim ker A(z) = 1/2` for every `z != 0`. `D` is not a skew field and the
  integrality conclusion fails.
* **The exceptional set is not vacuous in general tracial settings.**
  - Let `t` be a self-adjoint operator with no atoms at algebraic points and an
    atom of mass `1/2` at `pi`. Take `D = Qbar(t)`, a skew field of affiliated
    operators whose rank function is integral.
  - Then `t - pi` has a kernel of dimension `1/2`, so `pi` is exceptional.
  - What must rule this out for group algebras is group structure, not the
    algebra of `D`.
* **A real object.** For sofic `G` satisfying Strong Atiyah over `Qbar`, the base
  change of Jaikin-Zapirain (GAFA 29 (2019), Theorem 1.1) gives `E_G = ∅`.

No novelty is claimed for the ingredients. Jacobson's normal form and the
independence of eigenspaces are standard. The countability of the exceptional
set, and its identification with one-variable Galois invariance, are recorded
here because the graph's base-change region lacked them.
