# The centralizer of a north--south Thompson unit in the binary Leavitt algebra

Lane `ex-q34-leavitt-hs`, 2026-09-12. Complete written proofs; no computation is used.

## 0. Statement

Let `R = L_(F_2)(1,2)`, `Q = R^x`, and let

```text
c = s_00 t_0 + s_01 t_10 + s_1 t_11,
```

the Thompson unit `0 gamma -> 00 gamma`, `10 gamma -> 01 gamma`, `11 gamma -> 1 gamma`.
Here `s_00 t_0 = S[00]T[0]`, in the convention of `experiments/nonsofic-certificates/leavitt.py`.

**Theorem.** For every integer `a != 0`:
1. `C_R(c^a) = F_2[c, c^-1]`, and `t -> c` identifies it with the Laurent polynomial
   ring `F_2[t, t^-1]`;
2. `C_Q(c^a) = <c>`;
3. if `g` is in `Q` and `g c^a g^-1 = c^b` with `b != 0`, then `b = a` or `b = -a`;
4. `<c>` has index at most `2` in its normalizer `N_Q(<c>)`, and
   `g <c> g^-1 cap <c> = 1` for every `g` outside `N_Q(<c>)`;
5. `L(<c>)` is a maximal abelian subalgebra of the group von Neumann algebra `L(Q)`.

**Corollary.** No subgroup of `Q` isomorphic to `H_3(Z)` has a central commutator
conjugate in `Q` to a nonzero power of `c`. No subgroup `<x, t | t x t^-1 = x^k>` with
`|k| >= 2` has `x` conjugate to a nonzero power of `c`.

*Proof of the corollary.* Conjugating, we may take the commutator or `x` to be `c^a`.
- A Heisenberg pair `u, v` with `[u,v] = c^a` central lies in `C_Q(c^a) = <c>`, which is
  abelian. So `[u,v] = 1`, a contradiction.
- `t c^a t^-1 = c^(ak)` contradicts item 3. ∎

## 1. Set-up

- **The module.** `C` is the Cantor space `{0,1}^N` with the Bernoulli `(1/2,1/2)` measure
  `mu`. `M = C(C, F_2)` is the space of locally constant functions. `R` acts on `M` by
  `(S[alpha]T[beta] f)(x) = 1_[alpha](x) f(beta sigma^|alpha| x)`.
  This is a unital left module, and it is faithful because `R` is simple
  (`leavitt-algebras-l-k-1-n-are-simple`). A Thompson unit `h` acts by
  `(h f)(x) = f(h^-1 x)`.
- **Normal form and depth.** Every `x` in `R` has a unique normal form, a finite set of
  pairs `(alpha, beta)` not both ending in `1`
  (`leavitt-normal-form-decides-unit-words-proof`). Its depth is `N(x) = max(|alpha|, |beta|)`
  and `T(x)` is its number of terms.
- **Dynamics of `c`.** `c` fixes `p = 0^infinity`, which is attracting, and `q = 1^infinity`,
  which is repelling. Put `D = [10]`. Then `c^k D = [0^k 1]` for `k >= 1` and
  `c^-k D = [1^(k+1) 0]` for `k >= 1`, and

  ```text
  C - {p, q} = disjoint union over k in Z of c^k D.
  ```

  On `D`, `c^k` is the prefix replacement `10 -> 0^k 1` for `k >= 1`, and
  `mu(c^k U) = 2^-(k-1) mu(U)` for every clopen `U <= D` and `k >= 0`.
- **The flow module.** `M_flow` is the space of `f` in `M` that vanish on a neighbourhood
  of `p` and of `q`. It equals the finite sums of pieces in `M_(c^k D)`. The map
  `c^k -> t^k` makes `M_flow ~= M_D tensor F_2[t, t^-1]`, a free, hence faithful,
  `F_2[t^(+-1)]`-module.

**Lemma 1 (support measure).** For `x` in `R` and `f` in `M`,
`mu(supp(x f)) <= T(x) 2^N(x) mu(supp f)`.

*Proof.* `supp(S[alpha]T[beta] f)` is the image of `supp f cap [beta]` under the prefix
replacement `beta -> alpha`, which multiplies measure by `2^(|beta| - |alpha|) <= 2^N`.
Take the union over the terms. ∎

**Lemma 2 (killing the flow kills everything).** If `x` in `R` annihilates `M_flow`, then
`x = 0`.

*Proof.*
1. For a clopen `A` avoiding `p` and `q`, let `e_A` be the idempotent acting as
   multiplication by `1_A`. Then `x e_A M <= x M_flow = 0`, so `x e_A = 0` by
   faithfulness.
2. Let `xi` be an aperiodic sequence and `N_xi` the Chen module on its tail class, with
   basis `e_eta` for `eta` tail equivalent to `xi` and `S[alpha]T[beta] e_(beta w) = e_(alpha w)`.
3. Every such `eta` is aperiodic, so it differs from `p` and `q` and has a clopen
   neighbourhood `A` avoiding both. Then `x e_eta = x e_A e_eta = 0`.
4. So `x` annihilates the nonzero module `N_xi`. Its annihilator is a proper two-sided
   ideal, hence `0` by simplicity, and `x = 0`. ∎

## 2. Centralizers

Fix `a != 0` and `g` in `R` with `g c^a = c^a g`. Commuting with `c^a` is the same as
commuting with `c^-a`, so assume `a > 0`. Write `N = N(g)` and `T = T(g)`.

**Step 1: `g M_flow <= M_flow`.**
1. Let `f` be in `M_flow` and put `h = g f`. Suppose `h` does not vanish near `p`. Being
   locally constant, `h = 1` on some cylinder `[0^K]`.
2. For `m >= 1`, `c^(-am) h = h o c^(am)` is `1` on `c^(-am)[0^K]`. Every point other than
   `q` enters `[0^K]` under forward iteration of `c`, uniformly off each neighbourhood
   of `q`. So `mu(supp(c^(-am) h)) -> 1`.
3. Also `c^(-am) h = g (c^(-am) f)`. The support of `c^(-am) f = f o c^(am)` lies in
   `c^(-am)(supp f)`, a union of boundedly many domains `c^(i - am) D`. Their total
   measure tends to `0`. By Lemma 1, so does `mu(supp(g c^(-am) f))`.
4. This contradicts step 2. Near `q` the same argument works with `c^(+am)`. ∎

**Step 2: the coefficients.** Let `f` be in `M_D`, written `f(10 gamma) = F(gamma)`. Fix
`k > N + 1`. Then `c^(ak) f` is supported on `[0^(ak) 1]`, with value `F(gamma)` at
`0^(ak) 1 gamma`.
- **Which terms contribute.** A term `(alpha, beta)` of `g` contributes at `x` only if
  `beta sigma^|alpha| x` lies in `[0^(ak) 1]`. Since `|beta| <= N < ak`, this forces
  `beta = 0^b` and `x = alpha 0^(ak-b) 1 gamma`, and the contributed value is `F(gamma)`.
- **Terms with a `1` in `alpha`.** The point `x` then begins with `0^n 1` for some
  `n < |alpha|`, or with `1^n 0` for some `n <= |alpha|`. So it lies in a domain `c^i D`
  with `|i| <= N`.
- **Terms with `alpha = 0^a'`.** The point `x` lies in `c^(ak + a' - b) D`, and the
  contribution is `c^(ak + a' - b) f`.

By Step 1 and commutation, `g c^(ak) f = c^(ak) g f` lies in `M_flow`, supported in the
domains `c^(ak + j) D` over the finitely many `j` for which `g f` meets `c^j D`. For large
`k` these domains are disjoint from all `c^i D` with `|i| <= N`. So the terms with a `1`
in `alpha` sum to zero, and

```text
c^(ak) g f = g c^(ak) f = sum_j eps_j c^(ak+j) f,     eps_j = #{ (0^a', 0^b) in NF(g) : a' - b = j } mod 2 .
```

Applying `c^(-ak)` gives `g f = p_g(c) f` for every `f` in `M_D`, where
`p_g(t) = sum_j eps_j t^j`. The same computation starting from `c^i f` with `0 <= i < a`
gives `g c^i f = p_g(c) c^i f`. By `c^a`-equivariance, `g = p_g(c)` on all of `M_flow`.

**Step 3: conclusion.** The element `x = g - p_g(c)` annihilates `M_flow`, so `x = 0` by
Lemma 2. Hence `C_R(c^a) <= F_2[c, c^-1]`, and the reverse inclusion is clear. On the
faithful free module `M_flow` the element `p(c)` acts as `p(t)`, so
`F_2[c^(+-1)] ~= F_2[t^(+-1)]`. This proves item 1.

The units of `F_2[t^(+-1)]` are the monomials `t^k`. So a unit `g` commuting with `c^a` is
a power of `c`, which proves item 2.

## 3. Conjugate powers

Let `g` be in `Q` with `g c^a g^-1 = c^b`, where `a, b != 0`. Suppose first that
`a, b > 0`. Let `f = 1_D` and `h = g f`, and let `N`, `T` and `N'`, `T'` be the depths and
term counts of `g` and `g^-1`.
- `supp(c^(am) f) = c^(am) D` has measure exactly `2^-(am-1) mu(D)`.
- **Case A: `h` does not vanish near `q`.** Then `supp(c^(bm) h)` contains
  `c^(bm)` of a neighbourhood of `q`, so its measure tends to `1`. But
  `c^(bm) h = g c^(am) f` has support of measure at most `T 2^N 2^-(am-1) mu(D) -> 0`.
  Contradiction.
- **Case B: `h` vanishes near `q`.** Then `supp h` lies in `[0^K]` together with finitely
  many domains `c^i D`, and `mu(supp(c^(bm) h)) <= C 2^(-bm)`. From
  `c^(am) f = g^-1 c^(bm) h` and Lemma 1,
  `2^-(am-1) mu(D) <= T' 2^N' C 2^(-bm)` for all `m`, so `b <= a`.
- **The other inequality.** Applying the same argument to `g^-1 c^b g = c^a` gives
  `a <= b`. So `a = b`.

If `a > 0 > b`, use `c^-1`, the north--south unit with attractor `q`: its domains
`c^-k D` have measures `2^-(k+2)`, and the same two cases give `a = |b|`. The case
`a < 0` follows by inverting both sides. This proves item 3.

**Item 4.**
1. Conjugation gives a homomorphism `N_Q(<c>) -> Aut(Z) = {+-1}`. Its kernel is
   `C_Q(c) = <c>`, so the index is at most `2`.
2. If `g c^a g^-1 = c^b` for some `a, b != 0`, then `b = +-a` by item 3.
3. If `b = a`, then `g` is in `C_Q(c^a) = <c>`.
4. If `b = -a`, then `g^2` commutes with `c^a` and `g c^a g^-1 = c^-a`. So `g` normalizes
   `C_Q(c^a) = <c>`.
5. Hence a nontrivial intersection `g <c> g^-1 cap <c>` puts `g` in `N_Q(<c>)`.

**Item 5.** The relative commutant of `L(<c>)` in `L(Q)` is spanned, in `l^2`, by the
elements `g` whose `<c>`-conjugacy orbit is finite. Such `g` satisfy `c^n g c^-n = g` for
some `n != 0`, so `g` lies in `C_Q(c^n) = <c>` by item 2. ∎

## 4. Scope

- **What this settles for the Heisenberg question.** The theorem, with item 3,
  supersedes the flow-splitting outline on
  `leavitt-unit-group-has-no-integer-heisenberg-subgroup`. Neither the center of a Heisenberg
  subgroup nor the base element of a Baumslag--Solitar subgroup can be conjugate to a power
  of `c`.
- **What it does not settle.** A Heisenberg center that is a genuinely linear unit, not
  conjugate to a Thompson element, has no attractor. Steps 1 and 2 use points of `C`
  through the attractor and the fundamental domain, and they do not apply to it.
- **Where the obvious algebraic invariant fails.** Over a commutative coefficient ring
  of characteristic two, the central element `t` of `A[t^(+-1)]^x` is detected by a
  determinant degree. Here `K_0(R) = 0`, so by Bass--Heller--Swan the class of `t` in
  `K_1(R[t^(+-1)])` vanishes. No `K`-theoretic homomorphism can replace the
  finite-depth argument above.
- **Other Thompson units.** The proof uses only the north--south dynamics of `c`, the
  fundamental domain, and the prefix form of `c` near its attractor. It adapts to other
  north--south Thompson units with full support. That extension is not written here.
