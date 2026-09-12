# Completion hosts for Boone--Higman: what a recursion buys, and what kills it

Lane `bh-steinberg-hosts`, 2026-09-12. Target:
`simple-inputs-have-fp-elementary-leavitt-tensor-hosts`. For an infinite,
computably presented simple group `S`, find a finitely presented central simple
algebra `B` with `S <= B^x` whose Leavitt tensor has a finitely normally
generated Steinberg kernel, for instance because `B` is regular coherent.

Boone--Higman stays open. This note proves four things and records the exact
shape of what is still missing.

- **Theorem A.** Nekrashevych-type completions `O_psi` of any finitely
  presented algebra `B` along an injective unital recursion
  `psi : B -> M_d(B)` are finitely presented and contain `B`. Unlike the group
  case, this imposes no residual finiteness.
- **Theorem B.** A saturated invariant ideal of `B` stays a proper ideal of
  `O_psi`, so `O_psi` is not simple.
- **Theorem C.** If `psi` comes from a group wreath recursion (the monomial
  case), every simple completion kills the kernel of the tree action. In
  particular it kills every subgroup without finite quotients, which includes
  every infinite simple input.
- **Theorem D.** A left coherent host that contains a group algebra flatly, with
  the group algebra as a module summand, forces every finitely generated
  subgroup to be of type `FP_infinity`. Inputs containing `Z wr Z` therefore
  have no such hosts.

All four proofs are elementary and self-contained. The one external fact used is
the Bieri--Eckmann/Chase criterion in Theorem D, stated there.

## 0. Setting

`K` is a field, `d >= 2`, `L_d = L_K(1,d)` has generators `s_1..s_d`, `s_1*..s_d*`
with `s_i* s_j = δ_ij` and `Σ s_i s_i* = 1`. For a unital `K`-algebra `B` and a
unital algebra homomorphism `psi : B -> M_d(B)`, put

```text
O_psi = ( B * L_d ) / ( b = Σ_(i,j) s_i psi(b)_(ij) s_j*  for b in B ).
```

Examples:
- `B = K`, `psi(c) = c I_d`: `O_psi = L_d`.
- `psi(b) = diag(b, ..., b)`: the relation says `b` commutes with every `s_i`
  and `s_i*`, so `O_psi = B ⊗ L_d`.
- A self-similar group `P` with wreath recursion `g |-> (π_g; g|_1, ..., g|_d)`,
  `psi(g) = Σ_x E_(π_g(x), x)(g|_x)`: `O_psi` is the Nekrashevych algebra
  presented by `g s_x = s_(g(x)) g|_x`.

Conventions:
- **Words.** `s_u = s_(u_1) ... s_(u_n)` for a word `u` of length `n`.
- **Normal form.** The relations give `b s_j = Σ_i s_i psi(b)_(ij)` and
  `s_i* b = Σ_j psi(b)_(ij) s_j*`. So every element of `O_psi` is a sum of terms
  `s_u b s_v*`.

## 1. Theorem A: finite presentation, embedding, strong grading

**Theorem A.** Let `psi : B -> M_d(B)` be a unital homomorphism.
1. *(Finite presentation.)* If `B = K<X | R>` with `X`, `R` finite, then
   `O_psi = K<X, s_i, s_i* | R, Leavitt relations, x = Σ s_i psi(x)_(ij) s_j* (x in X)>`.
   In particular `O_psi` is finitely presented.
2. *(Embedding.)* If `psi` is injective, the canonical map `B -> O_psi` is
   injective.
3. *(Core.)* Put `B_n = M_(d^n)(B)`, indexed by words of length `n`, with
   `φ_n : B_n -> B_(n+1)` given by `φ_n(x)_(uw, vz) = psi(x_(uv))_(wz)`, and let
   `B_inf = lim B_n`. If `psi` is injective, `x |-> Σ_(u,v) s_u x_(uv) s_v*` embeds
   `B_inf` in `O_psi` as the degree-zero part of the grading
   `deg s_i = 1`, `deg s_i* = -1`, `deg B = 0`. This grading is strong.

*Proof of 1.* `Ψ(b) = Σ s_i psi(b)_(ij) s_j*` is a unital homomorphism
`B -> O`. It is the composite of `psi`, the entrywise map
`M_d(B) -> M_d(O)`, and the matrix-unit isomorphism `M_d(O) -> O`,
`(a_(ij)) |-> Σ s_i a_(ij) s_j*`. That last map is multiplicative because
`s_j* s_k = δ_(jk)`. The set where `Ψ` agrees with the inclusion is a subalgebra.
It contains `X`, hence it is all of `B`. `∎`

*Proof of 2.* We build a unital algebra `Q` and a homomorphism `O_psi -> Q` whose
restriction to `B` is injective.

- **(a) Core and corner map.**
  - The maps `φ_n` are unital, and injective since `psi` is, so `B` embeds in
    `B_inf`.
  - Define `α_n : B_n -> B_(n+1)` by putting `x` in the block of words beginning
    with the letter `1`: `α_n(x)_(1u, 1v) = x_(uv)`, all other entries `0`.
  - Both composites send `x` to the matrix with entries `psi(x_(uv))_(wz)` at
    `(1uw, 1vz)` and `0` elsewhere, so `φ_(n+1) α_n = α_(n+1) φ_n`.
  - So the `α_n` induce an injective, non-unital homomorphism
    `α : B_inf -> B_inf` with `α(1) = p := E_(11)` in `B_1`.
  - `α` maps onto the corner `p B_inf p`, because `p B_(n+1) p = α_n(B_n)`.
- **(b) Dilation.** Let `A = lim( B_inf --α--> B_inf --α--> ... )`, a non-unital
  ring. Write `[a]_k` for the class of `a` at stage `k`, so `[a]_k = [α a]_(k+1)`.
  - `σ([a]_k) = [a]_(k+1)` is a well-defined automorphism of `A`, with inverse
    `[a]_(k+1) |-> [a]_k`.
  - `σ([α a]_0) = [α a]_1 = [a]_0`, so `σ^-1([a]_0) = [α a]_0`.
  - `a |-> [a]_0` is injective, since `α` is.
- **(c) Skew Laurent ring.**
  - Let `R = ⊕_(k in Z) A t^k` with `(a t^k)(b t^l) = a σ^(-k)(b) t^(k+l)`. It is
    associative because `σ` is an automorphism.
  - Put `p_0 = [1]_0` and `Q = p_0 R p_0`, a unital ring with unit `p_0`.
  - Define `t_+ = t p_0` and `t_- = p_0 t^-1`. Since `t [a]_0 t^-1 = [α a]_0`, in
    `Q` we have:
    - `t_- t_+ = p_0`;
    - `t_+ t_- = [α 1]_0 = [p]_0`;
    - `t_+ [a]_0 = [α a]_0 t_+`;
    - `[a]_0 t_- = t_- [α a]_0`.
- **(d) The homomorphism.** Send `b |-> [b]_0`, `s_i |-> [E_(i1)]_0 t_+` and
  `s_i* |-> t_- [E_(1i)]_0`, with `E_(ij)` the matrix units of `B_1`. Then:
  - `s_i* s_j |-> t_- E_(1i) E_(j1) t_+ = δ_(ij) t_- p t_+ = δ_(ij) (t_- t_+)^2 = δ_(ij) p_0`.
  - `Σ s_i s_i* |-> Σ E_(i1) t_+ t_- E_(1i) = Σ E_(i1) p E_(1i) = Σ E_(ii) = 1 = p_0`.
  - For `c in B`, `t_+ c t_- = α(c) t_+ t_- = α(c) p = α(c)`, the matrix with `c`
    at `(1,1)`. Hence
    `Σ s_i psi(b)_(ij) s_j* |-> Σ E_(i1) α(psi(b)_(ij)) E_(1j) = psi(b) = φ_0(b)`,
    which is `[b]_0` in `A`.

  So the relations of `O_psi` hold in `Q`, and `B -> O_psi -> Q` is `b |-> [b]_0`,
  which is injective. `∎`

*Proof of 3.*
- **Homomorphism.** `x |-> Σ s_u x_(uv) s_v*` is multiplicative on each `B_n`,
  and compatible with `φ_n` by the defining relation. So it is a homomorphism
  `B_inf -> O_psi` landing in degree zero.
- **Onto degree zero.** By the normal form, degree zero is spanned by terms
  `s_u b s_v*` with `|u| = |v|`.
- **Injective.** Compose with the map of part 2. `s_i b s_j* |-> E_(i1) α(b) E_(1j)`,
  which is `b` at position `(i,j)` of `B_1`. By induction on `n`, `s_u b s_v*` maps
  to `b` at position `(u,v)` of `B_n`: the matrix units `E_(i1)` of `B_1` sit in
  `B_n` as `E_(i1) ⊗ I`, because `psi(1) = I`. So the composite is `x |-> [x]_0`,
  which is injective.
- **Strong grading.** `1 = Σ s_i s_i*` lies in `O_1 O_(-1)`, and `1 = s_1* s_1`
  lies in `O_(-1) O_1`. `∎`

**What Theorem A does not give.** It gives no simplicity, and no `K`-theory.

**Contrast with groups.** Self-similar hosts contain only residually finite groups
(`self-similar-hosts-contain-only-residually-finite-groups`), because a group
acting on a rooted tree acts through finite quotients. Theorem A has no such
constraint: `B` embeds in `O_psi` as soon as the algebra recursion is injective.
Theorem C shows that the constraint comes back for monomial recursions, so any
new case must use genuinely non-monomial `psi`.

## 2. Theorem B: saturated invariant ideals block simplicity

**Theorem B.** Let `psi : B -> M_d(B)` be unital, and let `I` be an ideal of `B`
with `psi^-1(M_d(I)) = I`. Then the ideal `J` of `O_psi` generated by `I`
satisfies `J ∩ B = I`. If `0 != I != B`, then `O_psi` is not simple.

*Proof.* `I ⊆ psi^-1(M_d(I))` gives `psi(I) ⊆ M_d(I)`, so `psi` induces
`psi_bar : B/I -> M_d(B/I)`. It is injective because
`psi(b) in M_d(I) => b in I`. Comparing presentations, `O_psi / J = O_(psi_bar)`,
and Theorem A.2 embeds `B/I` in it. So `J ∩ B = I`. If `I != 0` then `J != 0`, and
if `I != B` then `1 notin J`. `∎`

**Consequences.**
- *Simplicity is not functorial.* For `psi = diag(b, ..., b)`, every ideal is
  saturated and invariant, so `B ⊗ L_d` is simple only if `B` is, as expected.
  Any construction `B |-> (B, psi_B)` natural in `B` passes to quotients `B/I`
  and cannot be simple.
- *What simplicity requires.* The saturated invariant closure of every nonzero
  ideal must be all of `B`. A recursion must therefore use data specific to `B`,
  and a simple completion must carry the word-problem complexity of `B`. This is
  consistent with `no-fp-simple-algebra-hosts-every-decidable-algebra`.

## 3. Theorem C: monomial completions are residually finite on coefficients

A *wreath recursion* on a group `P` is a homomorphism
`P -> S_d wr P`, `g |-> (π_g; g|_1, ..., g|_d)`. Being a homomorphism means
`π_(gh) = π_g π_h` and `(gh)|_x = g|_(h(x)) h|_x`. The recursion need not be
faithful. The induced monomial recursion on `K[P]` is
`psi(g) = Σ_x E_(π_g(x), x)(g|_x)`.

**Theorem C.** Let `N` be the kernel of the action of `P` on the rooted tree `X^*`,
where `X = {1..d}` and the action is defined by `g(xw) = π_g(x) g|_x(w)`. Let `J`
be the ideal of `O_psi` generated by `{g - 1 : g in N}`. Then `J != O_psi`.
Consequently, if `O_psi` is simple:
- the canonical map `P -> O_psi^x` factors through the residually finite group
  `P/N`;
- every subgroup of `P` with no nontrivial finite quotient, in particular every
  infinite simple subgroup, maps to `1`.

*Proof.*
1. **Action.** The recursive formula defines homomorphisms `P -> Sym(X^n)` for
   every `n`, and `N` is the intersection of their kernels. `P/N` acts faithfully
   on the locally finite rooted tree, so its level stabilizers have finite index
   and it is residually finite.
2. **`N` is restriction-closed.** For `g in N`, `π_g = id`, and
   `xw = g(xw) = x g|_x(w)` for all `w`, so `g|_x in N`.
3. **The recursion descends.** For `n in N`, `π_(gn) = π_g` and
   `(gn)|_x = g|_(n(x)) n|_x = g|_x n|_x in g|_x N`. So `P/N` inherits a wreath
   recursion `psi_bar`, and comparing presentations gives
   `O_psi / J = O_(psi_bar)`.
4. **`O_(psi_bar) != 0`.** Let `V` be the vector space with basis `X^ω`, the
   infinite words.
   - Put `s_x(w) = xw`, `s_x*(yw) = δ_(xy) w`, and let `g` act by the tree action
     extended to infinite words. `N` acts trivially, so this is an action of `P/N`.
   - The Leavitt relations hold, because every infinite word begins with exactly
     one letter.
   - `g s_x (w) = g(xw) = π_g(x) g|_x(w) = s_(π_g(x)) g|_x (w)`, which is the
     defining relation `g = Σ_x s_(π_g(x)) g|_x s_x*`.
   - So `O_(psi_bar)` has a nonzero unital representation, and `1 != 0` in it.
5. **Conclusion.** If `O_psi` is simple, then `J = 0`, because `J` is proper by
   step 4. A group with no nontrivial finite quotient acts trivially on each
   finite level, so it lies in `N`. `∎`

**Reading.**
- *The algebra form of the residual finiteness fence.* A simple Nekrashevych
  completion sees its coefficient group only through the tree action. Infinite
  simple inputs cannot enter through `K[P]`.
- *Where V comes from.* The Röver--Nekrashevych group `V_d(P)` lies in
  `O_psi^x` through prefix-exchange units `Σ s_(u_i) g_i s_(v_i)*`. That is
  condition (R2) of `decidable-groups-embed-in-rover-nekrashevych-hosts`, not a
  coefficient embedding.
- *So the new mechanism of Theorem A requires non-monomial `psi`.*
  - Such a `psi` comes from a subalgebra `θ(B)`, `θ` an injective endomorphism,
    over which `B` is free of rank `d`: take the matrix of left multiplication in
    a basis.
  - It is monomial exactly when `θ` comes from a virtual endomorphism of a group.
  - For simplicity, by Theorem B, the saturated invariant closure of `S - 1` must
    reach `1`. For example, some entry of some `psi^n(s) - 1` could be a unit. A
    diagonal recursion on `S` never does this.

## 4. Theorem D: coherent flat group-algebra hosts force type `FP_infinity`

**Theorem D.** Let `S` be a finitely generated group and `B` a left coherent
`K`-algebra with `K[S] ⊆ B` a unital subalgebra. Suppose that `B` is flat as a
right `K[S]`-module and that `K[S]` is a direct summand of `B` as a right
`K[S]`-module.
1. Every finitely generated subgroup `H <= S` is of type `FP_infinity` over `K`.
2. If `B` is moreover left regular (every finitely presented left module has
   finite projective dimension), and `K[S]` is a direct summand of `B` as a
   `K[S]`-bimodule, then `cd_K S < infinity`.

*External inputs.*
- **Chase.** `B` is left coherent iff every direct product `Π B` is flat as a
  right `B`-module.
- **Bieri--Eckmann.** A left `R`-module `M` is of type `FP_n` iff
  `Tor_k^R(Π R, M) -> Π Tor_k^R(R, M)` is bijective for `k < n` and surjective for
  `k = n`. See Bieri, *Homological Dimension of Discrete Groups*, Theorem 1.3.
  For `n = 1` this is Lenzing's criterion.

*Proof of 1.*
1. **Reduce to `S`.** `K[S]` is free as a right `K[H]`-module on a set of coset
   representatives containing `1`. So `B` is flat over `K[H]`, since
   `B ⊗_(K[H]) - = B ⊗_(K[S]) (K[S] ⊗_(K[H]) -)`, and `K[H]` is a summand of `B`.
   It is enough to treat `H = S`.
2. **The trivial module induces up.** `K = K[S]/I_S`, and `I_S` is generated by
   `s_i - 1` for finitely many generators, so `K` is finitely presented. Hence
   `M = B ⊗_(K[S]) K` is a finitely presented left `B`-module.
3. **Vanishing over `B`.** Flat base change gives
   `Tor_k^(K[S])(N, K) = Tor_k^B(N, M)` for right `B`-modules `N`. For `N = Π B`,
   which is flat by Chase, this vanishes for `k >= 1`. For `k = 0`, Lenzing's
   criterion applies because `M` is finitely presented.
4. **Descend.** `Π B = Π K[S] ⊕ Π C` as right `K[S]`-modules. So
   `Tor_k^(K[S])(Π K[S], K)`, a summand of step 3, vanishes for `k >= 1`. With
   finite presentation of `K`, Bieri--Eckmann gives `FP_infinity`. `∎`

*Proof of 2.*
1. **Shapiro.** `B ⊗_(K[S]) -` is exact, preserves projectives, and is left
   adjoint to restriction. So `Ext^i_(K[S])(K, Res W) = Ext^i_B(M, W)` for left
   `B`-modules `W`. This is `0` for `i > pd_B M < infinity`.
2. **Coinduction.** Take `W = Hom_(K[S])(B, N)`, a left `B`-module through right
   multiplication on `B`. If `B = K[S] ⊕ C` as bimodules, then `N = Hom(K[S], N)`
   is a `K[S]`-summand of `Res W`. So `Ext^i_(K[S])(K, N) = 0` for `i > pd_B M`
   and every `N`. `∎`

**Corollary D1 (no universal flat coherent hosts).** `Z wr Z` is not of type `FP_2`
over any field `K`, so no left coherent algebra contains `K[S]` flatly with a
right summand whenever `S ⊇ Z wr Z`. Since `Z wr Z` has solvable word problem and
must lie in some input of `boone-higman-iff-infinite-simple-inputs`, no host
family of this shape serves the conjecture.

*Proof that `Z wr Z` is not `FP_2(K)`.* Write `Z wr Z = A ⋊ Z` with
`A = ⊕_(i in Z) Z e_i`. In the Lyndon--Hochschild--Serre spectral sequence only
the columns `p = 0, 1` are nonzero, so `E^inf_(0,2) = E^2_(0,2) = H_0(Z; H_2(A;K))`
injects into `H_2(Z wr Z; K)`. Now `H_2(A;K) = Λ^2(K^(Z))`, and the shift permutes
the basis `e_i ∧ e_j` (`i < j`) freely, with orbits indexed by `j - i >= 1`. So
the coinvariants are infinite-dimensional. Type `FP_2(K)` would force `H_2(G;K)`
to be finite-dimensional. `∎`

**Corollary D2.** In characteristic `p`, a left regular coherent host with a
bimodule summand excludes every input with an element of order `p`, because
`cd_(F_p)(Z/p) = infinity`. Over `F_2`, the field of Khanh's criterion, that
excludes every input containing an involution.

**Scope.**
- *The group-algebra premise.* `decidable-group-algebras-have-fp-central-simple-hosts`
  suggests regular supercoherence as a sufficient condition. By D1, regular
  coherent hosts cannot contain `F_2[G]` flatly with a summand, e.g. as a free
  module with `1` in a basis, once `G ⊇ Z wr Z`. Hosts built as crossed products,
  free products or HNN extensions over `F_2[G]` have exactly that shape.
- *No conflict with unit hosts.* `L_2` is regular coherent and contains `V`, and
  `V ⊇ Z wr Z`. The canonical map `F_2[V] -> L_2` has a kernel
  (`full-group-algebra-to-steinberg-algebra-not-injective`), so Theorem D does not
  apply. The unit-only form of `simple-inputs-have-fp-elementary-leavitt-tensor-hosts`
  is therefore forced, not only permitted.
- *Trust.* Theorem D is folklore-level homological algebra. No novelty is claimed
  for it, and the bounded search here did not locate a source stating it.
