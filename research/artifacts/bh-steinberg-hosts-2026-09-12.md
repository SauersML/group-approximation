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
