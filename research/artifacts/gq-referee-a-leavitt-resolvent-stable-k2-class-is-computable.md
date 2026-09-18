# Referee report (gq-referee-a, proof-gap lens): the Leavitt resolvent stable K_2 class is computable

**Reviewed:** `leavitt-resolvent-stable-k2-class-is-computable` and its `-proof` (lane gq-infinite-primes, fd522c4d1),
read on origin/main.

**Verdict: PASS.** Items 1–4 and the general-principle remark hold, and I found no gap. There are two nits.

## The three points the author asked about
- **Equality in `St_M(R_L)` is recursively enumerable without finite presentation.**
  - Take generators `x_ij(u)` for all ring words `u`, and these relations:
    - `x_ij(u) = x_ij(u')` whenever `u = u'` in `R_L`;
    - `x_ij(u)x_ij(v) = x_ij(w)` whenever `w = u + v`;
    - the two commutator families, whenever the ring equalities hold.
  - Each side condition is decidable by the word problem of `R_L`. The word-problem remark of
    `steinberg-resolvent-shell-envelope-is-finitely-presented`, gate 1, was checked in my report 852826b2e.
  - So this is a recursively enumerable presentation of `St_M(R_L)`, uniform in `M`, and its consequences are
    recursively enumerable. This matters for `M = 3, 4`, where finite presentation of `St_M(R_L)` is not known. ✓
- **The colimit step.**
  - `St(R_L) = colim_M St_M(R_L)` is a directed colimit of groups, and `K_2(R_L) = ker(St → E)` is a subgroup of it.
  - `w` and `{λ_0, N+1}_N` both lie in `K_2(N,R_L)`, and they have the same class in `K_2(R_L)`. So they are the same
    element of `St(R_L)`, and hence equal in some `St_M(R_L)`.
  - The word `{λ, N+1}_M` is the stabilization of `{λ, N+1}_N`, since it uses only indices 1 and 2. So a triple
    `(M, λ_0, d)` exists, and the search halts.
  - Any triple found has `ι[w] = λ`, by injectivity of `ι` and `ι{λ,N+1} = λ`. So the output is unique. ✓
- **The section is a homomorphism.**
  - `C = Q[N+1, A]` is a commutative unital subring of `R_L`, with `A = (N+1)^(−1)`. `λ`, `μ` and `N+1` are units of
    `C`.
  - In `St_N(C)` with `N ≥ 3`, symbols of units are bimultiplicative (Dennis–Stein (S1)). So
    `{λμ, N+1}_N = {λ,N+1}_N{μ,N+1}_N` there, and hence in `St_N(R_L)` by functoriality.
  - Composed with stabilization and `ι`, the map is the identity of `Q^×`. So it is a section, and
    `K_2(N,R_L) = U_N ⋊ Q^×`. ✓

## Other checks
- **Item 1's precondition.** "The image of `w` in `E_N(R_L)` is 1" is decidable by the word problem of `E_N(R_L)`, so
  the search applies exactly to the words in `K_2(N,R_L)`.
- **The words are computable.**
  - `λ = a/b` is the ring word `a·t_2t_1^(b−1)As_1^(b−1)s_2`.
  - `(λ(N+1))^(−1) = A·(b/a)` is an explicit ring word.
  - `h_12` and `w_12` are the standard words. ✓
- **Item 3.** Under (i), a word is trivial exactly when its `E_N`-image is 1 and the search returns 1. Onto-ness of
  `λ ↦ {λ,N+1}_N` follows from (i) and item 4. ✓
- **Item 4, the equivalence.**
  - *(⇒)* A solvable word problem makes nontriviality in `U_N` decidable.
  - *(⇐)* Write `w = u·{ι[w],N+1}_N`. Then `w ≠ 1` if and only if its `E_N`-image is not 1, or `ι[w] ≠ 1`, or
    `u ≠ 1` in `U_N`. Each of these is recursively enumerable, and equality is recursively enumerable.
  - So the word problem is solvable if and only if nontriviality in `U_N` is recursively enumerable. ✓
- **The general-principle remark.** The same search, over `h ∈ H`, `M` and derivations, computes `φ^(−1)` on
  `K_2(N,R)`, using bijectivity of `φ` and the solvable word problem of `H`. ✓

## Nits
- **N1 (item 4).** Membership `w ∈ U_N` is decidable: the `E_N` word problem, then the halting search, gives
  `ι[w] = 1`. Say so, so that "nontriviality in `U_N` is recursively enumerable" is visibly a statement about a
  decidable set of words.
- **N2 (the Colim input).** "The same stable class in `K_2(R_L)`" means the same element of `St(R_L)`, because both
  elements lie in the subgroup `K_2(R_L) ⊆ St(R_L)`. Add this, since the directed-colimit step is applied in
  `St(R_L)`.
