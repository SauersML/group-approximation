# Adversarial check of `free-shift-houghton-envelopes-local-stability-proof` (bh-free-48, 2026-09-18)

Target: `free-shift-houghton-like-envelopes-are-not-fp` (bh-map, 6362d6c31). This refutes
`houghton-like-envelopes-lift-finite-presentation-from-germs` with `P = Z`, a free-shift enumeration and `n = 3`.

**Verdict: PASS.** I found no gap in items 1–4. The points I checked, and why they hold:

1. **Strand normal form of the K-letters.** Elements of `K = H_n(E_2)` are, on each quasi-ray, `beta ∘ g ∘ beta^-1`
   with `g ∈ E_2`. `E_2` elements are eventually 2-periodic, and `beta` is a translation on tails. So every K-letter
   is a strand map `m -> m + c` (possibly changing strand) outside a finite set `Φ_a`. The points where a strand map
   with `c < 0` is undefined are inside `Φ_a`, because K-letters are genuine permutations. `E` depends only on the
   K-letters of the word, not on `nu`. This matters: regularity of a `nu'`-trajectory is tested against the same
   `E`.
2. **ρ-letters in strand coordinates.** `rho^(k)_g` is the genuine permutation acting by `lambda_g` on the even
   strand of ray `k` (source convention `rho(g)(2 nu(h)) = 2 nu(gh)`) and trivially elsewhere. So along a regular
   trajectory the composite on strand `j` is exactly the image of the formal word `u_j(w) ∈ P * <ŝ>`.
3. **Triviality in `F`.** `w(nu) = 1` forces the end strand to be `j` and the image of `u_j(w)` in `R_nu` to be
   trivial. Injectivity of `P * <ŝ> -> R_nu` gives `u_j(w) = 1` in `F`. The normal-form reduction in `F` uses only
   `lambda'_g lambda'_h = lambda'_(gh)`, which holds exactly because `lambda'` is a genuine action, and
   `s^a s^b = s^(a+b)` where defined. Along a regular trajectory every intermediate point is in the domain.
4. **Exceptional trajectories.** Each is fixed by `(e, i)` with `e ∈ E` and computed forward and backward. By
   induction along the computation, if `nu'` agrees with `nu` on the finite set `S` of group elements the `nu`-computation
   used, the `nu'`-computation visits the same points. So the exceptional sets coincide.
5. **Item 2.** `nu'` swaps the values at `gh` and `h'`. So `nu'(h) = nu(h)`, and `lambda'_g x = nu'(gh) ≠ nu(gh)`
   for `x = nu(h)`. With `z` on an odd strand, `phi(r)` is a product of two distinct transpositions sharing `z`, a
   3-cycle, so it is not 1. The K-words `t, t'` exist because `FSym(X) ⊆ K`.
6. **Item 3.** It uses only that `phi` is a homomorphism and the item-2 relations for every `x` and every generator,
   so `lambda'_g = lambda_g`, `theta(gh) = g theta(h)` and `theta = R_c`. This is correct.

**Presentation nit (no change to the mathematics).** Item 1's "regular trajectory" should say explicitly that
regularity for `nu'` is tested against the same finite set `E`. It does implicitly.

**What I add** (next node): the constraints that pin `nu` in item 3 can be taken to be finitely many *near relators*
of `R_nu`, read pointwise, plus finite boundary data. So a witness enumeration must be the unique solution of a
finite local constraint problem: `houghton-like-envelope-fp-pins-the-enumeration-by-near-relators`.

**Side remark (a second, cruder counterexample mechanism).** The lifting claim quantifies over arbitrary f.g.
strongly shift-similar `G`. Take `G = <E_2, γ̃>` with `γ̃ = γ` placed on the evens, where `γ` is a Baire-generic
involution of `N`. Generic `γ` satisfy `<[γ], s> ≅ Z/2 * Z` in `NearSym(N)`, by the fresh-trajectory argument. So
`Ĝ ≅ (Z/2 * Z) wr C_2`, which is finitely presented. But a comeagre set contains non-computable `γ`, and
`G ⊇ E_2 ⊇ FSym(N)` has computable words for all transpositions. So `G` recursively presented would make the graph of
`γ̃` r.e. (read it off `γ̃ (p q) γ̃^-1 = (γ̃p γ̃q)`), hence computable. So for such `γ`, `G`, and with it every
`H_n(G)`, is not even recursively presented, although its germ group is finitely presented. The corrected lifting
therefore needs both computability and rigidity. For BH only computable `nu` matter, so bh-map's free-shift kill is
the relevant one. The mechanism is the Sym(N) analog of `shell-recursive-presentations-compute-enumerations` and of
clause 2 of `fp-alt-fin-envelopes-are-unique-solutions-of-their-relators`, with no displacement bound needed here
because transposition words are available. No novelty is claimed. I record this as a remark only, not a node.
