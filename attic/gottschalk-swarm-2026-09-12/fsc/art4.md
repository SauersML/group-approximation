
## 4. Linear shadow: permutation modules and Hecke algebras

`K` is a field and `n >= 1`. A *linear automaton* on `(K^n)^(G/H)` is an equivariant linear map with finite
memory.

**Lemma 6 (duality).**
- `(K^n)^(G/H)` is the algebraic dual of the permutation module `K[G/H]^n`, with `(g . y)(v) = y(g^(-1) v)`.
- Linear automata `T` are exactly the transposes `f^*` of `K[G]`-module endomorphisms `f` of `K[G/H]^n`,
  with `(f^* y)(v) = y(f v)` on basis vectors `v`.
- `T` is injective iff `f` is surjective, and surjective iff `f` is injective.

*Proof.*
- `f` is determined by the vectors `w_i = f(H e_i)`, which are finitely supported and `H`-fixed. Then
  `(f^* y)(gH e_i) = y(g w_i)` reads `y` on the finite set `g . supp w_i`.
- Conversely, if `T` has finite memory, then `(Ty)(H e_i) = y(w_i)` for some finitely supported `w_i`.
  Equivariance under `H`, which fixes the site `H`, makes `w_i` `H`-fixed. So `f(gH e_i) = g w_i` is well
  defined, and `f^* = T`.
- For linear maps between vector spaces, `ker f^*` is the annihilator of `im f`, and `im f^*` is the
  annihilator of `ker f`. QED

For `H = 1` this is the standard equivalence between linear surjunctivity and stable finiteness of `K[G]`
(Ceccherini-Silberstein–Coornaert; cited, not re-read). In general, linear surjunctivity of every
`(K^n)^(G/H)` means: every surjective `K[G]`-endomorphism of every `K[G/H]^n` is injective.

**Proposition 7 (coprime characteristic).** If `char K` does not divide `|H|` and `K[G]` is stably finite,
then every surjective `K[G]`-endomorphism of `K[G/H]^n` is injective.

*Proof.*
1. `e = |H|^(-1) sum_h h` is idempotent, and `ge -> gH` gives `K[G]e ≅ K[G/H]`: `ghe = ge`, and the `ge`
   for distinct cosets have disjoint supports.
2. So `M = K[G/H]^n` is projective, with `M ⊕ Q ≅ K[G]^n` for `Q = (K[G](1 - e))^n`.
3. A surjection `f : M -> M` splits, so `M ≅ M ⊕ ker f` and `K[G]^n ≅ K[G]^n ⊕ ker f`.
4. Projecting gives a split surjection `psi : K[G]^n -> K[G]^n` with kernel `≅ ker f` and a section `s`, so
   `psi s = 1` in `M_n(K[G])`.
5. Stable finiteness gives `s psi = 1`, so `psi` is injective and `ker f = 0`. QED

This is the linear counterpart of Theorem 1, for self-maps of the coset shift. Part 3 of
`linear-invariant-output-automata-fail-augmentation` treats linear automata from the full shift into `Y`,
where the coprime case is a corner compression. The two meet through `End_(K[G])(K[G]e) ≅ (eK[G]e)^op`.

**The endomorphism ring.**
- An endomorphism `f` of `M = K[G/H]` is determined by `f(H)`, which lies in `M^H`.
- `M^H` has as basis the orbit sums `<HgH> = sum_(x in HgH/H) x`.
- Composition has integer structure constants reduced into `K`.
- So `End_(K[G])(M)` is, up to the opposite ring, the Hecke algebra of `(G, H)` over `K`. For `char K`
  not dividing `|H|` it is the corner `eK[G]e` of Proposition 7.

**Lemma 8 (non-projective at a shared prime).** If `char K = p` divides `|H|`, then `K[G/H]` is not a
projective `K[G]`-module.

*Proof.*
- `K[G]` is free over `K[H]`, so restriction to `H` preserves projectivity.
- `H` fixes the point `H` of `G/H`. So the trivial module `K . H` is a direct summand of the restriction,
  one `H`-orbit of the permutation basis.
- The trivial module is not projective over `K[H]`. Otherwise the augmentation `K[H] -> K` would split,
  giving an `H`-fixed vector of augmentation `1`. But the `H`-fixed vectors of `K[H]` are the multiples of
  `sum_h h`, whose augmentation is `|H| = 0` in `K`. QED

This is the augmentation argument of part 2 of `linear-invariant-output-automata-fail-augmentation`, in
module form. Steps 2 to 3 of Proposition 7 are unavailable at a shared prime.

**Question 9 (linear shadow of the open case).** Let `char K = p` divide `|H|`, and let `K[G]` be stably
finite. Is every surjective `K[G]`-endomorphism of `K[G/H]^n` injective?
- *Reduction.* Theorem 4 runs over `K`, with `c = [H : S]^(-1)` in `K`, and gives a linear `Phi` when `tau`
  is linear. So Question 9 at `H` follows from Question 9 at a Sylow `p`-subgroup of `H`.
- *Relation to the node.* For finite `K`, the node's claim at sizes `|K|^n`, applied to linear maps, answers
  Question 9 positively. That uses surjunctivity of `G` at every size `|K|^n`, which is a priori stronger
  than stable finiteness of `K[G]`. The two agree if `stable-finiteness-forces-prime-power-surjunctivity`
  (OPEN) holds.
- *Amenable `G`, finite `K`.* Positive, by Lemma 6 and the amenable remark of Section 2.
- *Normal Sylow subgroup.* Positive when the Sylow `p`-subgroup of `H` is normal in `G`, by the reduction and
  Proposition 10.

**Proposition 10 (normal `p`-subgroups).** Let `H` be a finite normal `p`-subgroup of `G`, `char K = p`, and
`K[G]` stably finite. Then every surjective `K[G]`-endomorphism of `K[G/H]^n` is injective.

*Proof.* `K[G/H]` is the group algebra of `Q = G/H`, and `K[G]` acts through `K[Q]`. So the endomorphisms
are right multiplications by matrices in `M_n(K[Q])`. A surjective one has a section, because the module is
free, and so gives a one-sided inverse pair in `M_n(K[Q])`. `K[Q]` is stably finite by
`finite-normal-p-subgroups-preserve-modular-stable-finiteness` (ESTABLISHED). So the pair is two-sided, and
the endomorphism is injective. QED

For normal `H` the coset shift is the full shift over `G/H`. So the node's claim at a normal `H` is a
per-size form of the quotient direction of `finite-normal-subgroups-do-not-affect-surjunctivity`:
surjunctivity at size `m` passes from `G` to `G/H`.
- Theorem 1 proves that direction when `gcd(m, |H|) = 1`, with no separation hypothesis. So it covers normal
  subgroups inside the finite residual.
- Proposition 10 is the linear shadow at a shared prime.

**Where the argument stops for non-normal `H`** (`n = 1`).
- Write `f(H) = xH` with `x in K[G]`. Right multiplication by `x` on `K[G]` lifts `f`.
- Surjectivity of `f` gives `z` with `zx in 1 + K[G] I_H`, where `I_H` is the augmentation ideal of `K[H]`.
- `K[G] I_H` is only a left ideal and need not be nilpotent. Take `G = <a> * <b>` with `a, b` of order 2,
  `H = <a>` and `p = 2`. The product `(1 + a) . b(1 + a) . ... . b(1 + a)` of `k + 1` elements of
  `K[G] I_H` contains the reduced word `(ab)^k a` with coefficient `1`, so it is nonzero.
- So `zx` need not be a unit, and stable finiteness does not apply. (This `G` is amenable, so Question 9
  holds there. The example only shows that this proof does not run.) Not pursued further.
