# Reading notes: O_n = Out(G_{n,n-1}) and its Lipschitz part (lane gq-infinite-primes, 2026-09-18)

Sources were read from arXiv e-prints fetched on MSI into `gq/src/on/` (TeX, not PDF):
- BCMNO, arXiv:1701.01474, `wearout-final.tex`;
- Bleak--Cameron--Olukoya (one-sided), arXiv:2004.08478, `AushiftoneDA.tex`;
- Belk--Bleak--Cameron--Olukoya (two-sided), arXiv:2006.01466, `2020_01_07_autshift2.tex`;
- Bleak--Cameron--Olukoya III, arXiv:2407.18720;
- Olukoya, *The core growth of strongly synchronizing transducers*, arXiv:2004.00516;
- Bruce--Li--Takeishi, arXiv:2512.14324;
- Salo, *Wreath products in the automorphism group of a full shift*, arXiv:2305.17946v2, `SecondWreath2.tex`.

Boyle--Lind--Rudolph (Trans. AMS 306, 1988) and Boyle, *Open problems in symbolic dynamics* (2008) were not read.
They are cited through Salo. Line numbers refer to the TeX files.

## 1. The groups

- **O_n and M_n** (2006.01466, §"The groups O_n and L_n", l. 768--817). `M_n` is the monoid of non-initial, minimal,
  strongly synchronizing core transducers over `X_n`. Every state must induce an injective map with clopen image
  (conditions S1, S2), and the product is the core of the minimized transducer product. `SO_n` is a submonoid, and
  `O_n` is "the largest inverse closed subset of `SO_n`". Theorem (from BCMNO): `O_(n,r) ≅ Out(G_(n,r))`, with
  `O_(n,n-1) = O_n`. So `Out(V) = Out(G_(2,1)) ≅ O_2`.
- **L_n** (l. 810--814). `SL_n` is the submonoid of elements satisfying the *Lipschitz constraint* SL3: "for all
  strings `a` and any state `q` such that `π_T(a,q) = q`, `|λ_T(a,q)| = |a|`". Then `L_n := O_n ∩ SL_n`.
- **Periodic orbit representation** (l. 162--170). The action of `M_n` on finite prime cyclic words is a
  monomorphism `Π` into the transformation monoid of prime cyclic words. Its restriction to `SL_n` is the periodic
  orbit representation of `End(X_n^Z, σ_n)/<σ_n>`. Proposition: `Π(T)` is a bijection iff `T in O_n`.

## 2. The shift automorphism group inside O_n

- **Theorem** (2006.01466, abstract and Cor. `cor:mainresult`): `Aut(X_n^Z, σ_n)/<σ_n> ≅ L_n`. It is a central
  extension `<σ_n> -> Aut(X_n^Z, σ_n) -> L_n`, with the centre `<σ_n>` by Ryan's theorem.
- **Splitting** (Thm `Thm:splittingtheorem-Belk`, l. 1366--1376). The sequence splits iff `n` is not a proper power.
  The proof uses the dimension representation `dim : Aut(X_n^Z, σ_n) -> G(n)`, where `G(n)` is generated in
  `Q^x` by the primes dividing `n`, and `dim(σ_n) = n`. For `n = 2`, `G(2) = <2>`. So
  `Aut(X_2^Z, σ_2) = <σ_2> × ker(dim)`, and `L_2 ≅ ker(dim)`, the inert automorphisms.
- **One-sided** (2004.08478, abstract). `Aut(X_n^N, σ_n)` embeds in `Out(G_(n,r))` as `H_n`. Every `H in H_n` is a product
  of at most `|H|` torsion elements. Finitely generated torsion subgroups of `H_n` are finite (l. 1166).
  `Aut(X_2^N, σ_2) ≅ C_2` (Hedlund, reproved there).

## 3. Decidability, torsion and growth

- The order problem is unsolvable in `Out(G_(n,r))`, for every `n > r >= 1` (2006.01466 Thm `thm:orderProblem`,
  from Kari--Ollinger through `Inert_n`; also 2407.18720 l. 1107--1114).
- `Out(G_(n,r))` has trivial centre (2006.01466 abstract).
- **Core growth** (2004.00516). An element of infinite order has logarithmic, polynomial or exponential *core
  growth*, the growth of `|core(A^m)|` in `m`.
  - Conjugation preserves the class.
  - Lemma `coregrowthratepowerinvariant`: if some power `A^m` has growth class `χ`, then so does `A`.
  - Exponential examples exist for every `n >= 2`.
  So the growth class cannot separate an element from its roots. Only a quantitative exponent could, with
  `rate(S^k) = k · rate(S)`, and no lower bound on exponents is known.
- **C*-simplicity** (2512.14324). The groups studied there are C*-simple. That gives no residual finiteness.

## 4. The open problems quoted at source (Salo, 2305.17946v2, l. 148--152)

- "The main 'upper bounds' known on `G` are that groups in it are countable [He69], residually finite
  [BoLiRu88], and ..." Here `G` is the class of groups embedding in the automorphism group of the `Z`-full shift.
- "already abelian groups are a mystery: all finitely-generated abelian groups are embeddable due to closure
  properties of `G`, but we already do not know whether the additive group of dyadic rationals `(Z[1/2], +)` is in
  `G`. Residual finiteness does not prevent this, and in general it is a major open problem whether
  `Aut(Σ^Z)` can have any elements of infinite order with roots of infinitely many orders [Bo08]."

## 5. Consequence recorded as a node

`out-v-contains-the-root-problem-for-the-full-2-shift`.
