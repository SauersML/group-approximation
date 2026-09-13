# Thompson's F: soficity is the failure of Arzhantseva--Păunescu's relator stability

Lane `ex-thompson-v-soficity`, 2026-09-12. Status: proved on paper, unreviewed.

This note proves the converse of the implication behind the Open problem of Arzhantseva--Păunescu
(arXiv:1410.2626v2, p. 3). They observed that stability in permutations of the two relator words of
Thompson's group `F` would make `F` nonsofic. The converse holds: if `F` is not sofic, the relator
system is stable. So their Open problem, in its "stable" form, is equivalent to the nonsoficity of
`F`. The same proof gives a one-commutator form: `F` is not sofic exactly when every almost-solution
of the two relators almost commutes.

The mechanism is the one already used for Thompson's `V` in
`research/artifacts/thompson-v-soficity-stability-and-full-groups-2026-09-12.md`, Section 2:
fixed-point characters of almost-actions are rigid by Dudko--Medynets. `F` has the abelianization
`Z^2`, so the rigid part is regular on `F'` plus scalar characters of `Z^2`. `Z^2` is itself stable in
permutations (Arzhantseva--Păunescu, Main Theorem), and that is what corrects the scalar part.

## 0. Definitions and sources (all read from the PDFs)

- **Presentation.** `F = <a, b | [a b^-1, a^-1 b a], [a b^-1, a^-2 b a^2]>`. Arzhantseva--Păunescu p. 3:
  "This system is the relator words of a finite presentation of the famous Thompson's group F".
- **Hamming distance.** For `p, q in Sym(n)`, `d(p,q) = (1/n) #{i : p(i) != q(i)}` (their Definition 2.1).
  It is bi-invariant.
- **Stability** (their Definition 3.2, verbatim in substance). Permutations `p_1, ..., p_m` are a
  *solution* of a finite set `R` of words if `xi(p_1, ..., p_m) = id` for all `xi in R`, and a
  *`delta`-solution* if `d(xi(p_1, ..., p_m), id) < delta` for all `xi in R`. "The system R is called
  stable (or stable in permutations) if for all epsilon > 0 there exists delta > 0 such that for all n
  and all p_1, ..., p_m in Sym(n) a delta-solution of R, there exist p~_1, ..., p~_m in Sym(n) a solution
  of R such that d_H(p_i, p~_i) < epsilon." A group is stable if the relator set of one (equivalently,
  every) finite presentation is.
- **Open problem** (p. 3, verbatim). "Is the system of two words [ab^-1, a^-1ba] and [ab^-1, a^-2ba^2]
  (weakly) stable in permutations?" They add that an affirmative answer, with their Theorems 1.1
  and 4.3, "will imply that F is not amenable and even not sofic".
- **Main Theorem** (p. 2, verbatim). "For any given k >= 2 and with respect to the normalized Hamming
  distance, every k (even) permutations that almost commute are near k commuting (respectively, even)
  permutations." For `k = 2` this is stability of the one-relator system `{[a,b]}`.
- **Characters of F.** Dudko--Medynets, *Finite factor representations of Higman--Thompson groups*,
  arXiv:1212.1230, p. 10: "the abelianization of F_(n,r) is isomorphic to Z^n". Corollary 3.3(2), p. 11,
  verbatim: "If chi is an indecomposable character of F_(n,r), then chi is either regular or
  chi(g) = rho([g]), where [g] is the image of g in the abelianization of F_(n,r) and rho : Z^n -> T is a
  group homomorphism." Thompson's `F` is `F_(2,1)`.

**Terms used below.**
- A *character* of a countable group is a positive definite class function `chi` with `chi(e) = 1`. The
  characters form a Choquet simplex whose extreme points are the indecomposable characters.
- An *almost-homomorphism* is a sequence of maps `phi_n : F -> Sym(k_n)` with
  `d(phi_n(gh), phi_n(g) phi_n(h)) -> 0` for all `g, h`. It is *separating* if `d(phi_n(g), id) -> 1` for
  all `g != e`. `F` is sofic iff it has a separating almost-homomorphism.
- Throughout, `ab : F -> Z^2` is the abelianization with `ab(a) = e_1`, `ab(b) = e_2`, and `F' = ker ab`.

## 1. Two elementary facts about F

**Fact 1.1 (finite quotients are abelian).** Every homomorphism from `F` to a finite group kills `F'`.
*Proof.* `F'` is infinite and simple. Dudko--Medynets, p. 10: "Observe that the commutator subgroup of
F_(n,r) is a simple group". The kernel meets `F'` in a normal subgroup of `F'`, so in `1` or in `F'`. It
cannot be `1`, because `F'` does not embed in a finite group. ∎

So the solutions of the relator system in `Sym(n)` are exactly the commuting pairs. A commuting pair
satisfies both relators, which are commutators of words. Conversely a solution defines a homomorphism
`F -> Sym(n)`, whose image is abelian by Fact 1.1.

**Fact 1.2 (almost-homomorphisms from almost-solutions).** Fix a word `w_g` in `a, b` for each `g in F`.
If `(A_n, B_n)` are `delta_n`-solutions with `delta_n -> 0`, then `phi_n(g) = w_g(A_n, B_n)` is an
almost-homomorphism. Indeed `w_g w_h w_(gh)^-1` is a product of `N(g,h)` conjugates of relators and their
inverses in the free group, so by bi-invariance `d(phi_n(g) phi_n(h), phi_n(gh)) <= N(g,h) delta_n`.
Conversely an almost-homomorphism evaluated on `a, b` gives `delta_n`-solutions with `delta_n -> 0`.

## 2. The fixed-point character

**Lemma 2.1.** Let `phi_n` be an almost-homomorphism of `F` and `omega` a nonprincipal ultrafilter. Then
`chi(g) = lim_omega |Fix(phi_n(g))| / k_n` is a character of `F`, and it has the form

```text
chi = t tau_reg + (1 - t) chi_ab,    t in [0,1],
```

where `chi_ab` is a character that factors through `ab`. In particular `chi(g) = 1 - t` for every
`g in F' \ {e}`.

*Proof.* The three verifications are word for word those of the V artifact, Section 2, (a)--(c).
- **`chi(e) = 1`.** `phi_n(e)^2` is close to `phi_n(e)`, so `phi_n(e)` is close to `id`.
- **Class function.** `phi_n(h g h^-1)` is close to `phi_n(h) phi_n(g) phi_n(h)^-1`, which has as many
  fixed points as `phi_n(g)`.
- **Positive definite.** For permutations `sigma_i` and `c in C^r`,
  `sum_(i,j) c_i conj(c_j) |Fix(sigma_j^-1 sigma_i)| = sum_(x,y) |sum_i c_i [sigma_i x = y]|^2 >= 0`,
  and `|Fix(phi_n(g_j^-1 g_i))|` differs from `|Fix(sigma_j^-1 sigma_i)|` by `o(k_n)`.

By Choquet's theorem `chi` is a barycenter of indecomposable characters, and by Dudko--Medynets
Corollary 3.3(2) these are `tau_reg` and the `rho o ab`. Let `t` be the weight of `tau_reg`. Then
`chi_ab` is the normalized barycenter of the remaining part, or any character through `ab` if `t = 1`.
For `g in F' \ {e}`, `tau_reg(g) = 0` and `rho(ab(g)) = 1`. ∎

**Lemma 2.2 (amplification).** If some almost-homomorphism of `F` has `t > 0` along some ultrafilter,
then `F` is sofic.

*Proof.* Fix `m >= 1` and `N >= 1`. On `[k_n]^m × (Z/N)^2` let `F` act by
`Psi(g) = phi_n(g)^(× m) × tau_N(ab(g))`, where the first factor acts coordinatewise and `tau_N` is
translation on `(Z/N)^2`.
- **Defect.** `tau_N o ab` is a homomorphism, and the coordinatewise action has defect at most `m` times
  that of `phi_n`, by a union bound. So `Psi` is an almost-homomorphism in `n`.
- **Elements outside `F'`.** For `g not in F'`, `ab(g) != 0`, and once `N` exceeds the entries of `ab(g)`
  the translation `tau_N(ab(g))` has no fixed point. Then `Psi(g)` has no fixed point either.
- **Elements of `F' \ {e}`.** The fixed-point proportion of `Psi(g)` is that of `phi_n(g)^(× m)`, which
  tends to `(1-t)^m` along `omega`.

Given a finite `E ⊆ F` and `epsilon > 0`, choose `m` with `(1-t)^m < epsilon/2` and `N` beyond the
entries of `ab(E)`. Then choose `n` in an `omega`-large set on which the defect on `E` is below
`epsilon` and every `g in E \ {e}` moves more than a `1 - epsilon` proportion. This is a sofic
approximation on `E`, so `F` is sofic. ∎

## 3. The theorem

**Theorem 3.1.** For Thompson's group `F` the following are equivalent.
1. `F` is not sofic.
2. The relator system `{[ab^-1, a^-1ba], [ab^-1, a^-2ba^2]}` is stable in permutations (Definition 3.2),
   i.e. `F` is stable.
3. **One-commutator form.** For every `epsilon > 0` there is `delta > 0` such that for all `n` and every
   `delta`-solution `(A, B)` of the relator system in `Sym(n)`, `d(AB, BA) < epsilon`.
4. For every almost-homomorphism of `F` and every ultrafilter, `t = 0` in Lemma 2.1.

*Proof.*
- **`1 => 4`.** Lemma 2.2.
- **`4 => 3`.** Suppose (3) fails. Then there are `epsilon > 0` and `delta_n`-solutions `(A_n, B_n)` with
  `delta_n -> 0` and `d(A_n B_n, B_n A_n) >= epsilon`. By Fact 1.2 they define an almost-homomorphism
  with `phi_n([a,b]) = [A_n, B_n]`, and by bi-invariance `d([A_n,B_n], id) = d(A_n B_n, B_n A_n)`. So
  `chi([a,b]) <= 1 - epsilon` along every ultrafilter. Since `[a,b] in F' \ {e}`, Lemma 2.1 gives
  `1 - t <= 1 - epsilon`, so `t >= epsilon > 0`, and (4) fails.
- **`3 => 2`.** Given `epsilon`, apply the Main Theorem for `k = 2`: some `eta > 0` is such that every
  pair with `d(AB, BA) < eta` is within `epsilon` of a commuting pair. Choose `delta` for `eta` by (3).
  A `delta`-solution then almost commutes, hence lies within `epsilon` of a commuting pair, which is a
  solution by Fact 1.1.
- **`2 => 1`.** Suppose `F` is sofic and stable. Take a separating almost-homomorphism and its
  `delta_n`-solutions `(A_n, B_n) = (phi_n(a), phi_n(b))`. Stability gives solutions `(A~_n, B~_n)` with
  `d(A_n, A~_n), d(B_n, B~_n) -> 0`. Solutions commute (Fact 1.1), so by bi-invariance
  `d([A_n, B_n], id) -> 0`. But `phi_n([a,b])` is close to `[A_n, B_n]` and, by separation, far from
  `id`. Contradiction. ∎

**Corollary 3.2.** The "stable" form of Arzhantseva--Păunescu's Open problem has an affirmative answer
exactly when Thompson's group `F` is not sofic. Soficity passes to subgroups and `F <= V`, so an
affirmative answer also makes Thompson's `V` nonsofic.

## 4. Reading

- **What changed.** Arzhantseva--Păunescu posed the Open problem as a sufficient condition. By
  Theorem 3.1 it is necessary as well, so any proof that `F` is not sofic proves their stability
  statement, and any construction on the positive side must make the two relators nearly hold while
  `A` and `B` stay far from commuting.
- **A target a computer can look at.** Statement 3 involves two permutations and three words: the
  relators, of lengths 10 and 14, and the commutator. A family of `delta`-solutions with `d(AB, BA)` bounded below makes
  `F` sofic. Exact solutions all commute (Fact 1.1), so such a family must use the error essentially.
- **Where the mechanism stops.** Nothing here decides soficity. `F` has the Haagerup property (it
  lies in `V`, which has it), so the Kazhdan compression mechanism has no instance inside `F`
  (`a-t-menable-groups-have-no-rigid-compression-defect`). Fournier-Facio--Rangarajan
  (arXiv:2301.03970) prove uniform stability of `F` for submultiplicative norms. That is uniform, not
  pointwise, and they themselves distinguish it from this question.
- **Scope of the argument.** Only two inputs are specific to `F`: the character classification and
  stability of the abelianization `Z^2`. By Dudko--Medynets Corollary 3.3(2) and the `k`-tuple Main
  Theorem, the same proof should apply to every `F_(n,r)`, with abelianization `Z^n`. That variant is
  not written out here.
