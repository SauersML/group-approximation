# Invariant measure versus finite models beyond free groups (part 1 of 2)

Lane `un-rf-beyond-free` (UN swarm), 2026-09-13. Written proofs, UNREVIEWED. Part 2 is the Toeplitz
construction over residually finite groups, credit, and open classes.

## 0. Question and answer

The UN flagship (`free-group-cantor-elementary-group-lef-iff-invariant-measure`) rests on one dynamical
input: for free groups, an invariant probability measure gives residually finite (RF) finite models
(Kerr–Nowak Theorem 5.2, via Ma). Which acting groups have that property?

**Answer (this part).** Call `Γ ∈ 𝔑` if every continuous `Γ`-action on a Cantor space with an invariant
Borel probability measure of full support is RF.
- `𝔑` is closed under subgroups and finite-index overgroups (Props I and R).
- Every virtually free group is in `𝔑` (Theorem V).
- `Z^2 ∉ 𝔑`, with a minimal free witness, so no group containing `Z^2` is in `𝔑` (Theorem Z).
- For virtually free acting groups the ring-level flagship equivalence extends verbatim (Corollary V).

**Conventions.** `Γ` countable; `α : Γ ↷ X` continuous; `X` compact metrizable, perfect, compatible metric
`d`. Shift: `(g·x)(h) = x(g^(-1)h)` on `A^Γ`.

**Definition (Kerr–Nowak, as restated by Ma, arXiv:2209.00580, `defn: residually finite action`, read from
the TeX source on MSI).** "A continuous action of $G$ on a perfect compact metrizable space $X$, equipped
with a compatible metric $d$, is said to be *residually finite* if for any finite $F\subset G$ and
$\epsilon>0$, there is a finite set $E\subset X$, equipped with a $G$-action $\beta$ such that $E$ is
$\epsilon$-dense in $X$ and $d(\alpha(s)(z), \beta(s)(z))<\epsilon$ for all $z\in E$ and $s\in F$."

## 1. Three elementary lemmas

**Lemma 1 (maps suffice).** Suppose that for every finite `F ⊆ Γ` and `ε > 0` there are a finite `Γ`-set `E`
and a map `ζ : E -> X` with `ζ(E)` `ε`-dense and `d(α(s)ζ(z), ζ(sz)) < ε` for all `z ∈ E`, `s ∈ F`. Then `α`
is RF.

*Proof.* Given `F, ε`, pick `η <= ε/3` with `d(x,x') < η ⇒ d(α(s)x, α(s)x') < ε/3` for `s ∈ F`, and a model
`(E, ζ)` for `(F, η)`. Since `X` is perfect, choose pairwise distinct `x_z ∈ X` with `d(x_z, ζ(z)) < η`, put
`E' = {x_z}` and `β(s)x_z = x_(sz)`. Then `d(α(s)x_z, β(s)x_z) <= ε/3 + η + η <= ε`, and `E'` is `2η`-dense. ∎
(This is the transport step of `extensions-of-aperiodic-sfts-not-rf-proof`, with non-injective `ζ`.)

**Lemma 2 (generators suffice).** Let `S ⊆ Γ` be finite and symmetric, and `F ⊆ ⟨S⟩` finite. For every
`ε > 0` there is `δ > 0` such that every model that is `δ`-close on `S` is `ε`-close on `F`.

*Proof.* Induction on word length, using `d(ζ(sw z), sw ζ(z)) <= d(ζ(s(wz)), sζ(wz)) + d(sζ(wz), s wζ(z))`
and uniform continuity of the finitely many `α(s)`, `s ∈ S`. ∎

**Lemma 3 (RF gives an invariant measure).** If `α` is RF, then `X` carries an `α`-invariant Borel
probability measure.

*Proof.* Take `F_n ↑ Γ`, `ε_n -> 0` and models `(E_n, β_n)`; let `ν_n` be uniform on `E_n`. For `f ∈ C(X)`
and `s ∈ F_n`: `|∫ f∘α(s) dν_n − ∫ f dν_n| = |avg_z f(α(s)z) − avg_z f(β_n(s)z)| <= ω_f(ε_n)`, because
`β_n(s)` permutes `E_n`. Any weak* limit point is invariant. ∎

## 2. RF subshifts are exactly those with periodic window models

For a subshift `X ⊆ A^Γ` and finite `W ⊆ Γ` let `L_W(X) = {x|_W : x ∈ X}` and
`X_W = {c ∈ A^Γ : (g^(-1)·c)|_W ∈ L_W(X) for all g}`, the window SFT of `X`.

**Proposition S.** Let `X ⊆ A^Γ` be a perfect subshift. Then `X` is RF iff for every finite `W ⊆ Γ` there is
a finite invariant set `O ⊆ X_W` (a finite union of finite orbits) with `{c|_W : c ∈ O} = L_W(X)`.

Fix finite `B_1 ⊆ B_2 ⊆ …` exhausting `Γ` with `e ∈ B_1`, and use
`d(x,x') = 2^(-max{j : x|_(B_j) = x'|_(B_j)})`.

*Proof of ⇐.* Given `F, ε`, choose `j` with `2^(-j) < ε`, put `B = B_j` and `W = B ∪ F^(-1)B`, and take `O`.
For `c ∈ O` choose `ζ(c) ∈ X` with `ζ(c)|_W = c|_W`. For `s ∈ F`, `b ∈ B`:
`(s·ζ(c))(b) = c(s^(-1)b) = (s·c)(b) = ζ(s·c)(b)`, since `s^(-1)b ∈ W` and `b ∈ W`. So `s·ζ(c)` and
`ζ(s·c)` agree on `B`. Density: for `x ∈ X` take `c ∈ O` with `c|_W = x|_W`. Lemma 1 applies. ∎

*Proof of ⇒.* Given `W`, choose `j` with `W ⊆ B_j`, `ε = 2^(-j)`, `F = W^(-1)`, and a model `(E, β)`. Put
`c_z(λ) = (β(λ^(-1))z)(e)`. Then `c_(β(g)z) = g·c_z`, so `O = {c_z : z ∈ E}` is finite and invariant.
Closeness for `s = w^(-1)` gives `c_z(w) = (α(w^(-1))z)(e) = z(w)`, so `c_z|_W = z|_W ∈ L_W(X)`. Applying
this to `β(g^(-1))z` gives `O ⊆ X_W`. Density covers `L_W(X)`. ∎

The ⇒ half is the pseudo-orbit argument of `sfts-without-finite-orbits-are-not-residually-finite-actions`.

**Caution.** Ma's TeX source contains a commented-out proposition asserting that every subshift of `2^Γ` over
a residually finite group is RF. Proposition S with Labbé's shift (§4) shows why it was withdrawn.

## 3. The class 𝔑

**Definition.** `Γ ∈ 𝔑` iff every continuous `Γ`-action on a Cantor space admitting an invariant Borel
probability measure of full support is RF.

**Lemma F (free groups).** `F_r ∈ 𝔑` for every `r ∈ N ∪ {∞}`.

*Proof.* Let `(a_i)` be a free basis. Given `F` and `ε`, words in `a_1,…,a_m` of length `<= L` cover `F`.
By Lemma 2 it is enough to be `δ`-close on `a_i^(±1)`, `i <= m`.
- Pick a clopen partition `𝒬` of mesh `< δ'`, and its common refinement `𝒫` with the partitions
  `a_i^(-1)𝒬`. Here `δ'` is also small enough that `a_i^(-1)` moves `δ'`-close points `δ`-close.
- Put `w(P) = μ(P) > 0` (full support), and `w_i(P,P') = μ(P ∩ a_i^(-1)P')`. By invariance
  `Σ_(P') w_i(P,P') = w(P)` and `Σ_P w_i(P,P') = w(P')`.
- The vector `w` lies in the rational polyhedral cone cut out by these equations and nonnegativity. Rational
  points are dense in the rational subspace `V_S` of vectors supported on `supp w` satisfying the equations,
  and `w` is strictly positive on `supp w`. So there is a rational point of `V_S` with the same support; scale
  it to integers `n(P) >= 1` and `n_i(P,P') >= 0`, with `n_i(P,P') > 0 ⇒ P ∩ a_i^(-1)P' ≠ ∅`, and with row
  and column sums `n(P)`.
- Let `E = ⊔_P E_P`, `|E_P| = n(P)`. For each `i`, choose a bijection `β(a_i)` of `E` sending exactly
  `n_i(P,P')` points of `E_P` into `E_(P')`; the row and column sums make this possible. Freeness makes `β`
  a `Γ`-action; generators `a_j`, `j > m`, act trivially.
- `ζ(z) ∈ P` for `z ∈ E_P`. If `z ∈ E_P` and `β(a_i)z ∈ E_(P')`, then `P ⊆ a_i^(-1)Q` for one `Q ∈ 𝒬`, so
  `a_iP ⊆ Q`, and `P'` meets `a_iP`, so `P' ⊆ Q`. Hence `ζ(a_i z), a_i ζ(z) ∈ Q` and are `δ'`-close. The
  inverses follow by uniform continuity. `ζ(E)` meets every atom, so it is `δ'`-dense.
Lemma 1 finishes. Minimality is not used. ∎

**Proposition I (finite-index overgroups).** Let `H <= Γ` have finite index and `α : Γ ↷ X` (perfect). If
`α|_H` is RF, so is `α`.

*Proof.* Fix a transversal `T ∋ e` with `Γ = ⊔_(t∈T) tH`. For `γ ∈ F` and `t ∈ T` write `γt = t'h`, and let
`F_H` be the finite set of `h` so obtained. Choose `δ` with `d(x,x') < δ ⇒ d(tx, tx') < ε/2` for `t ∈ T`, and an
RF model `(E_H, β_H)` of `α|_H` for `(F_H, δ)`. Let `Γ` act on `T × E_H` by `γ(t,z) = (t', β_H(h)z)` (the
induced action), and put `ζ(t,z) = α(t)z`. Then `ζ(γ(t,z)) = t'β_H(h)z` and `α(γ)ζ(t,z) = t'hz` are
`ε/2`-close, and `ζ(E) ⊇ E_H` is dense. Lemma 1 finishes. ∎

**Proposition R (subgroups).** (a) RF passes to restrictions `α|_H`. (b) If `Γ ∈ 𝔑` and `H <= Γ`, then
`H ∈ 𝔑`.

*Proof.* (a) Restrict `β`. (b) Let `H ↷ Y` be Cantor with invariant `μ` of full support.
- Co-induce: `X = {f : Γ -> Y : f(γh) = h^(-1)f(γ)}` with `(γ'f)(γ) = f(γ'^(-1)γ)`. A transversal identifies
  `X ≅ Y^(Γ/H)`, a Cantor space, and the product measure `μ^⊗` is `Γ`-invariant (coordinates are permuted and
  twisted by elements of `H`, which preserve `μ`) with full support.
- So `Γ ↷ X` is RF, hence `H ↷ X` is RF by (a).
- `p(f) = f(e)` is an `H`-equivariant factor map `X -> Y`, since `(hf)(e) = f(h^(-1)) = h f(e)`.
- RF passes to factors onto perfect spaces (`extensions-of-aperiodic-sfts-are-not-residually-finite-actions`,
  item 1). ∎

**Theorem V.** Every virtually free group is in `𝔑`. So is every group commensurable with a subgroup of a
group in `𝔑`.

*Proof.* A virtually free countable `Γ` has a finite-index free subgroup `F_r`, `r <= ∞`. An invariant measure
of full support for `Γ` is one for `F_r`. So `α|_(F_r)` is RF (Lemma F), hence `α` is RF (Proposition I). ∎

## 4. Z^2 and every group containing it are not in 𝔑

**Theorem Z.**
1. `Z^2 ∉ 𝔑`. Labbé's Wang shift `Ω_U` is a minimal free Cantor `Z^2`-system with an invariant measure of full
   support that is not RF.
2. No group containing `Z^2` is in `𝔑`.
3. For `Γ = Z^2 × Λ`, `Λ` countable, there is a **minimal free** Cantor `Γ`-system with an invariant
   probability measure that is not RF.

*Proof.*
1. `Ω_U` is minimal, aperiodic and an SFT (`minimal-aperiodic-wang-shift-exists`), so it is infinite, perfect,
   and a Cantor space. `Z^2` is amenable, so there is an invariant measure, of full support by minimality.
   Aperiodicity means no finite orbit, so `Ω_U` is not RF
   (`sfts-without-finite-orbits-are-not-residually-finite-actions`).
2. Proposition R(b).
3. For infinite `Λ`, take a free minimal `Λ ↷ C` with invariant `ν` (`elek-free-minimal-invariant-measure-actions-citation`,
   Elek Thm 1); for finite `Λ`, take `C = Λ`. The product action on `Ω_U × C` is minimal, free, and preserves
   `μ × ν`. If it were RF, the restriction to `Z^2 × {e}` (Proposition R(a)) and the factor onto `Ω_U` would be
   RF, contradicting 1. ∎

So for `Z^2`-containing groups "invariant measure" and "genuine finite models" separate. The ring-level
counterpart is the quantum-tiling question (`matricial-z2-sft-crossed-products-give-quantum-tilings`; lane
`un-labbe-ring`), which this lane does not touch.

## 5. The flagship equivalence over virtually free acting groups

**Corollary V.** Let `Γ` be virtually free, acting minimally and topologically freely on the Cantor set `X`,
let `k` be a field, and `R = LC(X,k) ⋊ Γ`. The following are equivalent:
- (i) `X` carries a `Γ`-invariant Borel probability measure;
- (ii) the action is RF;
- (iii) `R` embeds unitally and injectively in some `∏_ω M_(N_n)(k)`;
- (iv) `R` has a unital ring homomorphism into some `∏_ω M_(N_n)(k)`.

*Proof.* (i)⇒(ii): Theorem V (minimality gives full support). (ii)⇒(iii):
`residually-finite-actions-give-matricial-crossed-products`. (iii)⇒(iv) is trivial. (iv)⇒(i):
`matricial-steinberg-algebras-have-invariant-measures`. ∎

With `k = F_q`, R finitely generated, and `N >= 3`, this puts every virtually free acting group into the
flagship dichotomy:
- **(i):** `EL_N(R)/Z` is LEF;
- **no invariant measure:** it has no nontrivial MF quotient from rank `2n`
  (`no-invariant-measure-steinberg-elementary-no-mf-quotient`).

In both cases it is infinite, simple and Kazhdan (`steinberg-elementary-groups-are-simple-mod-centre`).
