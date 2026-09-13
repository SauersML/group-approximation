# Matricial crossed products: residually finite actions, invariant measures, and where towers stop

Lane `un-measure` (UN swarm, target U2), 2026-09-13. Part 1 of 2. Written proofs, UNREVIEWED.
Prior-art input from `un-prior-art` (bounded; see §7).

## 0. Summary

Throughout, `Γ` is a countable group acting on a Cantor space `X` by `α`, `k` is a field, and
`R = LC(X,k) ⋊ Γ` is the algebraic crossed product: finite sums `Σ_g f_g u_g`, `f_g` locally
constant, `u_g f u_g^(-1) = f ∘ α(g)^(-1)`. It is the Steinberg algebra of the transformation
groupoid `X ⋊ Γ`. "Matricial" means: there is a unital ring homomorphism
`Ψ : R -> ∏_ω M_(N_n)(k)` into an algebraic ultraproduct (non-principal ultrafilter `ω`).

- **Lemma S (simple rings).** For a simple unital ring, a sequence of unital maps into matrix
  rings that are exactly additive and multiplicative on an exhausting sequence of finite windows
  gives an *injective* matricial embedding. No faithfulness has to be arranged.
- **Theorem A (towers).** If `α` is minimal, topologically free and residually finite in the sense
  of Kerr–Nowak, then `R` embeds unitally and injectively in `∏_ω M_(N_n)(k)`. For finite `k`,
  every finitely generated subgroup of every `GL_m(R)` is LEF.
- **Proposition B (measure).** Any unital homomorphism of the Steinberg algebra of a Hausdorff
  ample groupoid with compact unit space into `∏_ω M_(N_n)(k)` produces a groupoid-invariant
  Borel probability measure on the unit space. So matricial rings are never paradoxical at `[1]`.
- **Theorem C (free groups: a Tarski dichotomy at ring level).** For a minimal topologically free
  action of `F_r` (`r ∈ N ∪ {∞}`) on the Cantor set, these are equivalent: an invariant probability
  measure exists; the action is residually finite; `R` is matricial; `R` has a unital Sylvester
  matrix rank function. The step from measure to residual finiteness is Kerr–Nowak Theorem 5.2,
  quoted here from Ma's restatement.
- **Proposition D (the boundary at `Z^2`).** For a free minimal `Z^2`-SFT, an invariant measure
  exists and the action is not residually finite, so Theorem A does not apply. Here `R` is
  matricial only through noncommuting periodic quantum tilings at every scale. If the SFT is
  quantum rigid, `R` is not matricial at all.

The single mechanism is **exact finite dynamics**. Genuine finite `Γ`-sets that approximately
follow `α` are exact ring models of `R`. Invariant measure is the necessary shadow of any
matricial model. The acting group decides whether the shadow can be lifted: free groups have no
relations to obstruct the lift, while `Z^2` carries commutation relations that aperiodic SFTs
cannot satisfy classically.

## 1. Lemma S

**Lemma S.** Let `R` be a simple unital ring, `W_1 ⊆ W_2 ⊆ ...` finite subsets with `∪ W_n = R`,
and `ψ_n : R -> M_(N_n)(k)` maps (`N_n >= 1`) such that `ψ_n(1) = 1` and
`ψ_n(a + b) = ψ_n(a) + ψ_n(b)`, `ψ_n(ab) = ψ_n(a) ψ_n(b)` whenever `a, b ∈ W_n`. Then
`Ψ(r) = [ψ_n(r)]_ω` is an injective unital ring homomorphism `R -> ∏_ω M_(N_n)(k)`.

*Proof.* For `a, b ∈ R`, both lie in `W_n` for all large `n`, and cofinite sets belong to `ω`. So
`Ψ` is additive, multiplicative and unital. Its kernel is a two-sided ideal, and it is proper,
since `Ψ(1) = [1]` and the ultraproduct is nonzero because every `N_n >= 1`. By simplicity the
kernel is zero. ∎

*Model test.* `R = k × k` (not simple) with `ψ_n(a,b) = a`: the conclusion fails, as it must.
`R = F_q` with `ψ_n` the inclusion: `Ψ` is the diagonal embedding.

## 2. Simplicity and Theorem A

**Lemma 2.1 (simplicity).** If `α` is minimal and topologically free, then `R` is simple.

*Proof.* Take `0 != P = Σ_(g ∈ S) f_g u_g ∈ J`, a nonzero ideal. Replacing `P` by `P u_h^(-1)`
we may assume `f_e != 0`. The set `{f_e != 0}` is open and nonempty, and free points are dense,
so pick a free point `x` with `f_e(x) = c != 0`. By continuity and freeness at `x` there is a
clopen `W ∋ x` with `f_e = c` on `W` and `α(g)W ∩ W = ∅` for `g ∈ S \ {e}`. Then

```text
χ_W P χ_W = Σ_g f_g χ_W χ_(α(g)W) u_g = c χ_W,
```

so `χ_W ∈ J`. By minimality and compactness, finitely many translates `α(h_i)W` cover `X`. Each
`χ_(α(h)W) = u_h χ_W u_h^(-1)` lies in `J`, and inclusion–exclusion writes `1` as a ring
expression in them. So `J = R`. ∎

This transcribes §1.3 of `simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md`, with free
points in place of the absence of periodic points. For Steinberg algebras over arbitrary fields
the general criterion is Clark–Edie-Michell–Sims and Steinberg; the direct proof above suffices.

**Definition (Kerr–Nowak, as restated by Ma, arXiv:2209.00580, `defn: residually finite action`,
read from source).** "A continuous action of `G` on a perfect compact metrizable space `X`,
equipped with a compatible metric `d`, is said to be *residually finite* if for any finite
`F ⊂ G` and `ε > 0`, there is a finite set `E ⊂ X`, equipped with a `G`-action `β` such that `E`
is `ε`-dense in `X` and `d(α(s)(z), β(s)(z)) < ε` for all `z ∈ E` and `s ∈ F`."

**Theorem A.** Let `α` be minimal, topologically free and residually finite on the Cantor set `X`,
and `k` a field. Then `R = LC(X,k) ⋊ Γ` embeds unitally and injectively in an algebraic
ultraproduct `∏_ω M_(N_n)(k)`, with `N_n = |E_n|`.

*Proof.* Fix increasing finite symmetric sets `F_n ∋ e` exhausting `Γ` and `ε_n -> 0`. Choose
`(E_n, β_n)` for `(F_n, ε_n)`. For `f ∈ LC(X,k)` put `D_n(f) = diag(f(z))_(z ∈ E_n)`, and for `g ∈ Γ`
let `P_n(g)` be the permutation matrix `δ_z -> δ_(β_n(g) z)`. Define, on normal forms,

```text
ψ_n(Σ_g f_g u_g) = Σ_g D_n(f_g) P_n(g).
```

Since normal forms are unique, `ψ_n` is well defined, additive and unital. `D_n` is multiplicative
on `LC(X,k)`, and `P_n` is a genuine representation because `β_n` is a genuine action.

*Window.* Let `W_n` be the set of `r = Σ f_g u_g` whose group support lies in `F_n^(1/2)` (a
symmetric set with `F_n^(1/2) F_n^(1/2) ⊆ F_n`, exhausting `Γ`) and whose coefficients `f_g` are
constant on every set of diameter `< ε_n`. Every `r` lies in `W_n` for large `n`, since each `f_g`
is locally constant on a compact space and has a positive Lebesgue number.

*Multiplicativity on the window.* It suffices to treat `f u_g` and `f' u_h`, with the products
`(f u_g)(f' u_h) = f·(f' ∘ α(g)^(-1)) u_(gh)`. On a basis vector `δ_z`:

```text
ψ_n(f u_g) ψ_n(f' u_h) δ_z = f'(β(h)z) f(β(gh)z) δ_(β(gh)z),
ψ_n(f·(f'∘α(g)^(-1)) u_(gh)) δ_z = f(β(gh)z) f'(α(g^(-1)) β(gh) z) δ_(β(gh)z).
```

With `w = β(gh)z ∈ E_n` we have `β(g^(-1)) w = β(h) z` and `d(α(g^(-1))w, β(g^(-1))w) < ε_n`, since
`g^(-1) ∈ F_n`. As `f'` is constant on sets of diameter `< ε_n`, the two coefficients agree.

So `ψ_n` is additive and multiplicative on `W_n` and unital. `R` is simple (Lemma 2.1), so Lemma S
gives the injective ultraproduct embedding. ∎

*Remarks.*
- Density of `E_n` is never used. Over a field, simplicity replaces all faithfulness bookkeeping.
- Ma's Prop `prop: free point` (read from source) lets `E_n` consist of free points. It is not
  needed here.
- For `Γ = Z` this recovers the ring statement of `minimal-subshift-algebra-is-simple-lef-ring`,
  since minimal `Z`-systems are residually finite (Kerr–Nowak Prop. 7.1 with Pimsner's Lemma 2, as
  quoted in Ma's Remark, read from source). The return-word models of the Pestov artifact are
  exactly such finite genuine actions.

**Corollary A1.** If `k = F_q` is finite, then for every `m >= 1`, `GL_m(R)` embeds in
`∏_ω GL_(m N_n)(F_q)`, so every finitely generated subgroup of `GL_m(R)` is LEF. If moreover `R` is
finitely generated as a ring (for instance when `α` is an expansive action, a subshift, of a
finitely generated group), then `EL_n(R)` is a finitely generated LEF group with property (T) for
every `n >= 3` (Ershov–Jaikin-Zapirain, Invent. Math. 179, Theorem 1.1, as quoted in the Pestov
artifact §2).
