---
rg: 2
id: micro-supported-word-automorphisms-pointwise-inner-proof
kind: route
title: Compare the support of r t r^-1 with the translated supports of the word factors, then use connectedness and breakpoint slopes on the circle
target: micro-supported-word-automorphisms-are-pointwise-inner
requires: []
---

Notation is as in the claim. `supp(g) = { p : g(p) != p }` is open, and
`supp(g t g^-1) = g(supp t)`.

## (1) Pointwise innerness

1. **Rewriting the word.** `u(1) = β(1) = 1` gives `g_0 g_1 ... g_k = 1`. With
   `h_j = g_0 ... g_{j-1}` we get `h_1 = g_0`, `h_j^-1 h_{j+1} = g_j` and
   `h_k g_k = 1`. So, for all `t ∈ S`,

       u(t) = (h_1 t^{e_1} h_1^-1)(h_2 t^{e_2} h_2^-1) ... (h_k t^{e_k} h_k^-1) .

   Here `k >= 1`: if `k = 0`, then `u` is constant, contradicting `S != 1`
   (micro-support forces `S != 1` when `Y` is nonempty).
2. **Supports.** If `supp(t) ⊆ J`, the `j`-th factor is supported in `h_j(J)`. So
   `u(t)` fixes every point outside `h_1(J) ∪ ... ∪ h_k(J)`.
3. **Every point is covered.** Suppose `r(p) != h_j(p)` for all `j`. Since `Y` is
   Hausdorff, choose open sets `V ∋ r(p)` and `V_j ∋ h_j(p)` with `V ∩ V_j = ∅`.
   Put `J = r^-1(V) ∩ h_1^-1(V_1) ∩ ... ∩ h_k^-1(V_k)`, an open set containing `p`.
   Take `1 != t ∈ rist_S(J)`. Then `r t r^-1 = β(t) = u(t)`.
   - The left side moves exactly the points of `r(supp t)`, a nonempty subset of
     `r(J) ⊆ V`.
   - By step 2, the right side moves only points of `∪ h_j(J) ⊆ ∪ V_j`, which is
     disjoint from `V`.

   So `r t r^-1` moves no point, and `t = 1`, a contradiction.
4. **Closedness.** `F_j` is the equalizer of two continuous maps into a Hausdorff
   space. ∎(1)

## (2) Uniqueness

Let `z ∈ Homeo(Y)` commute with `S`, and suppose `z(p) != p`. Choose an open
`J ∋ p` with `z(J) ∩ J = ∅`, and take `1 != t ∈ rist_S(J)`. Then
`t = z t z^-1` is supported in `z(J)` and in `J`, so `t = 1`, a contradiction.

So `c_r|_S = c_{r'}|_S` forces `r = r'`. If `β = c_s` with `s ∈ S`, then `r = s`.
∎(2)

## (3) Higman--Thompson circle kernels

Put `T = T_{n,r_0}` and `C = R/r_0 Z`. Call a point *n-adic* if it lies in
`Z[1/n]/r_0 Z`. For an orientation-preserving PL homeomorphism `f` and a point `p`,
put `σ_f(p) = f'(p+)/f'(p-)`. The chain rule gives

    σ_{f∘g}(p) = σ_f(g(p)) · σ_g(p) ,      σ_{f^-1}(f(p)) = 1/σ_f(p) .

**Hypotheses check.**
- *Normality.* `S` contains `[T,T]`, so `S ⊴ T` and `T/S` is abelian.
- *Micro-support.* Let `I` be an open interval, and take an n-adic interval
  `[a,b] ⊆ I`. By the import below, the elements of `T` supported in `[a,b]` form a
  copy of `F_n`, which is nonabelian. A nontrivial commutator of two such elements
  lies in `[T,T] <= S` and is supported in `I`.
- *Spatiality.* Let `β` be a word automorphism with word `u`. By Rubin's theorem
  (imported), `β = c_r|_S` for some `r ∈ Homeo(C)` normalizing `S`.

**Step A: `r` is PL with finitely many pieces from the `h_j`.**
1. For `i != j`, the set `C_{ij} = Fix(h_j^-1 h_i)` is a finite union of closed
   intervals and points. On each linear piece of the PL map `h_j^-1 h_i`, the fixed
   set is either the whole piece or at most one point.
2. Let `E` be the finite set of all breakpoints of the `h_j` together with all
   boundary points of all `C_{ij}`.
3. Let `I` be a component of `C \ E`. Each `C_{ij} ∩ I` has no boundary point in
   `I`, so it is clopen in the connected set `I`, hence empty or all of `I`. So the
   `h_j` fall into classes: elements of one class agree on `I`, and elements of
   different classes agree nowhere on `I`.
4. By (1), `I` is covered by the relatively closed sets `F_c ∩ I`, one per class.
   These are pairwise disjoint. A finite partition of a connected space into closed
   sets has a single nonempty member.
5. So `r|_I = h_{j(I)}|_I`, and `r` is PL with breakpoints in `E`, slopes in `n^Z`,
   and orientation preserving.

**Step B: `r` preserves n-adic points and their complement.** Every `h ∈ T` maps
the n-adic points bijectively onto themselves. By (1), every `p` has
`r(p) = h_j(p)` for some `j`. So `r` sends n-adic points to n-adic points and
non-n-adic points to non-n-adic points.


**Import (Brown; Bieri--Strebel).** For every point `y ∈ C` and every open interval
`J ∋ y`, some element of `T` supported in `J` moves `y`. The elements of `T`
supported in an n-adic interval `[a,b]` form a copy of `F_n`, which fixes no point
of `(a,b)`. The micro-support check above uses the same import.

**Step C: `S·x` is infinite for every `x ∈ C`.**
1. Take `g ∈ T` supported in a small interval around `x` with `g(x) != x`.
2. Take `g' ∈ T` supported in an interval `J'` around `y = g(x)` that misses `x`,
   with `g'(y) != y`.
3. Put `d_m = g^-1 g'^m g g'^-m`, a commutator, so `d_m ∈ [T,T] <= S`.
4. Since `x ∉ J'`, `d_m(x) = g^-1(g'^m(y))`. The points `g'^m(y)` are pairwise
   distinct: `g'` is an orientation-preserving homeomorphism of the interval
   component of `supp(g')` containing `y`, so the orbit of `y` is strictly monotone.

**Step D: every breakpoint of `r` is n-adic.** Suppose `σ_r(x_0) != 1` and `x_0` is
not n-adic.
1. By Step C, choose `p ∈ S·x_0` outside the finite breakpoint set of `r`, and
   `t ∈ S` with `t(p) = x_0`.
2. `p` is not n-adic, because `t^-1` preserves n-adic points. So `p` is not a
   breakpoint of `t`, and `σ_t(p) = 1`.
3. The element `g = r t r^-1` lies in `S`. By the chain rule,

       σ_g(r(p)) = σ_r(t(p)) · σ_t(p) · σ_{r^-1}(r(p)) = σ_r(x_0) · 1 · 1/σ_r(p) = σ_r(x_0) != 1 .

4. So `g` has a breakpoint at `r(p)`, which is not n-adic by Step B. But elements of
   `S <= T` break only at n-adic points. This is a contradiction.

**Step E: conclusion.**
- By Steps A, B and D, `r` is an orientation-preserving PL homeomorphism of `C`
  with finitely many breakpoints, all n-adic, slopes in `n^Z`, mapping n-adic points
  to n-adic points. So `r ∈ T` by definition.
- By (2), `r` is unique.
- *The quotient.* Let `W <= Aut(S)` contain `Inn(S)`, with every element a word
  automorphism. Each `β ∈ W` is `c_{r_β}|_S` with a unique `r_β ∈ T`, and
  `β -> r_β` is a homomorphism, again by uniqueness. Composing with `T -> T/S`
  gives a homomorphism with kernel `{ β : r_β ∈ S } = Inn(S)`. So `W/Inn(S)` embeds
  in `T/S`.
- *Finite generation.* `T/S` is abelian, since `[T,T] <= S`, and finitely generated,
  since `T` is finitely generated (Brown, imported). Subgroups of finitely generated
  abelian groups are finitely generated. ∎(3)
