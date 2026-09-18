---
rg: 2
id: mixed-degree-units-lift-non-positive-fixed-classes-proof
kind: route
title: The core is ultramatricial, a corner isometry exists when A^-1 contracts the unit class, and cancellation assembles a unit from partial isometries of degrees 1, -1 and 0
target: mixed-degree-units-lift-non-positive-fixed-classes
requires:
  - frame-generated-simple-rings-have-no-vacuum
  - degree-one-corner-unitaries-fail-the-k-budget
  - abc-twisted-laurent-k-theory-fibration
  - infinitely-generated-symbols-block-fp-elementary-groups
---

Notation of `frame-generated-simple-rings-have-no-vacuum`: `S_n`, `T_n` are the rows and columns of words of length
`n`, and `P^(n) = T_n S_n`. Here `s t = 1`, so `E_n = S_n T_n = 1`.

**Item 1.**
- By the normal form, `R_0` is spanned by the `s_α b t_β` with `|α| = |β|`. So `R_0 = ∪_n ι_n(P^(n) M_(k^n)(B) P^(n))`
  with `ι_n(c) = S_n c T_n`.
- `ι_n` is a unital ring map, since `S_n P^(n) T_n = E_n = 1`. It is injective, since `T_n ι_n(c) S_n = P^(n) c P^(n) = c`.
  The inclusions are `c -> φ(c)`, since `S_n c T_n = S_(n+1) φ(c) T_(n+1)`.
- Each `P^(n) M(B) P^(n)` is a corner of a matrix ring over a product of `U_Q`-type rings, hence ultramatricial.
  So `R_0` is ultramatricial. Cancellation holds, because equality in the colimit is reached at a finite semisimple
  stage (gq-referee-a, N1). `P^(n)` is full, since `A` has positive row sums, so the corner has `K_0 = K_0(B)` (N4).
- `K_0(R_0) = colim(K_0(B) --A--> K_0(B) --A--> ...)`, which is `Q^m` in level-`0` coordinates when `A` is invertible.
- For `g in M_j(B)`, `w_g = S φ(g)` (block-diagonal `S`) has `w_g w_g' = g` and `w_g' w_g = φ(g)`, with
  `w_g' = φ(g) T` (item 6 of the corner node). So a degree-`1` partial isometry with domain of class `A[g]` has range
  of class `[g]`. In general (gq-referee-a, N2): let `w` be of degree `1` with `w = E w D`, `w' w = D` and `w w' = E`.
  Then `w = s (t w)`, and `c = t w`, `c' = w' s` have entries in `R_0`. `c' c = w' (s t) w = D`, `c c' = t E s = φ(E)`,
  and `c c' c = c`. So `D ~ φ(E)`, that is `[D] = A[E]` in level-`0` coordinates, since `φ(ι_1(c)) = c`.

**Item 2.**
- Pick an idempotent `g in B` with `[g] = c`. Such a `g` exists: each `B_i` has idempotents of every class in
  `[0,1] ∩ Q`.
- `[φ(g)] = A c = [1_B]`, so by cancellation `φ(g) = x y` and `y x = 1_B` for some `x in M_(k×1)(B)`, `y in M_(1×k)(B)`.
- Put `t_+ = s x in R_1` and `t_- = y t in R_(-1)`. Then `t_- t_+ = y p x = y x = 1`, using `p x = x`. And
  `t_+ t_- = s φ(g) t = g`.
- **Structure.** For `a in R_n` with `n >= 1`, `a = (a t_-^n) t_+^n` with `a t_-^n in R_0`. Similarly
  `R_(-n) = t_-^n R_0`. This is the grading of the corner skew Laurent ring. The universal one maps onto `R`
  degreewise, and `r t_+^n = 0` forces `r α^n(1) = 0`, so the map is injective.

**Item 3.**
- Write `v = [dom_+] - A[dom_-]` for vectors `dom_+ = v + A b` and `dom_- = b`. Take `b >= 0` with `v + A b >= 0` and `v + b >= 0`, for
  example `b = N·(1, ..., 1)` for large `N` (gq-referee-a, N3).
  Ranges are `ran_+ = A^-1 dom_+` and `ran_- = A dom_-`, by item 1 applied to `w_+` and to the adjoint of `w_-`.
- Then `dom_+ + dom_- - ran_+ - ran_- = (1 - A^-1)(v + A b) + (1 - A) b = (1 - A^-1) v = 0`, since `A v = v`. So the
  totals agree. That is `[dom w_+] - [ran w_-] = v` in level-`0` coordinates, since `ran_- = A b`.
- Scale by `ε`. For `ε` small, choose pairwise orthogonal idempotents in `R_0` with classes `ε dom_+` and `ε dom_-`.
  Their sum `D` satisfies `1 - D >= 0` with class `[1] - ε(dom_+ + dom_-)`.
- Choose orthogonal idempotents for the ranges, with complement `1 - E` of class `[1] - ε(ran_+ + ran_-)`. This is
  the same class, so `1 - D ~ 1 - E` by cancellation, via `w_0` of degree `0`.
- Degree-`±1` partial isometries with these domains and ranges exist. Start from `w_g` or `w_g'` of item 1, and
  adjust by degree-`0` equivalences, using cancellation.
- `U = w_+ + w_- + w_0` maps each domain onto its range. Domains are orthogonal with sum `1`, and so are ranges. So
  `U` is a unit with inverse `w_+' + w_-' + w_0'`.
- `Q` is central.

**Item 4.**
- By (CSL), `∂{λ, U} = λ ∪ ∂[U] = λ ⊗ ε v`.
- `K_1(R_0) = Q^x ⊗ K_0(R_0)`, since `R_0` is ultramatricial over `Q` and `det` is used on each simple factor.
- `K_0(R_0)` is torsion-free, and `Z v -> K_0(R_0)` stays injective after tensoring with the free part of `Q^x`. So
  `{λ ⊗ ε v : λ in Q_(>0)} ≅ Q_(>0)`, which is not finitely generated.
- So the `{λ, U}` generate an infinitely generated subgroup of `Sym(R)`, and
  `infinitely-generated-symbols-block-fp-elementary-groups` applies.
- **The last sentence.**
  - If `ker(1 - A) = 0`, then `coker(1 - A) = 0`, so `[1]` is torsion by item 7(a) of the corner node.
  - Otherwise `v` exists, and items 3 and 4 apply.
