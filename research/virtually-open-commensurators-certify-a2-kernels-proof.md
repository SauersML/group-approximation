---
rg: 2
id: virtually-open-commensurators-certify-a2-kernels-proof
kind: route
title: Kernel elements are exactly the elements of their own commensurator intersections, and certificates from arbitrary permutation labellings of stabilizer generators need no relator check
target: virtually-open-commensurators-certify-a2-kernels
requires:
  - a2-kernel-removal-forces-recursive-kernel
  - a2-kernel-recursion-ascends-normal-orbit-finite-chains
  - permutation-hnn-realization-of-type-a-actor-is-a2
  - houghton-groups-have-at-most-exponential-dehn-function
---

Notation is as in the target. We use:
- from `a2-kernel-removal-forces-recursive-kernel` (a): membership in each
  `Stab_G(x_i)` is decidable, the action on encoded points is computable, and `K` is
  co-r.e.;
- the certificate lemma (1) of `a2-kernel-recursion-ascends-normal-orbit-finite-chains`.

Equality of encoded points is decidable: `c.x_i = d.x_j` iff `i = j` and
`d^-1 c in Stab_G(x_i)`.

## Four properties of virtual openness

Let `H, H' <= G`.

**(P1) Upward closure.** If `U <= V <= H` and `U` is virtually open in `H`, then so is
`V`. Indeed `[H_F : V ∩ H_F] <= [H_F : U ∩ H_F]`.

**(P2) Intersections.** If `U_1, U_2` are virtually open in `H`, then so is
`U_1 ∩ U_2`.
- Take witnesses `F_1, F_2` and put `F = F_1 ∪ F_2`.
- `H_F <= H_(F_i)`, so `[H_F : U_i ∩ H_F] <= [H_(F_i) : U_i ∩ H_(F_i)] < ∞`.
- Two finite-index subgroups of `H_F` meet in a finite-index subgroup.

**(P3) Conjugation.** If `U` is virtually open in `H`, then `gUg^-1` is virtually open
in `gHg^-1`. This holds because `g H_F g^-1 = (gHg^-1)_(g.F)`, where `g.F` is computed
through `ρ`.

**(P4) Transfer.** Suppose `B <= E <= H ∩ H'`, `B` is virtually open in `H'`, and `E`
is virtually open in `H`. Then `B` is virtually open in `H`.
- Take `F` with `[H'_F : B ∩ H'_F] < ∞`, and `F'` with `[H_(F') : E ∩ H_(F')] < ∞`.
- Put `F'' = F ∪ F'`, so that `[H_(F'') : E ∩ H_(F'')] < ∞`.
- `X := E ∩ H_(F'')` fixes `F` and lies in `H'`, so `X <= H'_F`. Since `B <= E`,
  `B ∩ X = B ∩ H_(F'')`. Hence `[X : B ∩ X] <= [H'_F : B ∩ H'_F] < ∞`.
- Multiplying the two indices, `[H_(F'') : B ∩ H_(F'')] < ∞`.

## (a)

**`Γ ⊆ VOComm`.** For `γ in Γ`, `Γ ∩ γΓγ^-1 = Γ`.

**Inverses.** `Γ ∩ g^-1Γg = g^-1 (gΓg^-1 ∩ Γ) g`. By (P3), `g^-1` exchanges the two
conditions defining `g in VOComm`.

**Products.** Let `g, h in VOComm` and put:
- `E_1 = Γ ∩ gΓg^-1`, virtually open in `Γ` and in `gΓg^-1`;
- `E_2 = g(Γ ∩ hΓh^-1)g^-1 = gΓg^-1 ∩ ghΓ(gh)^-1`. By (P3) this is virtually open in
  `gΓg^-1` and in `ghΓ(gh)^-1`;
- `B = E_1 ∩ E_2 ⊆ Γ ∩ ghΓ(gh)^-1`.

Then:
- by (P2), `B` is virtually open in `gΓg^-1`;
- by (P4) with `H = Γ`, `H' = gΓg^-1` and `E = E_1`, `B` is virtually open in `Γ`;
- by (P4) with `H = ghΓ(gh)^-1`, `H' = gΓg^-1` and `E = E_2`, `B` is virtually open in
  `ghΓ(gh)^-1`.

By (P1), `Γ ∩ ghΓ(gh)^-1` is virtually open in both. So `gh in VOComm`.

**Kernel elements.** Let `k in K` and `e in Γ ∩ k^-1Γk`. Then `kek^-1 in Γ` and
`ρ(kek^-1) = ρ(e)`, so `(kek^-1)e^-1 in Γ ∩ K = 1`, and `e in C_Γ(k)`. Conversely
`C_Γ(k) ⊆ Γ ∩ k^-1Γk`. So `Γ ∩ k^-1Γk = C_Γ(k)`. Applying this to `k^-1 in K` gives
`Γ ∩ kΓk^-1 = C_Γ(k)`.

Hence `k in VOComm` requires `C_Γ(k)` to be virtually open in `Γ`. Conversely, if
`C_Γ(k)` is virtually open in `Γ`, then:
- by (P3), `kC_Γ(k)k^-1 = C_Γ(k)` is virtually open in `kΓk^-1`;
- so both conditions hold. ∎

## Certificates

**Construction.** Fix, for each `n >= 0`, the EO data. A certificate is produced from
the following choices:
1. an `n`-tuple `F` of encoded points;
2. the first `γ in Γ` (a word in the generators of `Γ`) and representative tuple `T`
   found with `γ.T = F`. The search terminates, because the representatives meet
   every orbit and tuple equality is decidable;
3. `S_F = {γ s γ^-1 : s in gens(Γ_T)}`, which generates `Γ_F = γ Γ_T γ^-1`, and
   `Y_F = {γ.y : y in reps(Γ_T)}`, which meets every `Γ_F`-orbit;
4. an integer `m >= 1` and an arbitrary map `θ : S_F -> Sym(m)`;
5. words `c_2, ..., c_m` in `S_F`, with `c_1 = 1`.

Put:
- `a_(j,s) = c_(θ(s)j)^-1 s c_j` for `s in S_F` and `1 <= j <= m`;
- `A = {a_(j,s)}`;
- `Y = {c_j^-1 . y : y in Y_F, 1 <= j <= m}`, where `c_j^-1.(d.x_i)` is encoded by the
  word `c_j^-1 d` and the index `i`.

`C` is the set of all pairs `(A, Y)` obtained this way. It is r.e., since each pair is
computed from finitely many choices.

**Validity: `<A>.Y = S` for every pair, with no check.** Put `P = ⋃_j c_j <A>`, a
subset of `Γ_F`.
- `1 = c_1 . 1` lies in `P`.
- For `s in S_F`: `s c_j <A> = c_(θ(s)j) a_(j,s) <A> = c_(θ(s)j) <A>`. So `sP ⊆ P`.
- `θ(s)` is a permutation. So each index `i` equals `θ(s)j` for some `j`, and
  `s^-1 c_i <A> = c_j a_(j,s)^-1 <A> = c_j <A>`. So `s^-1 P ⊆ P`.

A subset containing `1` and closed under left multiplication by `S_F^(±1)` contains
`Γ_F`. So `Γ_F = ⋃_j c_j <A>`, and inverting, `Γ_F = ⋃_j <A> c_j^-1`. Therefore

```text
S = Γ_F . Y_F = ⋃_j <A> . (c_j^-1 . Y_F) = <A> . Y.
```

**Completeness.** Let `W <= Γ_F` have finite index `m`. Take `c_1 = 1, ..., c_m` to be
left coset representatives of `W`, and `θ(s)` the permutation with
`s c_j W = c_(θ(s)j) W`. Then every `a_(j,s)` lies in `W`.

## (b)

Let `k in K`. By hypothesis some finite `F` has
`[Γ_F : C_Γ(k) ∩ Γ_F] = m < ∞`. Order `F` as a tuple, and apply Completeness to
`W = C_Γ(k) ∩ Γ_F`. This gives `(A, Y) in C` with `A ⊆ W ⊆ C_Γ(k)`, so `[k, a] = 1` for
every `a in A`.

Apply (1) with:
- `W` = all words;
- `K_0 = {1}`, whose word set is r.e. since `G` is finitely presented;
- `C` as above, all of whose pairs are valid.

So `K` is r.e. It is co-r.e., hence recursive.

**The particular case.** If `G = <Γ, g_1, ..., g_r>` with `g_i in VOComm`, then by (a)
`G = VOComm`. So every `k in K` lies in `VOComm`, and by (a) `C_Γ(k)` is virtually
open. ∎

## (c)

Only `F` empty is used. The data are:
- the finitely many generators of `Γ`, as `S_F`;
- finitely many encoded points meeting every `Γ`-orbit, as `Y_F`.

These are fixed non-uniform data. The Construction runs over `m`, `θ` and `c_j` only.
Validity and Completeness are unchanged. If `C_Γ(k)` has finite index `m`, Completeness
gives a certificate, and (1) applies as in (b).

**The particular case.** Let `Comm` be the set of `g` with `Γ ∩ gΓg^-1` of finite
index in both `Γ` and `gΓg^-1`. It is a subgroup: take (a) with `F` empty throughout,
or Step 1 of `permutation-hnn-realization-of-type-a-actor-is-a2-proof`. By the kernel
computation in (a), `k in Comm` iff `C_Γ(k)` has finite index. ∎

## (d)

By `permutation-hnn-realization-of-type-a-actor-is-a2` (a):
- `L ↷ X` is of type `[A_2]`;
- `K ∩ Γ = 1`, since `Γ ↷ X` is faithful;
- `K` recursive iff `<Γ, π>` has solvable word problem.

By Britton's lemma, `Γ ∩ tΓt^-1 = D_2` (as in the proof of that node).

`t in VOComm_L(Γ)`:
- `Γ ∩ tΓt^-1 = D_2` is virtually open in `Γ` by hypothesis;
- it is virtually open in `tΓt^-1` iff `t^-1 D_2 t = D_1` is virtually open in `Γ`, by
  (P3) applied with `g = t^-1`. That is also a hypothesis.

So `L = <Γ, t>` with `t in VOComm`, and (b) applies. Note that `D_1` is automatically
orbit-finite: it contains a finite-index subgroup of an orbit-finite `Γ_F`.

For tuple stabilizers, `D_1 ⊇ U` with `[Γ_F : U] < ∞` is virtually open with witness
`F`. ∎

## (e)

Let `n >= 3` and `X = {1..n} x N`. `H_n` is the group of permutations `σ` of `X` for
which there are integers `m_i` and `N` with `σ(i, p) = (i, p + m_i)` for all `p >= N`.

**Type (A).**
- `H_n` is finitely presented: Lee, arXiv:1212.0257, Theorem C, with the presentation
  recorded in `houghton-groups-have-at-most-exponential-dehn-function`.
- Every finitary permutation of `X` lies in `H_n`, so `H_n` is highly transitive on
  `X`, and there is one orbit of two-element subsets.
- Point stabilizers are finitely generated by the conjugation below with `|F| = 1`.
- The action is faithful by definition.

**Conjugation.** Let `F ⊆ X` be finite, and let `f_i` be the number of points of `F`
on ray `i`. Define `β' : X -> X \ F` by letting `β'(i, p)` be the `p`-th point of ray
`i` not in `F`, in increasing order. It is a bijection `X -> X \ F`. For `p` beyond
every point of `F`, `β'(i, p) = (i, p + f_i)`.

For `σ in H_n`, `β' σ β'^-1`, extended by the identity on `F`, is a permutation of `X`
fixing `F`. On ray `i` it eventually translates by `m_i`, so it lies in `(H_n)_F`.
Conversely, for `ω in (H_n)_F`, `β'^-1 ω β'` lies in `H_n`, by the same computation.
So `(H_n)_F = β' H_n β'^-1` (extended by the identity on `F`). Consequently:
- `(H_n)_F` is finitely generated, by the conjugates of Lee's generators;
- `(H_n)_F` is transitive on `X \ F`, so its orbits are the singletons of `F` and
  `X \ F`.

**Effectivity.** Elements of `H_n` given by words are computable as finite data: the
vector `(m_i)`, a threshold `N`, and the finitely many values below the threshold.
Equality of two such descriptions is decidable. Every `H_n`-orbit on `X^k` is
determined by the equality pattern of the tuple. The algorithm for input `k`:
- lists one tuple per equality pattern, with values among `(1,1), ..., (1,k)`;
- for each such `T` with support `F`, computes the finite descriptions of the
  conjugated generators;
- searches words in Lee's generators until each matches. The search terminates because
  each element lies in `H_n`;
- outputs as orbit representatives the points of `F` and `(2,1)`.

Points are encoded as words applied to `x_0 = (1,1)`, again found by search. So
`H_n ↷ X` is EO. ∎
