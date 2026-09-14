# Gottschalk through Rokhlin entropy: what the landed toolkit can reach, and the exact gap

Lane `gk3-rokhlin-tester`, 2026-09-14. Handwritten proofs, nothing computed. Unreviewed. Part 2
(`research/artifacts/gk3-rokhlin-tester-2026-09-14-part2.md`) proves Theorem T, the soficity transfer for (O6).

**Verdict.** Not decided. No new Rokhlin entropy lower bound over a nonsofic group was found. The lane lands two
theorems:
- **Barrier.** `rokhlin-permanence-toolkit-certifies-only-sofic-groups` (Section 2): started from the sofic groups, the
  six landed permanence operations for Rokhlin maximality produce exactly the sofic groups. The Gottschalk tester host
  lies outside that class, so the Rokhlin route to Gottschalk needs a lower-bound mechanism that is not a permanence
  theorem. Section 5 names the three open statements that would supply one.
- **Transfer.** `weakly-bernoulli-liftable-finite-extensions-are-sofic` (part 2): a finite extension of a sofic group with
  a weakly Bernoulli liftable action is sofic, for every finite normal kernel.

## 0. State read on main

- **Goal chain.** `gottschalk-surjunctivity-fixed-two-generator-tester` (one host `U`), then
  `fixed-tester-surjunctive-via-rokhlin-entropy` with `strict-automaton-lowers-bernoulli-rokhlin-entropy`, and the open
  `bernoulli-rokhlin-entropy-maximal-on-fixed-tester`. It is equivalent to `tester-host-has-positive-rokhlin-entropy-action`
  through `tester-host-pos-iff-maximal-bernoulli-rokhlin-entropy`.
- **Finitary form.** `bernoulli-rokhlin-deficit-has-a-finitary-witness`: `rho_q(G) = inf Phi`, and `Phi` depends only on
  the incidence pattern of the products `fe` together with `1`. By `bernoulli-per-copy-rokhlin-entropy-is-zero-or-full`,
  `inf Phi` is `0` or `log q`.
- **Permanence operations landed.**
  - subgroups and finite index: `bernoulli-rokhlin-maximality-passes-to-subgroups`;
  - local embeddings and directed colimits: `rokhlin-maximality-closed-under-local-embeddings`, and the canonical hosts
    of the finitary witness node;
  - co-amenable overgroups: `rokhlin-maximality-ascends-co-amenable-subgroups`;
  - finite normal quotients: `rokhlin-maximality-descends-along-finite-normal-quotients`;
  - finite kernels through a weakly Bernoulli lift: `finite-kernel-rokhlin-ascent-from-weakly-minimal-lift`, cases (i)
    and (ii).
- **Finite-kernel barriers landed.** `bernoulli-maximizes-extension-class-norm` (the norm decides weakly Bernoulli lifts),
  `gohla-thom-lattices-no-weakly-bernoulli-liftable-action`, `weakly-bernoulli-liftable-action-makes-extension-sofic`, and
  `bernoulli-lifts-across-finite-kernels-force-virtual-splitting` (Popa, exact lifts).

## 1. Sources re-verified

Seward, *Krieger's finite generator theorem for actions of countable groups II*, arXiv:1501.03367v4. The PDF text on
MSI (`/scratch.global/sauer354/lit2/1501.03367v4.txt`) was re-read on 2026-09-14:
- Theorem 1.10 at line 239: "Let G be a countably infinite group and let (L;λ) be a standard probability space with
  H(L;λ) < ∞. Then h^Rok_G(L^G;λ^G) = min{H(L;λ), h^Rok_sup(G)}."
- Theorem 1.11 at line 252 and Theorem 1.12 at line 269.
- "INF⇒RBS⇒INV+CPE+GOT+KAP" at line 294, and Corollary 4.1 at line 725.

These match `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`.

## 2. Theorem K: the landed operations stay inside the sofic groups

**Operations.** Let `R` be the smallest class of countable groups that contains every sofic group and is closed under:
- **(O1) subgroups;**
- **(O2) finite-index overgroups:** if `H <= G` has finite index and `H ∈ R`, then `G ∈ R`;
- **(O3) local embeddings:** if every finite `S ∋ 1` of `H` has an injective `η : S -> K ∈ R` with `η(ab) = η(a)η(b)`
  whenever `a, b, ab ∈ S`, then `H ∈ R`. This contains directed colimits with arbitrary structure maps;
- **(O4) co-amenable overgroups:** if `H <= G` is infinite and co-amenable in the Følner sense and `H ∈ R`, then `G ∈ R`;
- **(O5) finite normal quotients:** if `W ∈ R` and `N ◁ W` is finite, then `W/N ∈ R`;
- **(O6) weakly Bernoulli finite ascent:** let `N ◁ W` be finite with `Q = W/N ∈ R` finitely generated. Then `W ∈ R` if
  - (i) some finite-entropy free ergodic `Q`-action lifting to a free `W`-action is weakly contained in all free
    `Q`-actions, or
  - (ii) some finite-entropy Bernoulli shift of `Q` lifts to a free `W`-action.

  These are cases (i) and (ii) of `finite-kernel-rokhlin-ascent-from-weakly-minimal-lift`. Its case (iii) is
  `seward-direct-product-relative-rokhlin-entropy-conjecture`, which is open and is not an operation here.

By the nodes listed in Section 0, every group in `R` is Rokhlin-maximal, since sofic groups are maximal by item 4 of
`seward-per-group-rokhlin-entropy-of-bernoulli-shifts`.

**Theorem K.** `R` is exactly the class of sofic groups.

*Proof.* It suffices that each operation carries sofic groups to sofic groups. Use the permutation definition: `G` is
sofic when for every finite `F ∋ 1` and `ε > 0` there is a map `σ : F -> Sym(V)`, `V` finite, such that `σ_g σ_h v =
σ_(gh) v` for all `g, h, gh ∈ F` and `σ_g v != v` for all `g ∈ F \ {1}`, on at least `(1 - ε)|V|` points `v`.

- **(O1), (O2).** Elek–Szabó Theorem 1 (`elek-szabo-sofic-permanence`) gives subgroups and amenable extensions. For
  (O2), the normal core `N` of `H` is a sofic finite-index normal subgroup and `G/N` is finite, so `G` is sofic.
- **(O3).** Let `F ∋ 1` be finite in `H` and `S = F ∪ FF`. Take `η : S -> K`, `K` sofic, as in (O3). Then
  `η(1) = η(1)^2 = 1`, and `η(g) != 1` for `g != 1` by injectivity. A good map `τ` for `η(S)` over `K` gives the good map
  `σ_g := τ_(η(g))` for `F` over `H`, because `g, h, gh ∈ F` gives `η(gh) = η(g)η(h)`. For a directed colimit
  `G = colim G_i`, a finite `S ⊂ G` lifts to some stage, and the finitely many products that coincide in `G` already
  coincide at a later stage `j`. The lift to `G_j` is injective on `S` and multiplicative on `S`, so `G` locally embeds
  into the `G_i`.
- **(O4).** This is the theorem of Brude–Sasyk recorded on main. The direct proof is Remark 4 in Section 2 of
  `research/artifacts/rokhlin-co-amenable-ascent-and-thompson-v-2026-09-12.md`. Put `c(ω, g) = r(ω) g r(ωg)^-1 ∈ H` over a
  Følner set `Ω'` of cosets, and let `g` act on `Ω' × [d_n]` by `(ω, i) -> (ω g^-1, σ_n(c(ω g^-1, g)) i)`. The cocycle
  identity bounds the defect by the boundary fraction plus the defects of `σ_n`, and a fixed point needs `ωg = ω` with
  `c(ω, g) != 1`. This lane read the construction and agrees with it.
- **(O5).** Let `G` be sofic, `N ◁ G` finite, and `F̄ ∋ 1` finite in `G/N`, with `F` a set of lifts containing `1`. Put
  `S = (F ∪ N)^3` and take a good map `σ` for `S` with small `δ`. Let `Good` be the set of `v` with `σ_a σ_b v = σ_(ab) v`
  for `a, b, ab ∈ S` and `σ_a v != v` for `a ∈ S \ {1}`. Let `V_0 = {v : σ_n v ∈ Good for all n ∈ N}`.
  - For `v ∈ V_0` the orbit `O(v) = {σ_n v : n ∈ N}` has `|N|` elements. It satisfies `σ_m v ∈ V_0` and
    `O(σ_m v) = O(v)` for `m ∈ N`. So `V_0` is a disjoint union of orbits of size `|N|`, and `|V \ V_0| <= C δ |V|` with
    `C` depending on `|S|`.
  - For `ḡ ∈ F̄` with lift `g`, put `τ_ḡ(O(v)) = O(σ_g v)`. It is well defined on good orbits:
    `σ_g σ_n v = σ_(gng^-1) σ_g v ∈ O(σ_g v)`.
  - It is injective there. If `σ_g w = σ_m σ_g v`, then `σ_g w = σ_g σ_(g^-1 m g) v`, so `w ∈ O(v)`.
  - Multiplicativity: if `gh = kn_0` with `k` the lift of `ḡh̄`, then
    `σ_g σ_h v = σ_(k n_0) v = σ_(k n_0 k^-1) σ_k v ∈ O(σ_k v)`, so `O(σ_g σ_h v) = O(σ_k v)`.
  - Freeness: `τ_ḡ` fixes `O(v)` only if `σ_g v = σ_n v`, that is `σ_(n^-1 g) v = v`. Then `n^-1 g = 1` and `ḡ = 1`.
  - Complete each `τ_ḡ` to a permutation of the orbit set together with `V \ V_0`. The bad proportion is `O(δ)`.
- **(O6).** Theorem T of part 2 (`weakly-bernoulli-liftable-finite-extensions-are-sofic`), through Corollary T3.
  - In case (i) the lifted action is weakly contained in the Bernoulli shift `[0,1]^Q`, which is free.
  - In case (ii) the lifted Bernoulli shift is a factor of `[0,1]^Q`.

  So `W` is sofic. The central case over a finitely presented base is `weakly-bernoulli-liftable-action-makes-extension-sofic`.

So the sofic class contains the sofic groups and is closed under (O1)–(O6), hence contains `R`. The reverse inclusion
is by definition. QED

**Novelty and scope.** The scope remark on `rokhlin-maximality-ascends-co-amenable-subgroups` already says that every
group currently known to be maximal is sofic. Theorem K turns that remark into a closure theorem. It covers local
embeddings, finite-kernel descent and the weakly Bernoulli ascent, and it covers any order of application. It is a
barrier, and it says nothing about whether a nonsofic group is maximal.

## 3. Consequences

1. **Tester host.** `U` contains every recursively presented group, including the finitely presented nonsofic group of
   `fp-surjunctive-nonsofic-group-exists`. So `U` is nonsofic and `U ∉ R`. No iteration of (O1)–(O6) from sofic groups
   proves `bernoulli-rokhlin-entropy-maximal-on-fixed-tester`.
2. **Deligne's triple cover.** `E_3 ∈ R` iff `deligne-triple-cover-is-sofic`.
   - Case (i) of `finite-kernel-rokhlin-ascent-from-weakly-minimal-lift` gives soficity by Theorem T.
   - Case (ii) is excluded by Popa.
   - So `rokhlin-maximality-ascends-finite-normal-extensions` can decide `deligne-triple-cover-surjunctive` beyond
     soficity only through case (iii), Seward's direct-product conjecture.
3. **Kun–Thom wreath and Gohla–Thom extensions.** Being nonsofic, they lie outside `R`. So
   `kun-thom-wreath-bernoulli-rokhlin-maximal` stays exactly as open as recorded.
4. **A Rokhlin deficit on any group kills the route for all groups.** `U` contains every countably generated recursively
   presented group, and maximality passes to subgroups. So a deficit over a recursively presented group gives one over
   `U`. Then `bernoulli-rokhlin-entropy-maximal-on-fixed-tester` is false, while Gottschalk's conjecture could still
   hold (`leavitt-units-have-zero-rokhlin-entropy-supremum`, Payoff).

## 4. Floor attempts, and why small windows do not help

Target: a floor `Phi >= c > 0` valid on the tester host. By the per-copy dichotomy that is enough.
- **Counting bounds.**
  - The read bound gives `Phi >= log q / |E|`: `x(1)` is independent of the codewords not reading it, and each reading
    codeword carries at most `H(psi)` (`bernoulli-witness-information-is-bounded-by-code-reads`).
  - The codeword Følner count gives `Phi >= log q / λ(F)` with `λ(F) = inf_S |SF|/|S|`
    (`bernoulli-window-codeword-folner-ratio-bound`).
  - Shearer-type counting over an arbitrary finite set `S` of sites reproduces exactly the Følner bound: every site in `S`
    is determined by `y_(SF)`, whose entropy is at most `|SF| H(psi)`.
  - None of these is uniform over configurations on a nonamenable host.
- **Remark R (small windows already see every presentation).** Windows with `|E| = 2`, or two codewords, have
  incidence patterns realized in abelian groups, so they carry no deficit
  (`bernoulli-deficit-windows-need-a-non-maximal-difference-subgroup`). But `|E| = 3` already sees every 2-generator group.
  - **Setup.** Let `H = <s, t>`, `E = {1, s, t}`, and `F = B_R(H)`. Suppose an exact realization of the pattern in a group
    `K` is given, by `α : F -> K`, `β : E -> K` and `γ` injective on points with `α(f)β(e) = γ(fe)`.
  - **The map.** Put `ι = γ|_(B_R)`, `s' = β(1)^-1 β(s)` and `t' = β(1)^-1 β(t)`. Then `ι(fs) = γ(f)s'` and
    `ι(ft) = γ(f)t'` whenever the points lie in `B_R`.
  - **Consequence.** Every relator of `H` of length at most `R` holds for `s', t'`, and `ι` is injective. So exact
    realizations of `|E| = 3` patterns are local embeddings of Cayley balls. No reduction of domination to finitely
    many small pattern types exists, because every countable group embeds in a 2-generator group. This is consistent
    with `self-copy-host-rokhlin-deficits-need-unbounded-windows`.
- **Where the attempt stops.** A floor on `U` must price codewords outside a region that carry information about it, and
  no finite count that ignores the pattern's global structure bounds that transport. Sofic counting is exactly such a
  global argument, and it is unavailable on `U`.

## 5. Exact gap: the three open statements outside the toolkit

Each would give a Rokhlin lower bound that Theorem K does not already cover.
- **(M1) `seward-direct-product-relative-rokhlin-entropy-conjecture`, for `Y = Ω/N`.** Over a finitely presented sofic `Q`
  with a non-virtually-split central class, `h_Q(Ω/N × L^Q | B(Ω/N)) = H(L)` would make the extension maximal by case
  (iii) (`deligne-triple-cover-surjunctive` for `Q = Sp_4(Z)`). The landed barriers do not touch it: Theorem G and (O6)
  concern weak containment only.
  - **Obstacle.** Every known relative lower bound over a base with no finite models is (I6), which needs weak
    containment.
  - **Sketch, not proved here.** A sofic-model lower bound needs microstates of `Ω/N`. Microstates of a liftable action
    carry the extension cocycle and give permutation models of the extension on `N × V_n`, by the argument of Theorem T.
    So finite models reproduce soficity again.
- **(M2) `rokhlin-window-transport-is-dominated` on a nonsofic canonical host.** This is a finitary information
  inequality that must use associativity (`cancellative-incidence-patterns-do-not-force-domination`).
- **(M3) `rokhlin-maximality-ascends-amenable-normal-extensions`.** It reaches the Kun–Thom wreath. One ascent step from
  a sofic quotient never produces a group containing an infinite simple nonsofic subgroup `S`: `S` would meet the
  amenable kernel trivially and embed in the sofic quotient.

**Single statement that decides the route.** `tester-host-has-positive-rokhlin-entropy-action`. A proof must exhibit a
Rokhlin lower bound over `U` by a mechanism that is neither sofic counting nor weak containment. None is known.

## 6. Model tests for Theorem K

- **Hypothesis side.** Each operation is used with its landed maximality node. Weak containment in (O6) is consumed by
  Theorem T. Case (iii) of the finite-kernel ascent drops it and is not an operation.
- **Conclusion side.**
  - `R` contains the Gohla–Thom lattice `Γ` but not `Γ~` whenever `Γ~` is nonsofic. This is consistent with
    `gohla-thom-lattices-no-weakly-bernoulli-liftable-action`, which excludes (O6) there.
  - It contains `E_3` exactly when `E_3` is sofic.
- **Trivial model.** If every group were sofic, Theorem K would say nothing, and neither would the route. The existence
  of nonsofic groups is what makes the barrier bite.
