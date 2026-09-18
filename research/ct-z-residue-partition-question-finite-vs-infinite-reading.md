---
rg: 2
id: ct-z-residue-partition-question-finite-vs-infinite-reading
kind: claim
title: "Kourovka 21.74(a): every instance of our (b), (c) and 21.73 reductions is a yes-instance; the two-transposition element τ_{1(2),0(4)}τ_{0(2),1(2)} is a no-instance for finite and infinite partitions; Kohl's mixer ψ is a no-instance only for finite partitions, since it permutes an infinite partition into residue classes"
requires:
  - ct-z-invariant-residue-partitions-are-not-conjugacy-invariant
  - ct-z-residue-partitions-cannot-carve-thin-invariant-sets
  - ct-z-north-south-element-has-no-finite-cycles
  - ct-z-finite-cycle-problems-are-undecidable
  - ct-z-conjugacy-problem-is-undecidable
---

**ESTABLISHED** (lane proof, not reviewed). Elementary and self-contained. No priority is claimed.
**Kourovka 21.74(a) itself remains OPEN** under its intended (finite) reading. This node gives four
facts that fix what any solution has to do.

## Source

Kourovka Notebook, arXiv:1401.0300v46 (1 Sep 2026), Problem 21.74 (S. Kohl). The text below was
checked verbatim by the referee of `ct-z-finite-cycle-problems-are-undecidable` (fac0259d6b):
"Is it algorithmically decidable whether a given element `g ∈ CT(Z)` (a) permutes a nontrivial
partition of `Z` into residue classes? (b) has only finite cycles? (c) has no finite cycles?"
It is unmarked, i.e. unsolved in that issue. Parts (b) and (c) are answered negatively on main
(referee PASS, conditional on the published theorems of Kari–Ollinger).

**Two readings.** The printed text does not say "finitely many". Kohl's own rcwa usage
(RCWA manual: `RespectedPartition`, "tame") always means a partition into *finitely many* residue
classes. Call that the **finite reading**, and the one allowing countably many classes the
**infinite reading**. Both earlier nodes on (a) use the finite reading, and so should item 2 of
`ct-z-north-south-element-has-no-finite-cycles` (Theorem 3 below shows it is false otherwise).

**Literature** (searched 2026-09-18: class transposition with decidable/undecidable, "residue class
partition", "21.74"; plus the referee's search). No paper treats 21.74(a). The RCWA package
decides membership only for tame groups and tests tameness by sufficient criteria. It has no
procedure for (a).

## Conventions

As in `ct-z-invariant-residue-partitions-are-not-conjugacy-invariant`: `τ_{A,B}` is the class
transposition `r_1 + m_1 t ↔ r_2 + m_2 t`, and products act right to left. `g` is **YES**
(respectively **YES∞**) if it permutes a partition of `Z` into at least two residue classes, finitely
many (respectively countably many). YES implies YES∞. A class is an infinite progression `r(m)`,
`m ≥ 1`. An injective affine integer map sends a class onto a class. If `g` permutes `𝒫` and
`g(n) = n`, then `g` maps the part containing `n` onto itself.

## Statement

**Theorem 1 (support lemma; the reductions are blind to (a)).**
1. Let `m ≥ 2`, and suppose `g(C) = C` for every class `C` mod `m` except possibly one. Then `g` is
   YES. In particular, `g` is YES whenever the points it moves lie in one proper class.
2. Every element produced by the reductions on main is YES, uniformly in the machine `M`, via the
   partition `{0(7), 1(7), …, 6(7)}`, each part fixed. That covers `F_M` and `H_M`
   (`ct-z-finite-cycle-problems-are-undecidable`, 21.74(b),(c)) and `A_M` and `B_M`
   (`ct-z-conjugacy-problem-is-undecidable`, 21.73).

**Theorem 2 (a two-transposition no-instance).** Let `g_0 = τ_{1(2),0(4)} τ_{0(2),1(2)}`. Then

    g_0(n) = 2n          if n ≡ 0 (mod 2),
    g_0(n) = (n + 1)/2   if n ≡ 1 (mod 4),
    g_0(n) = n − 1       if n ≡ 3 (mod 4),

and `g_0` is neither YES nor YES∞. The obstruction is the fixed point `0`, where the local slope is `2`.

**Theorem 3 (ψ is YES∞).** Let `ψ` be the five-transposition element of
`ct-z-north-south-element-has-no-finite-cycles`, which is not YES by that node's item 2 and
Theorem 4 of `ct-z-invariant-residue-partitions-are-not-conjugacy-invariant`. Then `ψ` permutes the
infinite partition

    𝒫_ψ = { ψ^j(2(16)), ψ^j(6(16)), ψ^j(14(16)) : j ∈ Z }

of `Z` into residue classes. So the finite and infinite readings of (a) differ on explicit
elements.

**Theorem 4 (dissipative elements are YES∞).** Suppose `g ∈ CT(Z)` and classes `A`, `R` satisfy:
- **(A1)** `g` is affine on `A` and `g(A) ⊊ A`; `g^{-1}` is affine on `R` and `g^{-1}(R) ⊊ R`;
- **(A2)** every `g`-orbit in `Z` meets `A`, and `⋂_{j≥0} g^j(A)` contains no integer;
- **(A3)** with `D = A ∖ g(A)`, the backward `ĝ`-orbit of every point of the closure `D̂ ⊆ Ẑ`
  meets `R̂`.

Then `g` is YES∞. Theorem 3 is the case `g = ψ`, `A = 2(4)`, `R = 1(4)`.

**Remark (tame versus YES).** Every tame element, in Kohl's sense, is YES: if its respected
partition has one part, `g(n) = ±n + b` permutes `{0(2), 1(2)}`. The converse fails.
`h = ψ_{0(2)} ψ_{1(2)}` is YES (it fixes both parity classes) but wild: a power `h^N` of a tame
element is a translation on each part of a respected partition, so its orbits grow at most linearly,
whereas `h` has orbits growing like `4^k`: on `0(2)` it is `2ψ(·/2)`, and `ψ(n) = 4n + 2` on `2(4)`.
So (a) lies strictly between tameness and the conjugacy-invariant condition
(Theorem 3 of `ct-z-invariant-residue-partitions-are-not-conjugacy-invariant`).

## Proofs

**Theorem 1.**
1. Let `r(m)` be the exceptional class. Since `g` is a bijection fixing the union of the other
   classes mod `m` setwise, it fixes `r(m)` as well. So `g` permutes (fixes) the `m ≥ 2` classes mod `m`.
   If the moved points lie in `r(m)`, every other class mod `m` is fixed pointwise.
2. In both reduction nodes, `X` consists of odd `n` with `1 ≤ v_7(n) ≤ N`, so `X ∪ 2X ⊆ 0(7)`.
   - `F_M = s_2 s_1` and `A_M` move only points of `X ∪ 2X`. `B_M = T_*^{(2X)} A_M T_*` does too,
     since `T_*` acts on codes and `T_*^{(2X)}` on their doubles. Apply 1 with `m = 7`.
   - `H_M = (∏_j ψ_j) F_M`, where `ψ_j` moves only points of its class `j(L′) ⊆ Y = Z ∖ (X ∪ 2X)`
     and `7 | L′`. For `i ≢ 0 (mod 7)`, `i(7)` misses `X ∪ 2X`. So it is the union of the classes
     `j(L′) ⊆ Y` with `j ≡ i (mod 7)`, each preserved by `H_M`. Apply 1 with `m = 7`. ∎

**Theorem 2.** Put `a = τ_{0(2),1(2)}` (`n ↦ n + 1` on evens, `n ↦ n − 1` on odds) and
`b = τ_{1(2),0(4)}` (`1 + 2t ↔ 4t`). Then `g_0 = b ∘ a`.
- **The formula.**
  - For `n` even, `a(n) = n + 1 = 1 + 2(n/2)`, so `b` gives `4(n/2) = 2n`.
  - For `n ≡ 1 (mod 4)`, `a(n) = n − 1 = 4t` with `t = (n − 1)/4`, so `b` gives `1 + 2t = (n + 1)/2`.
  - For `n ≡ 3 (mod 4)`, `a(n) = n − 1 ∈ 2(4)`, which `b` fixes.
- **No partition.** Let `g_0` permute a partition `𝒫` of `Z` into residue classes, of any
  cardinality. Since `g_0(0) = 0`, the part `C ∋ 0` satisfies `g_0(C) = C`, and `C = mZ`.
  - If `m` is even, then `C ⊆ 0(2)`, and `g_0(C) = 2mZ ≠ mZ`.
  - If `m ≥ 3` is odd, choose `n ≡ 0 (mod m)` with `n ≡ 3 (mod 4)` (CRT). Then
    `g_0(n) = n − 1 ≡ −1 (mod m)`, so `g_0(n) ∉ C`.
  - Hence `m = 1`, `C = Z`, and `𝒫` is trivial. ∎

Two is the minimum. A single class transposition has order 2, and elements of finite order are YES
(Theorem 2 of `ct-z-invariant-residue-partitions-are-not-conjugacy-invariant`).

**Theorem 4.** Write `D` for `A ∖ g(A)`. It is a nonempty finite union of classes by (A1).
- **Step 1: `D` is a fundamental domain.**
  - Since `g(A) ⊆ A`, the set of `j` with `g^j(x) ∈ A` is upward closed, and it is nonempty by (A2).
  - It is bounded below: if `g^j(x) ∈ A` for all `j ≤ j_0`, then `g^{j_0}(x) ∈ ⋂_{k≥0} g^k(A)`,
    which contradicts (A2).
  - At the least such `j`, the point `g^j(x)` lies in `D`. So every orbit meets `D`.
  - It meets `D` only once: if `g^j(x), g^{j′}(x) ∈ D` with `j < j′`, then
    `g^{j′}(x) ∈ g^{j′−j}(A) ⊆ g(A)`, which is disjoint from `D`.
  - Hence `Z = ⊔_{k∈Z} g^k(D)`.
- **Step 2: bounded transit.**
  - The sets `U_k = {z ∈ D̂ : ĝ^{-k}(z) ∈ R̂}` are clopen.
  - They increase with `k`, since `ĝ^{-1}(R̂) ⊆ R̂`.
  - By (A3) they cover the compact `D̂`, so `U_J = D̂` for some `J`.
- **Step 3: affine pieces.**
  - Refine `D` into finitely many classes `D_i` on each of which `g^{-1}, …, g^{-J}` are affine.
  - For `k ≥ 0`, `g^k` is affine on `D_i ⊆ A` by (A1).
  - For `k ≥ J`, `g^{-J}(D_i) ⊆ R ∩ Z = R`, where `g^{-1}` is affine and maps `R` into `R`. So
    `g^{-k}` is affine on `D_i`.
  - So every `g^k(D_i)`, `k ∈ Z`, is a class.
- **Conclusion.** By Step 1 these classes partition `Z`, and `g` maps `g^k(D_i)` onto `g^{k+1}(D_i)`.
  The parts are infinitely many because `D ≠ ∅`. ∎

**Theorem 3 (checking (A1)–(A3) for ψ).** Recall `ψ(n) = 4n + 2` for `n ≢ 1 (mod 4)`,
`ψ(n) = n − 3` for `n ≡ 9 (mod 16)`, and `ψ(n) = (n − 1)/4` for `n ≡ 1, 5, 13 (mod 16)`.
- **(A1).**
  - `ψ = 4n + 2` on `A = 2(4)`, and `ψ(A) = 10(16) ⊊ A`.
  - `ψ^{-1}(x) = 4x + 1` on `R = 1(4)`: for `x ∈ 1(4)`, `4x + 1 ∈ 5(16)` and `ψ(4x + 1) = x`.
    Also `ψ^{-1}(R) = 5(16) ⊊ R`.
- **(A2).**
  - **Every orbit meets `A`.** For `n ∈ 0(4) ∪ 3(4)`, `ψ(n) = 4n + 2 ∈ A`. For `n ∈ 9(16)`,
    `ψ(n) ∈ 6(16) ⊆ A`. On `1, 5, 13 (mod 16)`, the step `(n − 1)/4` strictly lowers `|n|` for
    `n ≠ 0`, so these cases end in one of the others.
  - **The intersection has no integer.** If `n ∈ ψ^j(A)` for all `j ≥ 0`, the backward orbit stays
    in `ψ(A) = 10(16)`, where `ψ^{-1}(x) = (x − 2)/4` strictly lowers `|x| ≥ 2`. That is impossible.
- **(A3).** `D = 2(16) ∪ 6(16) ∪ 14(16)`. On boxes of `Ẑ`:
  - `ψ̂^{-1}` maps `2(16)` onto `0(4)` and `14(16)` onto `3(4)` by `(x − 2)/4`, and `6(16)` onto
    `9(16) ⊆ R` by `x + 3`;
  - `ψ̂^{-1} = 4x + 1` maps `0(4)` and `3(4)` into `1(16)` and `13(16)`, both inside `R`.

  So `J = 2`, with each `D_i ∈ {2(16), 6(16), 14(16)}` already carrying affine `ψ^{-1}` and `ψ^{-2}`.
  This gives `𝒫_ψ`. ∎

## What this says about 21.74(a)

**What the (b), (c) and 21.73 methods fail to give.**
- By Theorem 1 their instances are YES for a trivial reason that does not depend on `M`. The
  machine lives inside the proper class `0(7)`, and everything else is fixed or mixed class by class.
- Coupling the machine to one global mixer does not help. By
  `ct-z-residue-partitions-cannot-carve-thin-invariant-sets`, valuation-coded Σ₁ events create only
  invariant sets inside some `pZ`, and those never contain a co-class.
- YES is r.e. (Theorem 1 of `ct-z-invariant-residue-partitions-are-not-conjugacy-invariant`),
  so an undecidability proof must send halting to YES: a finite event must *create* a permuted
  partition. The Σ₁ events of valuation codings (halting, a periodic configuration) are thin. The
  one thick event they offer is finite order, and finite order of `F_M` is decidable (Kari–Ollinger
  Thm 4).

**Where the finite reading is sensitive.** Theorems 2–4 locate the obstructions.
- Under the infinite reading, dissipative dynamics imposes nothing (Theorem 4). The obstruction
  sits at recurrent integers whose germ is not a translation (`g_0`: a fixed point of slope 2).
- Under the finite reading there is one more source: recurrent points of `ĝ` in `Ẑ ∖ Z`. For `ψ`
  this is the attracting 2-adic fixed point `−2/3`, whose basin fills `Z_2` (Theorem 4 of
  `ct-z-invariant-residue-partitions-are-not-conjugacy-invariant`). Finite partitions are clopen in
  `Ẑ`, so they see `ĝ` on the compact space. Infinite partitions see only the orbits of integers.
- So a decision procedure must certify NO from the non-wandering set of `ĝ` on `Ẑ` (attractors,
  their basins, and the translation parts `F_Q^{-1}F_P` between pieces).
- The cycle type on `Z` does not decide (a). `ψ` and `h = ψ_{0(2)} ψ_{1(2)}` both consist of countably
  many infinite cycles, so they are conjugate in `Sym(Z)`, yet `h` is YES and `ψ` is NO.

**Exact missing step for undecidability (route, not claimed).**
- Code by **digits** over at least two primes, not by valuations, so that configuration sets are
  unions of boxes that can be thick.
- Reduce from a reversible model in which periodicity is Σ₁ and undecidable, and in which
  periodicity forces uniform periodicity. Then periodic ⇒ finite order ⇒ YES, for free. For
  counter machines this fails: periodicity and uniform periodicity differ for 2-RCMs, because the
  first is undecidable and the second is decidable (Kari–Ollinger Thms 3, 4). Reversible Turing
  machines are the natural candidate; that needs checking at source.
- **The missing lemma: non-periodic ⇒ NO.** This is a Theorem-4-type certificate, meaning an attractor
  in one coordinate whose basin is in no proper ball, plus a translation in the transverse
  coordinate. It has to hold uniformly for every non-periodic machine, and no argument for it is
  known here.
- A sufficient target: a machine family whose non-periodic members give clopen-indecomposable `ĝ`.
  YES implies that some power of `ĝ` fixes a proper clopen set, so indecomposable means NO. This is
  stronger than needed.

**Exact missing step for decidability.** A Σ₁ NO-certificate for arbitrary `g`. Two such
certificates exist: the fixed-point certificate (Theorem 2) and the autonomous-2-adic
attractor-plus-translation certificate (Theorem 4 of
`ct-z-invariant-residue-partitions-are-not-conjugacy-invariant`). The multi-prime case, where the
2-adic coordinate is not autonomous, has none.

## Lesson for general BH

**Finite coordinates see compact recurrence; infinite coordinates see only germs.**
- A dissipative element of a Cantor-type host is coordinate-free in the countable sense. It
  permutes a partition into standard pieces (boxes, cones), built from a fundamental domain and
  bounded transit to its repeller (Theorem 4).
- Box-level rigidity is forced only at recurrent points. At integer points it comes from germs
  with non-trivial slope; in the finite reading it also comes from attractors at infinity (`Ẑ ∖ Z`).
- This matches the v5 picture that hard inputs sit at an infinite emitter. Constraints that finite
  (compact) structure imposes live at the non-wandering set, and at its germs.
- **For stabilizer and permutational constructions:** on wandering sets one may always choose
  countable box-adapted structures; all the cost sits at the recurrent points and their germs.
  Design hosts so that the input's hard part is carried by germs at recurrent points, and let
  the dissipative remainder be free.
