---
title: UCT problem through cyclic actions on O_2 - Rokhlin ascent reformulation and a source audit of Barlak--Li II (uct-o2-cyclic-actions lane, 2026-09-12)
---

# Scope

Lane `uct-o2-cyclic-actions` on `nuclear-algebra-without-uct-exists` (STW
Problem II). Its predecessor `uct-nuclear-proper-isometry` refuted the MF-tensor
route (43a6971d4).

The Barlak--Szabó / Barlak--Li reduction to cyclic actions on `O_2` was already
on main before this lane started:
- `barlak-li-p-half-iff-zp-actions-fix-cartan`;
- `o2-zp-cartan-fixing-all-primes-or-at-most-one`;
- the route `stw99-ii-via-o2-cartan-invariant-actions`.

This lane therefore did not re-land the reduction. It added:
- the dual (Rokhlin) form of each prime half;
- an audit of the one step in Barlak--Li II whose justification is not visible
  in the source.

# 1. Source read

Barlak--Li, *Cartan subalgebras and the UCT problem, II*, arXiv:1704.04939v2,
extracted on MSI with ghostscript `txtwrite` on 2026-09-12. Statements below are
paraphrased closely from the extracted text; numbers are the source's.

* **Definition 2.6** (after Izumi, Definition 3.1). An action `α : Γ ↷ A` of a
  finite group on a separable C\*-algebra has the Rokhlin property if there is a
  unital equivariant \*-homomorphism `(C(Γ), σ) → (F_∞(A), α_∞)`, where `σ` is
  the translation action.
* **Definition 2.7** (after Izumi, Definition 3.6). For `Γ` finite abelian, `α`
  is approximately representable if there is a unitary representation
  `u : Γ → F_∞(A^α) ⊆ F_∞(A^α, A)` with `α_γ(a) = u_γ a u_γ*` for all `a ∈ A`.
* **Theorem 2.8** (their [14, Lemma 3.8] and [32, Proposition 4.4]). For `Γ`
  finite abelian and `A` separable:
  - `α` has the Rokhlin property iff `α̂` is approximately representable;
  - `α` is approximately representable iff `α̂` has the Rokhlin property.
* **Theorem 4.12.** Let `A` be a unital UCT Kirchberg algebra, `n ≥ 2`, and
  `α : Z_n ↷ A` outer and approximately representable, with `A ⋊_α Z_n`
  absorbing `M_(n^∞)`. Then `A ⋊_α Z_n` satisfies the UCT iff there is an
  `α`-homogeneous inverse semigroup model iff some Cartan subalgebra `C ⊆ A` has
  `α(C) = C`. The proof derives simplicity and pure infiniteness of the crossed
  product from outerness ([24, Theorem 3.1], [16, Theorem 3]), and uses the
  Rokhlin dual action.
* **Definition 4.13** (Izumi, Definition 3.6). For unital `A`, `α` is strongly
  approximately inner if `α = lim_n Ad(u_n)` pointwise in norm, with unitaries
  `u_n ∈ A^α`.
* **Remark 4.14.**
  1. Absorption of `M_(n^∞)` by `A ⋊_α Z_n` is equivalent to `α` being conjugate
     to `α ⊗ id` on `A ⊗ M_(n^∞)`. For outer strongly approximately inner `α` on
     a unital UCT Kirchberg algebra, `α ⊗ id` is outer and approximately
     representable ([14, Lemma 3.10]).
  2. "To the best of the authors' knowledge, it is not known whether all
     `Z_2`-actions on `O_2` are strongly approximately inner."
* **Corollary 4.15, proof.**
  - Pimsner--Voiculescu makes `K_*(O_2 ⋊_α Z_q)` uniquely `p`-divisible and in
    Cuntz standard form ([14, Lemma 4.4]).
  - "Therefore `O_2 ⋊_α Z_q` absorbs `M_(p^∞)` tensorially by the
    Kirchberg--Phillips classification theorem."
  - `α` is approximately representable by [14, Theorem 4.6].
  - Theorem 4.12 then applies.
* **Theorem 4.16, proof of (i) ⟹ (ii).** "Then `O_2 ⋊_α Z_p` is a unital,
  `M_(p^∞)`-absorbing Kirchberg algebra. By assumption, `O_2 ⋊_α Z_p` satisfies
  the UCT. Claim (ii) now follows from Corollary 4.15."
* **Theorem 4.16, proof of (iii) ⟹ (i).** `α := id_(A') ⊗ γ` with `γ` from
  Barlak--Szabó Proposition 4.14. It fixes a Cartan subalgebra by assumption, so
  `O_2 ⋊_α Z_p` satisfies the UCT ([1, Proposition 3.4]), and hence so does `A`.

# 2. The Rokhlin ascent reformulation (landed)

For a prime `p`:
- `D_p`: every outer, strongly approximately inner `Z_p`-action on `O_2` fixes a
  Cartan subalgebra;
- `Asc_p`: every unital Kirchberg algebra `B` with a Rokhlin action
  `δ : Z_p ↷ B` and `B ⋊_δ Z_p ≅ O_2` satisfies the UCT.

`D_p ⟺ Asc_p` is landed as `o2-zp-cartan-fixing-iff-rokhlin-uct-ascent`, with
its `-proof` route. It uses only Corollary 4.15 in both directions, together
with Theorem 2.8 and Takai duality:
- **forward:** take the dual of the approximately representable `α`;
- **backward:** check that the dual of a Rokhlin action is outer and strongly
  approximately inner, then transport the UCT from `B ⊗ M_p` to `B`.

The literature facts it consumes are landed as
`izumi-rokhlin-approximately-representable-duality` with a `-citation` route.

**What it adds:** the counterexample shape on the dual side. A non-UCT unital
Kirchberg algebra `B` carrying a Rokhlin `Z_p`-action with crossed product `O_2`
is a witness at `p`, and every witness at `p` has this form. Nothing here proves
either side.

# 3. Audit note: `M_(p^∞)`-absorption in Theorem 4.16, (i) ⟹ (ii)

**The step.** To apply hypothesis (i), the proof needs `O_2 ⋊_α Z_p` to be
KK-equivalent to its `M_(p^∞)`-stabilization *before* the UCT is known. The
source asserts absorption with no argument at that point. The only absorption
argument visible in the paper is the one in Corollary 4.15: unique
`p`-divisibility of K-theory, plus Kirchberg--Phillips. That deduction runs
through the UCT: for a non-UCT Kirchberg algebra, K-theory does not determine
KK-equivalence.

**Whether it is a gap.** A UCT-free argument may exist in Izumi I ([14],
Theorem 4.6 or its classification of strongly approximately inner actions on
`O_2`), or through Remark 4.14(1). This lane could not read Izumi I: the arXiv
PDF fetched as `math/0201143` was an unrelated paper, and MSI connectivity
dropped repeatedly. **Status: UNVERIFIED, not a confirmed gap.**

**What on main uses that direction.** The graph consumes the prime-half node
`barlak-li-p-half-iff-zp-actions-fix-cartan` in these ways:
- `o2-zp-cartan-fixing-all-primes-or-at-most-one`: items 1 (forward) and 3 use
  (iii) ⟹ (i), whose proof is complete in the source. Items 1 (backward) and 2
  apply Corollary 4.15 only once every separable nuclear algebra satisfies the
  UCT, so absorption is not needed.
- `bootstrap-class-zp-actions-on-o2-fix-a-cartan`: applies Corollary 4.15
  (i) ⟹ (iii) with the UCT already known.
- `uct-three-half-via-z3-actions-on-o2`: uses (iii) ⟹ (i) at `p = 3`.
- `o2-zp-cartan-fixing-iff-rokhlin-uct-ascent` (this lane): uses only
  Corollary 4.15.

A `git grep` of `requires:` lines on main at b3ef22443 finds no other consumer.
So no route on main uses the unverified direction.

**If absorption fails without the UCT.** The robust form of (i) ⟹ (iii)
replaces `α` by `α ⊗ id_(M_(p^∞))`.

# 4. Not landed: Rokhlin descent of the UCT

**Planned derivation.** For a Rokhlin action of a finite group on a separable,
unital, simple, nuclear UCT algebra, the fixed-point algebra and the crossed
product satisfy the UCT. Proof sketch:
1. Take exact equivariant Rokhlin towers in `A` (lifting from `F_∞(A)`), using
   equivariant semiprojectivity of `(C(G), σ)`; see Phillips, arXiv:1112.4584.
2. The map `y ↦ Σ_g α_g(y)` embeds the corner `p_1 A p_1` into `A^α` and
   approximates finite subsets.
3. Apply Dadarlat's local UCT theorem.
4. Use Morita equivalence of `A^α` with `A ⋊ G`.

**Why it is not landed.** The two inputs (the exact hypotheses of Dadarlat's
local UCT, and the finite-group case of equivariant semiprojectivity) were not
read from their sources this session.

**What it would add.** For Rokhlin actions the UCT passes down, and `Asc_p` asks
whether it passes up. Nothing more is claimed.

# 5. Assessment

Neither side of Problem II moved. Each prime half is now stated three ways:
- UCT for `M_(p^∞)`-stable algebras;
- Cartan-fixing for order-`p` automorphisms of `O_2`;
- UCT ascent along Rokhlin actions with crossed product `O_2`.

Every attack tried so far stops at the same coherence step. Approximate
representability supplies approximately central implementing unitaries, but a
subalgebra approximation of the crossed product needs them to generate genuine
subalgebras. Dadarlat's local UCT accepts subalgebras, not approximately
multiplicative maps.
