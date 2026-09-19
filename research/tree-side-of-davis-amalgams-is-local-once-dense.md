---
rg: 2
id: tree-side-of-davis-amalgams-is-local-once-dense
kind: claim
title: For an amalgam Λ = W_1 *_A W_2 of Davis lattices whose X-projection has closure containing U^+, the tree projection is automatically non-discrete and faithful, so boundary-2-transitivity of the tree closure reduces to the two finite permutation groups W_i ↷ W_i/A (containing Alt(c_i)); with the all-vertex density certificate, Kourovka 21.46 on this route is a finite verification for one explicit twist
---

**ESTABLISHED** (lane proof, not reviewed) for items 1–2. Item 3 rests on Burger–Mozes Props. 3.3.1–3.3.2
as quoted by Radu (arXiv:1712.01091 l.2271) for regular trees; the biregular case is not checked.
Item 4 records what the explicit check needs.

## Statement

Let `W_1, W_2 ≤ U(Alt_{2d-1})` be Davis lattices on `X = X_{O_d}` (`d >= 6`), with `A = W_1 ∩ W_2` of
index `c_i` in `W_i`. Let `Λ = W_1 *_A W_2` act on `T × X`, where `T` is its biregular `(c_1,c_2)`
Bass–Serre tree. Assume **(N1)**: the closure of `⟨W_1, W_2⟩` contains `U^+`, which holds under the
all-vertex certificate (3∀) of `al-local-to-global-holds-without-vertex-transitivity`.

1. **Faithful and non-discrete on the tree.** `Λ` acts faithfully on `T`, and `pr_T(Λ)` is non-discrete.
2. **Local actions.** Let `H_T` be the closure of `pr_T(Λ)`. At a vertex of type `i`, its local action
   is the finite permutation group `P_i := image of W_i in Sym(W_i/A)`.
3. **Boundary-2-transitivity from finite data.** If `P_i ⊇ Alt(c_i)` with `c_i >= 6` for `i = 1, 2`,
   then `H_T` is 2-transitive on `∂T`. Via Burger–Mozes Props. 3.3.1–3.3.2, this is the same deduction
   Radu makes for `(d_1,d_2)`-groups.
   - Then (N1)–(N2) of `kourovka-21-46-reduces-to-simple-amalgams-of-davis-lattices` hold.
   - `Λ` is virtually simple as soon as it is non-residually finite, which the hyperplane sub-amalgam
     provides.
4. **What one explicit instance needs.** Everything is now a finite check.
   - **Input.** A torsion-free, edge-transitive, non-residually-finite lattice on `T' × T_6` with
     explicit squares. Radu's virtually simple `(6,6)`-groups `Γ_{6,6,k}` have torsion but are explicit:
     their squares are Γ_{4,4}'s four plus Tables simple1–5.
     - Their type-preserving index-4 subgroups `Γ^+` are torsion-free by Radu's lemma (l.411): a
       type-preserving group acting freely on vertices is torsion-free.
     - `Γ^+` is edge-transitive on `T_1`, since `Γ^+_v` has local action `⊇ Alt(6)`. It is simple for most
       `k`, since `|Q| = 4`.
     - So `Γ^+ = F_a *_{F_e} F_b` is an explicit input with `d = 6`. By
       `bm-lattices-have-color-preserving-edge-groups`, at most one more index-2 passage makes `F_e`
       color-preserving.
   - **Twist.** A wall twist `φ_ε` whose values move `D` (item 4 of `twisted-davis-amalgams-keep-hyperplane-data`).
   - **Certificates.**
     - (3∀): witnesses in `G_v` whose local actions generate `Alt_11` at each orbit representative, plus
       one element fixing `B_1(v)` that acts nontrivially on some `B_1(w)`, by the all-vertex form of AL's
       Prop. "local action options".
     - `P_1, P_2 ⊇ Alt(c_i)`.
   - **Parity.** All local actions of `E(F_a)`, `E(F_b)` and `φ_ε` must be even, to stay in `U(Alt)`.
     Otherwise one needs AL's theorem for `U(Sym)`.

## Proof

1. **Faithful and non-discrete.**
   - Faithfulness is item 1 of `twisted-davis-amalgams-keep-hyperplane-data`.
   - Suppose `pr_T(Λ)` were discrete. Then `pr_T(W_1) ⊆ pr_T(Λ)_v`, which is finite. So
     `W_1 ∩ ker pr_T` would have finite index in `W_1`.
   - But `Λ ∩ ker pr_T` is a normal subgroup acting trivially on `T`, so it is trivial by faithfulness.
     Then `W_1` is finite, a contradiction.
2. **Local actions.** `(H_T)_v` is the closure of `pr_T(Λ_v)`, since an element of `pr_T(Λ)` close to
   `(H_T)_v` fixes `v`. Here `Λ_v` is a conjugate of `W_i`, and the link of `v` is `W_i/A`.
3. **Boundary-2-transitivity.** Burger–Mozes show that a closed non-discrete subgroup of `Aut(T)` whose
   local actions contain `Alt(c) ≥ Alt(6)` (2-transitive, with nonabelian simple point stabilizers) is
   locally ∞-transitive. By BM Lemma 3.1.1 it is then boundary-2-transitive. This is the route Radu
   (l.2271) and AL (l.2362, via BM Lemma 3.5.3) take.
   - The rest follows from item 4 of the reduction node, Bader–Shalom, and Radu's NST corollary
     (l.2128–2138).

## Status of the approved MSI check

It was **not run** this round, deliberately.
- **The input is not wired.** No explicit torsion-free non-residually-finite input with `d >= 6` exists
  in machine-readable form: Radu does not print his torsion-free `(6,8)` and `(8,6)` groups. The
  `Γ_{6,6,k}^+` input above must first be parsed from Radu's tables. After that, three more pieces are
  needed:
  - the 6-edge-coloring of `F_e\T_6` (König);
  - the section `E`;
  - the wall-twist fields on `X_{O_6}` (462 generators).
- **The calibration case is not wired.** The positive control (an untwisted AL lattice, dense by AL's
  theorem) needs AL's §5.3 interlacing construction from an involutive alternating seed.
- **Signal would be poor.** A single blind run, with no local testing, is more likely to report a bug
  than a fact.
- **Plan.** Next round: code and parse locally with no execution, then one job that does all of:
  - (i) validates the `Γ_{6,6,k}^+` datum against Radu's printed invariants (corner condition,
    `|Q| = 4`);
  - (ii) calibrates the certificate search on the untwisted split amalgam, a negative control whose
    local actions must stay in `Sym(D^c)`;
  - (iii) runs the twisted certificate.

## Lesson for general BH

- **Density propagates across factors.** For lattice amalgams in products, density in one factor gives
  faithfulness and non-discreteness in the other. After that, the second factor asks only for finite
  permutation data, the local actions `W_i ↷ W_i/A`.
- **Whole programs collapse to finite checks.** Simplicity of such a host then reduces to three finite
  certificates: X-side local density, tree-side local 2-transitivity, and one non-residually-finite
  input. This is the right shape for a formal (and eventually Lean) proof: each piece is a finite
  computation or a cited theorem.
