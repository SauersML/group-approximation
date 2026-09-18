---
rg: 2
id: fully-self-replicating-fp-infinity-groups-are-acyclic
kind: claim
title: A group isomorphic to its own permutational wreath product R wr_X P has H_*(R;k) = (H_*(R;k)^(tensor X))_P, so with root image in Alt(X) every class in degree a forces infinite-dimensional H_((d-1)a); an FP_infinity fully self-replicating group is Z[1/|P|]-acyclic and a finitely presented one has b_1 at most 1
artifacts:
  - experiments/self-replicating-homology-2026-09-17/verify_wreath_coinvariants.py
  - experiments/self-replicating-homology-2026-09-17/verify_wreath_coinvariants.out
distinct_from:
  fully-self-replicating-tree-groups-give-fg-tits-hosts: that builds the simple Tits-(P) host from a fully self-replicating R and reduces its finite presentation to that of R; this proves homological necessary conditions on R itself, which any finitely presented or FP_infinity host of that shape must meet.
  tits-independence-vertex-groups-are-branch-type: that shows vertex groups of (P)-hosts are branch-type; this constrains the homology of the self-replicating groups that such branch-type vertex groups are built from.
  self-similar-spinal-groups-not-fp-torsion-quotients: that is about finitely presented torsion covers of spinal groups; this is a Kunneth-coinvariant argument that uses only the abstract isomorphism R = R wr_X P and applies to non-contracting groups.
---

**ESTABLISHED (unreviewed).** Proof: `fully-self-replicating-fp-infinity-groups-are-acyclic-proof`.
The coinvariant count is checked by brute-force linear algebra in the attached script.

**Setting.** `X` is a finite set with `d = |X| ≥ 2`, and `P ≤ Sym(X)` is transitive. `R`
is any group with an isomorphism `R ≅ R ≀_X P = R^X ⋊ P`, with `P` permuting the
coordinates. Every fully self-replicating `R ≤ Aut(X*)` with root image `P` (conditions
(S), (B), (A) of `fully-self-replicating-tree-groups-give-fg-tits-hosts`, with `A_d`
replaced by `P`) is such a group, through the section map. `k` is a field whose
characteristic does not divide `|P|`, and `h_n = dim_k H_n(R; k)`, a cardinal.

**Theorem.**

1. **Coinvariant identity.** As graded vector spaces,
   `H_*(R; k) ≅ (H_*(R; k)^{⊗X})_P`,
   where `P` permutes tensor factors with the Koszul sign. The right side is
   `k ⊕ H_{>0}(R; k) ⊕ E_*`. Here `E_n` has one basis vector for each `P`-orbit of basis
   tensors of degree `n` with at least two non-unit factors whose stabilizer acts on them
   by `+1`. So `h_n = h_n + dim E_n`, and **`E_n = 0` in every degree with `h_n < ∞`.**
2. **Excess classes.** Let `a, b ≥ 1`.
   - (i) Two distinct basis classes in degrees `a` and `b` give `E_{a+b} ≠ 0`.
   - (ii) If `a` is even and `h_a ≠ 0`, then `E_{2a} ≠ 0`.
   - (iii) Suppose some `S ⊆ X` with `|S| ≥ 2` has setwise stabilizer `P_S` acting on
     `S` by even permutations only. If `h_a ≠ 0`, then `E_{|S| a} ≠ 0`. When
     `P ≤ Alt(X)` and `d ≥ 3`, `S = X ∖ {x}` qualifies, so `E_{(d−1)a} ≠ 0`.
3. **Root image in `Alt(X)`, for instance `A_d` with `d ≥ 3`.** For every `a ≥ 1`,
   either `H_a(R; k) = 0` or `H_{(d−1)a}(R; k)` is infinite-dimensional. Hence:
   - (a) if `R` is of type `FP_{(d−1)a}` over `k`, then `H_j(R; k) = 0` for `1 ≤ j ≤ a`;
   - (b) if `R` is of type `FP_∞` over `k`, then `R` is `k`-acyclic;
   - (c) if `R` is of type `FP_∞` (over `Z`), then `H̃_*(R; Z[1/|P|]) = 0`: every reduced
     integral homology group of `R` is finite, with order divisible only by primes
     dividing `|P|`;
   - (d) if `R` is finitely presented and `d ≥ 4`, then `dim_k H_1(R; k) ≤ 1`. In
     particular `rank H_1(R; Z) ≤ 1`. If `d = 3`, then `H_1(R; k) = 0`. If `R` is of type
     `FP_{d−1}`, then `R^{ab}` is finite with order divisible only by primes dividing `|P|`.
4. **Arbitrary transitive `P`.** If `R` is of type `FP_∞` over `k`, then `H̃_*(R; k)` is
   `0` or is one-dimensional, concentrated in one odd degree. The second case needs
   every 2-subset of `X` to be swapped by some element of `P`, and no `S` as in (iii) to
   exist. It is consistent for `P = Sym(X)`, as the script confirms.

**What it says about the Tits route of `boone-higman-conjecture`.**
`fully-self-replicating-tree-groups-give-fg-tits-hosts` reduces a finitely presented
simple (P)-host of the form `(R ≀ A_{d+1}) *_{R×R} (R ≀ A_{d+1})` to a finitely presented
fully self-replicating `R` with root image `A_d`. Contracting `R` are excluded by
Bartholdi's theorem. This node excludes, whatever the contraction behaviour:

- every candidate `R` with `b_1(R) ≥ 2`, or with `dim H_1(R; F_p) ≥ 2` for a prime
  `p > d`, from being finitely presented;
- every candidate of type `FP_{d−1}` with infinite abelianization, or with a prime
  `p > d` dividing `|R^{ab}|`;
- every candidate of type `FP_∞` with nonzero reduced homology over `Q` or over `F_p`
  for any `p > d`.

A finitely presented `R` of type `FP_∞` must therefore be homologically invisible away
from the primes up to `d`, as Thompson's group `V` is. That points the construction
toward cloning-type groups and away from groups assembled from pieces with free abelian
homology, such as HNN extensions over infinite-order stable letters that survive in
`H_1`, or lattice-like groups.

**What it does not do.** It gives no contradiction for a finitely presented `R` with
`b_1 ≤ 1`, and none for an acyclic one. The existence of a finitely presented fully
self-replicating group stays open. It is a special case of the Bartholdi--Grigorchuk--Šunić
question on finitely presented branch groups.

**Calibration.**

- `R = Fin(A_d)`, the finitary group. It satisfies `R ≅ R ≀ A_d` and is a direct limit of
  iterated wreath products of `A_d`, whose orders involve only primes `≤ d`. So
  `H̃_*(R; Z[1/d!]) = 0`, as item 3 requires of every `FP_∞` example. It is not
  finitely generated, so the theorem imposes nothing more.
- `R = ⟨A_5, b⟩` of `fully-self-replicating-tree-groups-give-fg-tits-hosts` has `b` of
  order 15, so `H_1(R; Z)` is a quotient of `Z/15` and `H_1(R; Q) = 0`, as item 3(d)
  allows.
- An abstract `G ≅ G × G`, the case `d = 2` with trivial `P`, is outside the setting
  because `P` is not transitive. The same count gives `h_1 = 2h_1`. This is consistent
  with the finitely presented examples of Tyrer Jones: a finitely generated `G ≅ G × G`
  is perfect, since `G^{ab} ≅ (G^{ab})^2` forces the finitely generated abelian group
  `G^{ab}` to be `0`.
- `P = Sym(X)` with one odd class leaves no excess in any degree. So item 4 cannot be
  sharpened to acyclicity without using that `P` lies in the alternating group.
