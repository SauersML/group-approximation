---
rg: 2
id: nonrecursive-a2-kernel-makes-e-of-wreath-not-rec-presented
kind: claim
title: If some type [A_2] action G on S has a nonrecursive kernel, then the finitely presented wreath product (Z/2) wr_S G has E not recursively presented, answering MathOverflow 412219 negatively
requires:
  - mixed-identities-encode-normal-closure-commutation
  - e-of-finitely-presented-group-is-recursively-presented
distinct_from:
  some-a2-action-has-a-nonrecursive-kernel: that is the open existence claim (FFWZ Question 5.9, first part, negative direction); this shows it implies a negative answer to MO 412219 in the finitely presented case.
  mixed-identities-encode-normal-closure-commutation: that is the general encoding of normal-closure commutation as one-variable mixed identities; this applies it to lamp elements of a permutational wreath product, where commutation becomes membership in an action kernel.
  e-of-finitely-presented-group-is-recursively-presented: that is the open MO 412219 claim; this is a conditional refutation of it.
---

**ESTABLISHED as an implication** (lane proof, elementary; not reviewed; no priority claimed). One input is
recalled but not read at source here: Cornulier's criterion for finitely presented wreath products,
*Finitely presented wreath products and double coset decompositions* (Geom. Dedicata 122, 2006). As
recalled, it says: for `A ≠ 1`, the group `A wr_X G` is finitely presented iff `A` and `G` are finitely
presented, `X` has finitely many `G`-orbits with finitely generated stabilizers, and `G` has finitely many
orbits on `X × X`.

**Statement.** Let `G ↷ S` be of type `[A_2]` (FFWZ Definition 1.3: `G` finitely presented, finitely
generated point stabilizers, finitely many orbits on `S × S`), with kernel `K` not recursive. Put
`W = (Z/2) wr_S G`. Then:
1. `W` is finitely presented, by Cornulier's criterion applied to the type `[A_2]` data.
2. `E(W) ≅ (W * ⟨x⟩)/J_1(W)` is not recursively presented. So `W` is a counterexample to MO 412219.

**Proof.**
1. **Stabilizer membership is decidable.** The double cosets `G_s g G_s` are finitely many r.e. sets of
   words that partition all words, so each is recursive. In particular `G_s` is. Hence equality of points
   of `S` is decidable, and each orbit kernel `K_O` is co-r.e.
2. **Some orbit kernel is not r.e.** `K = K_{O_1} ∩ … ∩ K_{O_r}` over the finitely many orbits. If every
   `K_{O_i}` were r.e., each would be recursive, and so would `K`. So some `K_O` is co-r.e. and not
   recursive, hence not r.e.
3. **The lamp computation.** Fix `s_0 ∈ O`, let `c = δ_{s_0}` be the lamp at `s_0`, and let `d = g ∈ G`.
   - The normal closure `N_c` is the group of finitely supported functions `O → Z/2`.
   - An element `(b, n)` of `N_d`, with `n` ranging over the normal closure of `g` in `G`, commutes with
     every `m ∈ N_c` exactly when `n·m = m`, that is, when `n` fixes `O` pointwise.
   - So `[N_c, N_d] = 1` iff `g ∈ K_O`, since `K_O` is normal.
4. **The reduction.** By `mixed-identities-encode-normal-closure-commutation`,
   `[x δ_{s_0} x^{-1}, g] ∈ J_1(W)` iff `g ∈ K_O`. This is a computable many-one reduction of `K_O` to
   `J_1(W)`. If `J_1(W)` were r.e., `K_O` would be r.e., contradicting step 2. By item 1 of
   `e-of-finitely-presented-group-is-recursively-presented`, `E(W)` is recursively presented iff `J_1(W)` is
   r.e. ∎

**Reading.**
- A negative answer to FFWZ Question 5.9 of this kind, `some-a2-action-has-a-nonrecursive-kernel`, gives a
  negative answer to MO 412219 in the finitely presented case. No solvable word problem is needed anywhere.
- **Why this shape.** A reachability encoding with finitely many orbits cannot work directly. Finitely many r.e.
  orbits that partition a set are each recursive. So the undecidability has to sit in a Π_1 condition such as an
  orbit kernel, which is exactly what this node uses. This applies, for example, to the elementary reversible
  Turing machine groups suggested by team-lead.

**Status note (2026-09-18).** MathOverflow 412219 in the finitely presented case is now answered negatively outright by `fp-decidable-group-whose-e-is-not-recursively-presented` (bh-free-08, 1c6cfe928). That construction is consistent with this node: in its group, normal-closure commutation is undecidable. This node remains a separate reduction and is no longer needed for the answer.
