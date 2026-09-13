
## 3. Reduction to subgroups of index coprime to m

For `S <= G` write `Y_S` for the right-`S`-invariant configurations in `A^G`. It is a copy of `A^(G/S)`.
When `S <= H`, `Y_H ⊆ Y_S`.

**Theorem 4.** Let `S <= H <= G`, with `H` finite and `[H : S]` coprime to `m`, and identify `A` with `Z/m`.
Let `tau : Y_H -> Y_H` be continuous, equivariant and injective. Then there is a continuous, equivariant,
injective `Phi : Y_S -> Y_S` with:
- `Phi(Y_S) ∩ Y_H = tau(Y_H)`;
- `Phi` onto iff `tau` onto.

*Proof.* Let `c` be the inverse of `[H : S]` mod `m`, and for `z in Y_S` put
`P(z)(k) = c sum_(hS in H/S) z(kh)`.
1. *Well defined.* Replacing the representative `h` by `hs`, `s in S`, does not change `z(kh)`, because `z`
   is right-`S`-invariant.
2. *Output in `Y_H`.* `P(z)(kh') = c sum_(hS) z(kh'h)`, and `hS -> h'hS` permutes `H/S`.
3. *Fixes `Y_H`.* For `z in Y_H` the sum is `[H : S] z(k)`, so `P(z) = z`.
4. `P` is linear, continuous and equivariant, so `Y_S = Y_H ⊕ (ker P ∩ Y_S)`.
5. Put `Phi(z) = tau(Pz) + (z - Pz)`. Every term lies in `Y_S`, so `Phi` maps `Y_S` to itself. Steps 3 to 6
   of Theorem 1 run verbatim inside `Y_S`. QED

For `S = 1` this is Theorem 1.

**Corollary 5 (minimal stabilizers).** Suppose the node's claim holds at `(G, S, m)`: every injective
continuous equivariant self-map of `Y_S` at size `m` is onto. Then it holds at `(G, H, m)` for every finite
`H >= S` with `[H : S]` coprime to `m`. Hence:
- **Prime-power alphabets.** For `m = p^k`, it suffices to treat finite `p`-subgroups of `G`. Take `S` a Sylow
  `p`-subgroup of `H`.
- **General `m`.** It suffices to treat finite subgroups `H` with no proper subgroup of index coprime to `m`.
  - For `m = p^k` these are exactly the `p`-groups. A Sylow `p`-subgroup has index coprime to `p`, and
    proper subgroups of a `p`-group have index a positive power of `p`.
  - For `m` with two prime factors both dividing `|H|`, no reduction may be available: over `m = 6`,
    `H = S_3` has no proper subgroup of index coprime to `6`.

So over prime-power alphabets, the open part of the node concerns only coset shifts `A^(G/S)` whose
stabilizer `S` is a nontrivial finite `p`-subgroup of the host, at alphabet size `p^k`.

**Remark (one step inside a `p`-group).** Let `H` be a `p`-group, `N` a normal subgroup of index `p`, and
`h in H \ N`.
- Right translation `R_h z(k) = z(kh)` preserves `Y_N`: `z(knh) = z(kh (h^(-1) n h)) = z(kh)` because `N` is
  normal in `H`.
- `R_h` commutes with the left shift and has order `p` on `Y_N`.
- `Y_H = Fix(R_h) ∩ Y_N`, because `H = <N, h>`.

So the minimal step asks the following. Let `theta` be a shift-commuting automorphism of order `p` of the coset
shift `Y_N`, and let `tau` be an injective self-map of `Fix(theta)`. Is `tau` surjective whenever every
injective self-map of `Y_N` is? The order `p` of `theta` shares the prime with the alphabet. For `N = 1` this
is the full shift with the right translation by an element of order `p`. Lemma 2 is stated for the full shift
only; it is not claimed here for ambient `Y_N`.
