## 5. Pass 4: the colour-exchange defects die (the {2,p,q}-cube swindle)

Lane proof, not reviewed. It supersedes the "Proposed kill" and the `π` bookkeeping of §3.

**Forced lifts.** Keep only `Y_p` free (`Y_2 = 1`). Put:
- `X_{1,1,p} = Y_p`;
- `X_{n,2,p} := φ_1(X_{n−1,1,p})` for `n ≥ 2`;
- every other position by (d)-transport from position 2.

Then (a) and (d) hold exactly (Lemma P), and `X_{n,i,p} = φ_1(X_{n−1,i−1,p})` for all `i ≥ 2`,
because (d)-transport by permutations fixing cell 1 commutes with `φ_1`. So `π ≡ 1` by
construction, and a defect of an instance at size `n` is `ψ^{n−1}` (colour exchange) or
`ψ^{n−2}` (far commutation) of the base defect.

**ψ is idempotent on K.** For `z ∈ K`, `ψ(z) := φ_A(z)` does not depend on the proper box `A`
(pass 2). So `ψψ(z) = φ_A φ_A(z) = φ_{place A A}(z) = ψ(z)`. Hence `ψ = id` on `ψ(K)`.

**Far commutation.** The base defect `D_b(p,q)` (size 2, cells `0(2)`, `1(2)`) is independent of
the `Y`'s:
- each lift at size `≥ 2` carries a central change `ψ(z)`;
- after the `Y`'s are transported away (Lemma T), both paths reduce to words in comb-cell
  transpositions.

So `D_b(p,q) ∈ K ∩ Γ_∅`. **Input V:** `ε` is injective on the 2-power subgroup `Γ_∅`. This follows
from Bleak–Quick's theorem for `P = ∅`, since their relations map into ours. Given it,
`D_b(p,q) = 1`, and every far-commutation square closes.

**Colour exchange.** Write `D_{uv}` (additively; `D_{vu} = −D_{uv}`) for the root defect, at size
1, of the square "`u` then `v` on all children" against "`v` then `u`".
1. *Changing `Y`.* Under `Y_p ↦ Y_p z_p`, a path gains `z` for its size-1 step and `ψ(z)` for each
   later step. So `D_{uv}` changes by `z_u + u ψ(z_v) − z_v − v ψ(z_u)`, and in particular
   `D_{2p}` changes by `2ψ(z_p) − z_p`.
2. *The cube.* The six orderings of the splits `2, p, q` of `Z` form a hexagon of squares. Defects
   are central and telescope, so
   `D_{2p} + F_{2q}(p) + D_{pq} − F_{2p}(q) − D_{2q} − F_{pq}(2) = 0`.
   Here `F_{uv}(w)` is the sum of the `(u,v)` defects at the `w` children, all at sizes `≥ 2`,
   hence in `ψ(K)`. The far-commutation defects that interleave vanish.
3. *Step 1.* Take `z_p := D_{2p}`. Then the new `D_{2p} = 2ψ(D_{2p}) ∈ ψ(K)`, and by the cube
   `D_{pq} ≡ D_{2q} − D_{2p} ≡ 0 (mod ψ(K))`.
   - So every generator of `K` lies in `ψ(K)`, i.e. `K = ψ(K)`.
   - By idempotence, `ψ = id` on `K`.
4. *Step 2.* With `ψ = id`, take `z_p := −D_{2p}`. Now `D_{2p} = 0`, and the cube reads
   `D_{pq} = (1−q) D_{2p} + (p−1) D_{2q} = 0`.

Every defect vanishes for this choice of lifts, so `K = 1` by Corollary R. Hence:

> **Theorem (conditional).** Assume Fact O (the Ore presentation of `PC`; MMN 1609.07058, or its
> elementary proof) and Input V (Bleak–Quick: (R1)–(R3) present Thompson's `V`). Then (R1)–(R3)
> present `CT_P(Z)` for every finite `P`.

**Why it works.** The colour with two edges gives `D_{2p} ↦ D_{2p} + 2ψ(z) − z`. That is the
2-cell shadow of `[B] = 2[B]` (FKPS: `N_2 = 1`). Without a colour of arity 2 the swindle fails,
which matches `H_2 ≠ 0` when `gcd(N_i) > 1`.

**Remaining for an unconditional proof:**
- Fact O, written in full;
- Input V without Cannon–Floyd–Parry (Higman normal forms, or the same swindle on the
  far-commutation squares of `V`, which does not work as is: the far-commutation class at size 2
  is untouched by the cubes);
- then the finite truncation.

