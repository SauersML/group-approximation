---
rg: 2
id: thompson-v-mf-models-overlap-disjoint-involutions
kind: claim
title: In every operator-norm model of Thompson V, disjointly supported free involutions have -1 eigenspaces meeting in exactly half, so support-additive rank counting cannot prove V is not MF
distinct_from:
  thompson-v-character-simplex: that classifies traces of C*(V) (normalized, scale 1, a von Neumann statement); this is an exact integer statement about ranks in each matrix coordinate of an operator-norm model, valid at every scale including ranks o(d_n), and uses no character theory.
  v-rank-functions-split-as-augmentation-plus-reduced: that splits Sylvester rank functions on the group algebra F[V]; this concerns unitary operator-norm asymptotic representations and the exact isotypic multiplicities of their finite elementary abelian subgroups.
  torsion-normal-generator-mf-character-criterion: that reduces full MF radical to triviality of normalized trace limits; this constrains the unnormalized integer ranks, where a trace limit sees nothing when the -1 eigenspace has rank o(d_n).
  unperforated-paradox-makes-steinberg-purely-infinite: that makes the type-semigroup paradox 2[1]<=[1] kill MF quotients of EL_n(R) for n>=2; this shows the paradox cannot be read inside the rank-one unit group V through finite-subgroup ranks, because there the rank of a support is not additive.
  thompson-v-has-full-mf-radical: that is the open goal (V not MF); this is an unconditional structure theorem for hypothetical MF models of V and kills one class of proofs of it.
---

**ESTABLISHED** by `thompson-v-mf-models-overlap-disjoint-involutions-proof`
(lane proof, swarm-0917-w17-w17-ptm-pull, elementary, no literature input).

**Setting.** `V=G_(2,1)` acts on Cantor space `C={0,1}^N` by finite prefix
replacements. Call an involution `x in V` a **free proper involution** if its
support `A=supp(x)` is a clopen set with `A != C`, and `x` has no fixed point
in `A`. Let `pi_n: V -> U(d_n)` be an operator-norm asymptotic representation
(`||pi_n(gh)-pi_n(g)pi_n(h)|| -> 0` for all `g,h`) and `omega` a free
ultrafilter. For an involution `x` let `M_n(x)` be the rank of the `-1`
eigenprojection of any exact involution within distance `<1` of `pi_n(x)`
(well defined for `omega`-almost every `n`).

**Theorem.** For `omega`-almost every `n`:

1. **(Uniform rank.)** `M_n(x)=M_n` is the same integer for all free proper
   involutions `x`.
2. **(Exact half overlap.)** If `a,b` are free proper involutions with
   disjoint supports and `supp(a) cup supp(b) != C`, then the exact commuting
   rounding of `(pi_n(a),pi_n(b))` has joint eigenspace multiplicities
   `m_{--}=m_{-+}=m_{+-}=M_n/2` and `m_{++}=d_n-3M_n/2`. In particular
   `rank(P_a^- wedge P_b^-) = M_n/2` and
   `rank(1-e_{<a,b>}) = (3/2) M_n`, not `2M_n`.
3. **(Regular blocks, supernatural divisibility.)** For every `k>=1` the
   group `E_k=(Z/2)^k` acting by XOR on the `2^k` cylinders `[0w]`, `|w|=k`,
   is represented (after exact rounding) as
   `trivial^(d_n-2M_n)  +  (M_n/2^(k-1)) * regular(E_k)`
   (total trivial multiplicity `d_n-(2-2^(1-k))M_n`).
   Hence `2^(k-1)` divides `M_n` for `omega`-almost every `n`, for each fixed `k`.

**Consequence (class obstruction).** Any proof of `thompson-v-has-full-mf-radical`
that transplants the Cuntz/Tarski paradox of `V subset U(O_2)` (`[1]=2[1]` in
`K_0(O_2)`) by assigning to each clopen set `A` the rank of the nontrivial
part of a finite subgroup supported in `A` needs **support additivity**:
`rank(1-e_{<a,b>}) = rank(1-e_a)+rank(1-e_b)` for disjointly supported `a,b`.
By part 2 that identity reads `(3/2)M_n = 2M_n`, i.e. `M_n=0`; and `M_n=0`
eventually is already equivalent to asymptotic triviality of `pi` (a free
proper involution normally generates the simple group `V`). So support
additivity is not a lemma toward the goal but a restatement of it: the class
dies at the additivity step, at every scale, with the invariant `m_{--}`
(overlap of the `-1` eigenspaces) forced to equal `M_n/2`. What the finite
subgroup rank data do force (parts 1 and 3) is realized by exact
representations `trivial^a + regular^b` of the locally finite dyadic
permutation group `W = union_N Sym(level-N cylinders)` (take `d-a` divisible
by `|Sym(2^N)|`; restrictions of regular representations to subgroups are
regular, so the data are consistent under inclusion and `V`-conjugacy), so
no contradiction can come from these multiplicities alone. A surviving proof must use either infinite-order
elements of `V` or the relative position of non-commuting finite subgroups'
eigenspaces, which ranks do not record.
