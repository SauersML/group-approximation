---
rg: 2
id: root-column-fixed-projection-is-not-in-root-pair-cstar
kind: claim
title: In every delta_e-profile adjoint corona, the fixed-vector projection of an amenable root column is not in the C-star algebra of any normalizing subgroup in which a centralizing root has amenable centralizer, so relative (T) of the root pair cannot supply the transport projection
distinct_from:
  window-average-kazhdan-substitute-forces-trivial-corona-rep: that kills norm limits of finite-window averages over one root subgroup, which lie in C*(sigma(N)); this kills every element of the larger algebra C*(sigma(K)) for a nonabelian K normalizing N, including all functional calculus of Markov elements of the relative-(T) pair EL_2(J) x| J^2, and names a different invariant, a tempered quasi-regular representation realized on Fix(N).
  kesten-spectral-gap-replaces-kazhdan-projection-per-model: that isolates (MSG) for a finitely generated subgroup L as the only Kazhdan input of transport; this shows that for L replaced by an amenable root column N, which already carries the full compression certificate of the Jacobson head, the substitute projection cannot come from C*(sigma(K)) for the normalizing subgroups K that relative (T) controls.
  tracial-model-spectral-gap-is-character-gap-weaker-than-t: that shows the trace sees the regular representation and is blind to tau-null spectrum; this uses exactly that fact, together with centralizing root vectors on Fix(N), to force two weakly overlapping summands and hence rule out a central fixed projection.
  property-t-free-jacobson-head-collapse: that is the open (T)-free head collapse; this is a class kill of one natural route to it.
artifacts:
  - research/root-column-fixed-projection-is-not-in-root-pair-cstar-proof.md
  - non_mf_groups_exist.tex
---

**ESTABLISHED KILL (written proof; not Lean-verified).**

**Setting.**
- `G` is countable and `(V_n)` is an operator-norm asymptotic representation
  of `G` on `C^(d_n)`.
- `sigma~(g)=[Ad V_n(g)]` in the adjoint corona
  `B=prod_n B(M_(d_n)(C),||.||_2)/direct_sum`, as in Theorem
  `thm:transport` of `non_mf_groups_exist.tex`.
- For a free ultrafilter `omega`, `H_omega` is the ultraproduct of the
  Hilbert spaces `(M_(d_n)(C),||.||_2)`, with the representation `pi_omega` of `B`.
  `H_B=direct_sum_omega H_omega` is the **canonical faithful representation** of `B`.
- For `N<=G`, `P_N` is the orthogonal projection of `H_B` onto
  `Fix pi(sigma~(N))`.
- For `K<=G`, put `A_K=C*(sigma~(K)) subset B`.

**Theorem (root-column kill).** Assume:
- (K1) `N` is an infinite normal subgroup of `K<=G`;
- (K2) there is `y in G` commuting with every element of `N` such that the
  centralizer `C_K(y)` is amenable;
- (K3) `tr V_n(g)->0` for every `g != e` in `<K,y>`.

Then `P_N` is not an element of `A_K`. More precisely, the summands of
`sigma~|K` on `H_1=Fix(N)` and on `H_2=H_1^perp` both weakly contain the
quasi-regular representation `lambda_(K/C_K(y))`. The first contains it
as a subrepresentation. The second weakly contains it if `P_N in A_K`,
and then `P_N` would split `A_K` along two summands with a common
nonzero weak quotient, which is impossible.

**Application to the Jacobson head.** Let:
- `J=F_2<S,T|TS=1>`, `Q=1-ST`;
- `G` be `St_5(J)`, or `Delta=St_20(L_(F_2)(1,2))` through `S->s_1, T->t_1`;
- `N=X_13(J)X_23(J)` (isomorphic to `J^2`);
- `K=<X_12(J),X_21(J),N>`, the root pair `EL_2(J) x| J^2` at the matrix level;
- `y=x_14(1)`.

Then:
1. **(K1), (K2) hold.** `C_K(y)` is central-by-(`Stab_(EL_2(J))(e_1) x| J^2`).
   The stabilizer is abelian-by-`U(J)`, and `U(J)=union_m GL_m(F_2)` is
   locally finite. So every `delta_e`-profile model of `G` satisfies the
   Theorem, and `P_N` is not in `C*(sigma~(K))`.
2. **The column carries the whole certificate.** With `u,c` from Lemma
   `lem:ring-compression-cell` (`s=S`, `t=T`, `e=Q`):
   - `uNu^(-1)<=N` and `c in C_G(N)`;
   - `[ucu^(-1),x_23(1)]=x_13(Q)`.

   So the head `w=x_13(Q)` lies in the compression defect `D_G(N)` of an
   amenable, locally finite subgroup.
3. **Transport needs only `P_N in B`.** If `P_N in B`, the proof of
   Theorem `thm:transport` and Corollary `cor:defect-hs` goes through
   verbatim for `L:=N`, with no (T), and gives `||V_n(w)-1||_2->0`.
4. **Relative (T) cannot fill it.** The pair `(K,N)` has relative (T)
   (`elementary-linear-semidir-pair-relative-t`). Every element that
   relative (T), functional calculus of Markov elements of `C[K]`, or norm
   limits of averages over `N` can produce lies in `A_K`. Item 1 excludes
   all of them in every `delta_e`-profile model.

**Invariant and step where every member dies.**
- *Invariant:* the tempered quasi-regular representation `lambda_(K/C_K(y))`.
  - It is realized **exactly** on `Fix(N)` by the centralizing root vectors
    `eta=[V_n(y)]`.
  - It is realized **weakly** on `Fix(N)^perp` through the trace, which sees
    `lambda_K` there.
- *Step:* placing `P_N` in `A_K`. Centrality of `P_N` in `A_K` would force
  `ker sigma_1 + ker sigma_2 = A_K`, and that sum is contained in the kernel of
  that common weak quotient.

**What is left.** A (T)-free proof along the root column must produce
`P_N` in `B` from outside every such `A_K`:
- non-centrally, from elements of `C*(sigma~(G))` whose defining subgroup has
  a nonamenable `y`-centralizer;
- or from non-group elements of `B`.

Relative (T) of the root pair is not enough. Even with `P_N in B`, only the
Hilbert--Schmidt form of the head collapse follows (item 3). The passage to
operator norm is a separate input, which the manuscript takes from Theorem
`thm:normal-kazhdan`.

Proof route: `root-column-fixed-projection-is-not-in-root-pair-cstar-proof`.
