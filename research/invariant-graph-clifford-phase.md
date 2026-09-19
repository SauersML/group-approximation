---
rg: 2
id: invariant-graph-clifford-phase
kind: claim
title: Invariant-graph central quotients carry the same sofic-radical phase, and only a sign
distinct_from:
  kun-thom-clifford-radical-phase: That records one detector, the complete Clifford graph; this classifies the whole family of invariant-graph central quotients, identifies which of them are minimal, and proves no phase finer than a sign is available.
  literal-clifford-ce-model: That is the finite-index compressor group and its coset tower; this is the Kun--Thom infinite-index pair and the lattice of its central lamp quotients.
  sofic-radical-soficization: That is a general structure theorem for the sofic radical of an arbitrary countable group; this computes the image of one marked radical word in an explicit family of central quotients of one explicit group.
artifacts:
  - notes/TRUE_KUN_THOM_CLIFFORD_PHASE.md
  - notes/FALSE_FERMIONIC_KUN_THOM_ENDPOINT.md
---

Let `Gamma<G` be a nonnormal infranormal Kazhdan pair as in
`kun-thom-clifford-radical-phase`, `X=G/Gamma`, `o=Gamma`, `h=t^(-1)gamma t`
outside `Gamma`, `y=h Gamma`, and

```text
H=G *_Gamma (Gamma x C_2),   r=[k,h],   x=[k,r].
```

1. **Free-lamp normal form.**  `H = (*_X C_2) semidirect G`, with
   `k_(g Gamma)=g k g^(-1)`.  Under it `r=k_o k_y` and `x=(k_o k_y)^(-2)`,
   an element of infinite order.
2. **The invariant-graph family.**  Let `S` be any `G`-invariant set of
   unordered pairs of distinct points of `X` (equivalently a union of
   symmetric nontrivial double cosets `Gamma g Gamma`), let `V=directSum_X F_2`
   carry the adjacency form `b_S`, let `Vtilde_S` be the central extension

   ```text
   z^2=1,  z central,  c_u^2=1,  [c_u,c_v]=z^(b_S(u,v)),
   ```

   and `Wtilde_S=Vtilde_S semidirect G`.  Then `k |-> c_o`, `g |-> g` defines
   a surjection `H ->> Wtilde_S` with

   ```text
   x |-> z^(b_S(o,y)).
   ```

   So `x` survives exactly when `{o,y} in S`, and every such `Wtilde_S` is a
   nonsofic quotient of `H`.
3. **Tracial model.**  Let `A_S` be the twisted group von Neumann algebra of
   `(V,b_S)` at the character `z |-> -1` — self-adjoint unitaries `C_u` with
   `C_u C_v = (-1)^(b_S(u,v)) C_v C_u` and the canonical trace — with `G`
   permuting the `C_u`, and `M_S = A_S crossed_product G`.  Then `Wtilde_S`
   embeds faithfully in `U(M_S)` and `x |-> -1` exactly.
4. **Minimal quotient = factorial model.**  The following are equivalent:
   `b_S` is nondegenerate on `V`; `Z(Vtilde_S)=<z>`; `A_S` is a factor, and
   then `A_S` is the hyperfinite `II_1` factor.  If moreover `G` acts
   faithfully on `X`, they imply that `<z>` is the monolith of `Wtilde_S`, so
   `Wtilde_S` is a *minimal* quotient of `H` in which `x` survives.  If `b_S`
   is degenerate, `L(rad b_S)` is a nontrivial `G`-invariant abelian
   subalgebra of the centre of `A_S`: the model reacquires exactly the
   commuting coordinate that the Kun--Thom permutation-normalization argument
   acts on.  The complete graph is nondegenerate and gives `A_S=Cl(X)`, so the
   literal Clifford model is one instance of this family, not a canonical
   choice forced by anything.
5. **Phase rigidity: only a sign is available.**  Let `K` be abelian, let
   `H_K=G *_Gamma (Gamma x K) = (*_X K) semidirect G`, and let the lamp part
   of a homomorphism factor through any `G`-equivariant central extension of
   `directSum_X K` with commutator pairing `b`.  Then the marked word satisfies

   ```text
   x |-> b(e_o,e_y)^(-1).
   ```

   If some element of `G` reverses the marked pair — equivalently
   `Gamma h Gamma = Gamma h^(-1) Gamma` — then `2 b(e_o,e_y)=0`.  Hence at a
   symmetric marked double coset the only nontrivial detector value is an
   involution: the Clifford sign is the *unique* phase, and no root-of-unity
   (anyonic or paraparticle) refinement of the lamp can exist.
