---
rg: 2
id: jacobson-lifting-growth-needs-nilpotent-or-matrix-commutant
kind: claim
title: The lifting growth of a Jacobson compressor is the shift defect of the symbol image of the commutant under conjugation by the compressor symbol, so it vanishes whenever that conjugation has finite order on the symbol commutant, in particular whenever the symbol commutant is commutative and reduced
distinct_from:
  jacobson-compressor-commutant-growth-splits: that defines type (b) growth B(g) as a cohomological quotient and asks whether it can be nonzero; this identifies B(g) with beta(P)/P for the automorphism beta = Ad rho(g) of the symbol commutant, proves dim B(g^k) = k dim B(g), and kills B(g) whenever beta has finite order, leaving only non-reduced or non-commutative symbol commutants.
  noetherian-invariant-compression-rigidity: that is the chain-condition principle for R-submodules; the symbol image P of the commutant is only an F-subalgebra, and this shows the noetherian argument still traps beta(P) inside R.P, with the remaining defect controlled by the order of beta in Aut_R(C).
---

**ESTABLISHED** (route `jacobson-lifting-growth-nilpotent-or-matrix-commutant-proof`, whose only prerequisite is
the ESTABLISHED `jacobson-compressor-commutant-growth-splits`).

## Setting

Notation of `jacobson-compressor-commutant-growth-splits`.

- `F` is any field, `J = F<S,T | TS = 1>`, `I = (1 - ST)`, `R = F[x,x^-1]` and `K = F(x)`.
- `rho : M_N(J) -> M_N(R)` is the symbol map.
- `Gamma <= GL_N(J)` is any subgroup, and `g in GL_N(J)` satisfies `Gamma' = g Gamma g^-1 <= Gamma`.
- Put `h = rho(g)`, `C = C_R(Gamma)` (the commutant of `rho(Gamma)` in `M_N(R)`), and `P = rho(A(Gamma))`.
- `B(g)` is the type (b) (lifting) growth of that theorem.

By symbol rigidity `h C h^-1 = C`. So `beta = Ad(h)|_C` is an automorphism of the `R`-algebra `C`.

## Theorem

1. **Shift formula.** `P <= beta(P)` and `B(g) ~= beta(P) / P` as `F`-vector spaces.
2. **Saturation trap.** `beta(R.P) = R.P`. Hence `beta(P) <= R.P` and `B(g)` embeds in `R.P / P`.
   In particular `B(g) = 0` whenever `P` is an `R`-submodule of `C`.
3. **Powers.** `g^k` is a compressor for every `k >= 1`, and `dim B(g^k) = k dim B(g)` (as cardinals).
   So `B(g) = 0` if and only if `B(g^k) = 0` for some `k >= 1`.
4. **Finite order kills lifting growth.** If `beta^m = id_C` for some `m >= 1`, then `B(g) = 0`.
5. **Reduced commutative symbol commutants.** If `C` is commutative and has no nonzero nilpotents, then
   `Aut_R(C)` is finite. Hence `B(g) = 0` for every compressor `g` of `Gamma`, and all commutant growth of every
   compressor is finitary (type (a)). This covers every `Gamma` for which `rho(Gamma)` acts on `K^N` semisimply
   with pairwise non-isomorphic simple constituents whose endomorphism rings are commutative (for instance
   absolutely irreducible constituents), and in particular every absolutely irreducible `rho(Gamma)`, where
   `C = R.1`.

## Corollary (what type (b) growth needs)

If `B(g) != 0`, then `beta` has infinite order in `Aut_R(C)`, and after replacing `g` by a power one of the
following holds.

- **(N) Nilpotent commutant.** `C_K = C (x)_R K`, which is the commutant of `rho(Gamma)` in `M_N(K)`, is not
  semisimple. Then its radical is a nonzero nilpotent ideal of intertwiners, and `rho(Gamma)` acts on `K^N`
  non-semisimply.
- **(M) Matrix commutant with inner shift.** `C_K` is semisimple but not commutative. For semisimple `rho(Gamma)`
  this means some simple constituent has multiplicity at least 2 or a noncommutative endomorphism division ring.
  Then `beta = Ad(w)` on `C_K` for some
  `w in C cap C_K^x` that normalizes `C`, and `Ad(w)` has infinite order on `C`.

Each shape can fail on its own. Both are realized at the level of algebras: with `h = diag(x^-1, x)` (which lifts to
`GL_2(J)` because `det h = 1`),

- `P = {[[a, b], [0, a]] : a in F, b in x^2 F[x]}` inside `C = {[[a, b], [0, a]] : a, b in R}` for shape (N);
- `P = {[[a, b], [0, d]] : a, d in F, b in x^2 F[x]}` inside `C = M_2(R)` for shape (M);

and in both cases `beta(P) / P ~= F + F x` is nonzero. Whether such a `P` is `rho(A(Gamma))` for an actual
`Gamma` and compressor `g` is the open part.

## Consequence for DD on GL_N(J_F)

Combine this with Corollary 1 of `jacobson-compressor-commutant-growth-splits`. A Kazhdan infranormal pair
`Gamma <= G <= GL_N(J_F)` whose symbol commutant `C_R(Gamma)` is commutative and reduced carries a nontrivial rigid
defect only if some compressor has infinite type (a) growth. So question (ii) of that node, "can type (b) growth be
nonzero at all", is reduced to shapes (N) and (M).

## Scope

- Any field `F`, any subgroup `Gamma`; neither finite generation nor property (T) is used in the Theorem.
- Nothing is claimed about type (a) growth, or about soficity or hyperlinearity of any group.
