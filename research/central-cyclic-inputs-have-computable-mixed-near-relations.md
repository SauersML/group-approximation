---
rg: 2
id: central-cyclic-inputs-have-computable-mixed-near-relations
kind: claim
title: Inputs with a central infinite cyclic subgroup of infinite index admit computable enumerations whose near shift group satisfies a mixed relation
distinct_from:
  route-form-shell-inputs-have-computable-mixed-near-relations: that needs an infinite cyclic direct factor; this needs only a central infinite cyclic subgroup of infinite index, which covers Deligne's lattice, whose center is not a direct factor.
  free-shift-shell-envelopes-are-not-finitely-presented: that is the obstruction for enumerations whose near shift group is P*<s>; this constructs enumerations to which it does not apply.
  decidable-inputs-have-fp-shell-envelopes: that asks for a finitely presented envelope; this only removes one necessary obstruction and asserts no finite presentation.
artifacts:
  - research/artifacts/solve-deligne-shell-singfix-2026-09-13.md
---

**ESTABLISHED** through `mixed-near-relations-via-arithmetic-central-element-proof`
(elementary; not independently reviewed; no novelty claimed).

**Setting.** Let `P` be countably infinite, and let `t` be a central element of
infinite order with `|P : <t>|` infinite. Let `lambda'` be the residue-affine
permutation of `route-form-shell-inputs-have-computable-mixed-near-relations`:

    lambda'(4k)   = 8k,       lambda'(4k+1) = 2k+1,
    lambda'(4k+2) = 8k+4,     lambda'(4k+3) = 4k+2,

except that `lambda'(0) = 1`, `lambda'(1) = 2` and `lambda'(3) = 0`.

**Statement.**
1. There is a bijection `nu : P -> N` whose left regular permutations satisfy
   `lambda_t = lambda'`.
2. For such `nu`, `[lambda_t s^4 lambda_t^-1, s^8] = 1` in `NearSym(N)`, where
   `s : n -> n+1`. This is a nonidentity reduced word of `P*<s>`. So
   `R_nu = <lambda(P), s>` is not `P*<s>`, and
   `free-shift-shell-envelopes-are-not-finitely-presented` does not apply to
   `E_nu`.
3. Suppose `P` is finitely generated, has decidable word problem, and membership
   in `<t>` is decidable. Then `nu` and its inverse can be computed.

**Deligne's lattice.** Take `P = Gamma~` and `t = z`, the generator of the
central kernel of `Gamma~ -> Sp_4(Z)`. All three items hold, so `Gamma~` has
computable enumerations that avoid the free-near-shift obstruction.

**Scope.** The regular permutations of the other elements are unconstrained. No
finite presentation of `E_nu`, of its singularity stabilizers or of its germ
group is asserted.
