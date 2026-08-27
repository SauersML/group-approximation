---
rg: 2
id: km-l0-h2-is-the-three-subspace-defect
kind: claim
title: The lattice's second L0-cohomology is a three-subspace distributivity defect with vanishing pairwise part
artifacts:
  - research/artifacts/km-lattice-cohomology-and-lp-fork-2026-08-23.md
distinct_from:
  km-some-ergodic-action-has-nonzero-l0-second-cohomology: that is the open existence question across all ergodic actions; this is an established exact computation of the Bernoulli instance's H^2 as an explicit defect module, deciding nothing about its (non)vanishing yet.
  km-l0-cohomology-is-the-49-orbit-invariants-complex: that reduces H^(<=2) to the thick-part orbit complex for all divisible coefficients; this supersedes it for the Bernoulli L^0 module by running the isotropy spectral sequence on the contractible building itself, where local finiteness of parabolics kills every entry except (1,1).
  locally-finite-bernoulli-first-l0-cohomology-nonzero: that proves the ingredient groups are nonzero; this computes how they assemble into H^2.
---

**THEOREM (established; proof in
`km-l0-three-subspace-proof`).**  Let `Lambda = Lambda_(2,4,6)(q)`,
`q > 1764^3`, acting on its Bernoulli shift `Y = [0,1]^Lambda`, and
`V = L^0(Y, R)`.  Identify (injectively, by finite index over `B_-`
and unique divisibility) each `H^1(P_K^-, V)` with its stable image
`St_K` inside `H := H^1(B_-, V)`.  Then:

```text
(a) H^2(Lambda, V) = E_2^(1,1) of the isotropy spectral sequence on
    the contractible building X_-, the ONLY nonzero entry on its
    degree-two diagonal;

(b) St_j cap St_k = St_jk for all three vertex pairs (the pairwise
    defect vanishes: the obstruction module is the Levi-invariant
    rational cycle space of the rank-two polygon incidence graph,
    which flag-transitivity kills);

(c) H^2(Lambda, V) ~= ((St_1 + St_2) cap St_3) / (St_13 + St_23),
    the three-subspace distributivity defect;

(d) Hom(N_3, V)^Lambda = 0 (the digon-link flag-transitivity
    kill, artifact Addendum 14), so inflation embeds H^2(Lambda, V)
    into H^2(Gamma_3, V) = St_3/(St_13 + St_23) EXACTLY onto the
    defect of (c): no extension ambiguity, and the defect is the
    kernel of an explicit Shapiro map delta into
    H^1(P_12^-, Hom(Z_1(K_(q+1,q+1)), V)).
```

Consequence: Ioana--Spaas--Wiersma Corollary E fires at the Bernoulli
action (hence `C*(Lambda)` fails the LP) IF AND ONLY IF this defect
module is nonzero -- the clause is now a single equivariant
computation, not a search over mechanisms.


## Not an integral Smith-form computation

An imported suggestion is to materialize `((St_1+St_2) cap St_3)/(St_13+St_23)`
as a signed integer incidence complex and read a nonzero certificate off its
Smith normal form.  That tool does not apply here: the coefficients
`V=L^0(Y,R)` are uniquely divisible, the identification of the `St_K` already
uses that divisibility, and the pairwise part (b) is a *rational* cycle space.
The reduction in (d) is also strictly sharper than the suggestion — the defect
is already the kernel of one explicit Shapiro map — so the remaining work is
that equivariant computation, not an integral normal form.
