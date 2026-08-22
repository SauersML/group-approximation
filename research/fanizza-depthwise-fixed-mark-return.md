---
rg: 2
id: fanizza-depthwise-fixed-mark-return
kind: claim
title: Return each fixed Fanizza heat depth to one common mark with depth-dependent loss
distinct_from:
  fanizza-heat-filter-one-sided-return: that asks one finite gadget to decode arbitrarily large virtual depth, including a dimension-independent return mechanism; this permits a recursively presented family of fixed-depth cells and arbitrary loss growth with depth.
  dimension-reported-julia-amplitude-return: that makes a finite approximation detect its multiplicity and select an endogenous heat depth; this fixes the heat depth externally before taking the microstate limit and needs no dimension oracle.
  fanizza-canonical-profile-groupification: that states the final qualitative canonical collapse; this isolates the scalar fixed-depth comparison which, together with heat decay, proves that collapse.
---

**OPEN.**  Totally computably from the Fanizza instance `m`, construct a
uniformly recursively presented ordinary group extension with one fixed
rational group-algebra projection `P_m` such that:

1. on HALT instances, `P_m!=0` in one exact representation; and
2. for every fixed heat depth `t`, there are a finite relator prefix `R_(m,t)`,
   a finite canonical trace window `F_(m,t)`, and a finite constant
   `C_(m,t)` such that every matrix tuple `U` satisfies

```text
||P_m(U)||_2^2
 <=tr(A_(m,t)(U))
   +C_(m,t)(def_(R_(m,t))(U)+sep_(F_(m,t))(U)).        (DFR1)
```

Here `A_(m,t)=B_(m,t)^*B_(m,t)` is the fixed Fanizza heat amplitude.  Since
`P_m` is a fixed rational group-algebra expression, its evaluated HS norm is
well-defined even before its projection identities have been exactified.

There is no uniformity requirement on `C_(m,t)`, no endogenous stopping
index, and no comparison between `t` and matrix dimension.  This is strictly
weaker than the dimension-reported Julia return.  By
`fanizza-fixed-heat-depth-survives-hs-microstates`, on a NONHALT canonical
microstate sequence `(DFR1)` gives, first for fixed `t`,

```text
limsup_n ||P_m(U_n)||_2^2<=C_m/(4t^2).                 (DFR2)
```

Sending `t->infinity` collapses the same fixed mark.  Thus this claim is
exactly sufficient for `fanizza-canonical-profile-groupification` and hence
for the canonical-profile reverse-Kleene route.

## Attempts

- **Fresh cells at each depth remove finite compilation, not groupification.**
  Because the presentation may be recursively enumerable before effective
  Higman embedding, the `t`th return cell may have size and proof area growing
  arbitrarily with `t`.  This eliminates the unbounded-instruction compiler
  and the Amitsur--Levitzki stopping flag.
- **The scalar endpoint is already minimal.**
  `fanizza-heat-return-is-one-cyclic-amplitude-product` reduces `(DFR1)` to
  two cyclic products, and
  `one-additive-commutator-suffices-for-julia-return` reduces it further to
  one trace-zero additive commutator residual.  At fixed `t`, all
  telescoping constants may depend on `t`.
- **The surviving obstruction is genuinely matrix-only.**
  Imposing the return as a functorial identity in every finite tracial
  representation would also impose it in the regular finite von Neumann
  algebra.  Applying all depths would then kill the mark there.  The return
  still needs one finite-coordinate comparison unavailable in that regular
  representation; DCK removes runtime uniformity but not this firewall.
- **Finite Pauli rank is not that comparison.**
  `depthwise-pauli-packets-have-canonical-regular-escape` gives an exact
  canonical left-regular countermodel at every fixed packet rank.
- **Canonical moments linearize one depth but cannot close all depths.**
  `canonical-moments-linearize-fixed-depth-fanizza-return` expands
  `P_m^*P_m-A_(m,t)` in the group basis and pays every nonidentity term with
  the finite trace window.  However the tempting compiler which proves the
  corresponding regular-trace inequality for every `t` is refuted by
  `computable-regular-trace-fanizza-return-would-decide-halting`: it would
  make the mark literally zero in the NONHALT group algebra, an r.e.
  condition, while preserving it on HALT instances.  Thus cyclic/Julia/
  wandering constructions are useful only if their return is genuinely
  finite-matrix and fails in the regular representation.
- **A natural `2 by 2` Julia/Schur cell is not that comparison either.**
  `two-by-two-julia-schur-cell-cannot-return-the-fanizza-mark` shows that
  Julia and ordinary Schur calculus are regular-tracially functorial.  The
  alternative opposite-root `GL_2` commutator has exact quadratic/cubic
  contamination and does not isolate the additive trace-zero certificate.
  Passing to the clean `GL_3` Steinberg identity leaves the already isolated
  characteristic-zero coefficient-decoding problem.
