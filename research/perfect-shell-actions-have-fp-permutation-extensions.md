---
rg: 2
id: perfect-shell-actions-have-fp-permutation-extensions
kind: claim
title: Perfect decidable shell inputs admit finitely presented permutation extensions with an enlarged stabilizer
distinct_from:
  perfect-shell-pairs-have-finite-biindex-fp-hosts: that keeps the original shell point stabilizer itself; this allows a larger subgroup K whose intersection with the shell envelope is exactly that stabilizer, and requires K to be core-free and finitely generated.
artifacts:
  - research/artifacts/boone-higman-enlarged-digit-fiber-stabilizer-2026-09-08.md
---

For every infinite perfect finitely presented group P with decidable
word problem, there exist an enumeration nu, an embedding E_nu<=Gamma
in a finitely presented group, and K<=Gamma satisfying

    K finitely generated,
    core_Gamma(K)=1,
    K\Gamma/K finite,
    K intersect E_nu=(E_nu)_p.

This is OPEN. The Gamma/K action is an extension in the sense
that it contains the original shell orbit as one E_nu orbit;
E_nu need not be transitive on the enlarged set.

The retained-stabilizer host hypothesis implies this by taking
K=(E_nu)_p. The digit-fiber theorem supplies these data for every
fixed-base shell action, including the arithmetic A5*A5 example,
using Gamma=H_(h,r) and its full setwise fiber stabilizer. That K
contains the retained stabilizer with infinite index.

There is no construction of these data for arbitrary decidable
inputs. The rational digit host cannot be assumed available for
them. Finite presentation of E_nu itself is not a requirement.
