---
rg: 2
id: decidable-inputs-admit-two-sided-fg-near-index-kernel
kind: claim
title: A decidable infinite finite presentation admits an enumeration whose near shift group is finitely presented with finitely generated near-index kernel
distinct_from:
  decidable-inputs-have-fp-one-singularity-shell-stabilizer: that asks for a finitely presented shell stabilizer; its germ gate needs only a one-sided ascending window, while this asks for the two-sided condition that ker(eta) is finitely generated.
  infinite-shift-higman-compiler: that asks for the whole envelope E_nu(P) to be finitely presented; this is the germ-level necessary gate (G1)+(G2) extracted by mz-envelope-fp-forces-two-sided-fg-near-index-kernel, which is equivalent to finite presentation of E_nu(P)/FSym(N).
  accessible-shell-inputs-admit-no-shift-normalizing-enumeration: that forbids width zero; this asks for some finite width N with s<s^i lambda(P) s^-i : |i|<=N>s^-1 equal to the same subgroup.
---

Let `P` be an infinite finitely presented group with decidable word problem. Then there is a bijection
`nu : P -> N` such that the near shift group `R_nu = < lambda(P), s >` (near permutations modulo finitary ones) is
finitely presented, and its near-index kernel `ker eta` is finitely generated.

Equivalently, by `mz-envelope-fp-forces-two-sided-fg-near-index-kernel`, the Mallery–Zaremsky germ group
`E_nu(P)/FSym(N)` is finitely presented for some `nu`. This is necessary for `infinite-shift-higman-compiler`.

**Known.**

- For `P = Z`, the zigzag enumeration works, because `zigzag-cyclic-shift-envelope-is-finitely-presented` makes
  `E_nu(Z)` finitely presented.
- The square spiral enumeration of `Z^2` fails.
- Every enumeration with injective `P*<s> -> R_nu` fails.
- Window width zero fails for accessible, not virtually cyclic, inputs.

**How this can fail.** It is a statement about the family of all enumerations of `P`. A refutation needs an
invariant of `P` such that every `nu` has
- `ker eta` not finitely generated (at least one of `[eta]`, `[-eta]` lies outside `Σ^1(R_nu)`), or
- `R_nu` not finitely presented.

## Attempts

- **Bounded two-dimensional enumerations of `Z^2`.** Finite-ray and bounded-jump realizations are already
  excluded by `finite-ray-shift-envelopes-require-virtually-cyclic-input`. The square spiral passes the one-sided
  shell window, but it dies at (G2): its `R_nu` is metabelian with a non-tame line module. A 45-degree "diamond
  spiral" enumeration looks like an axis-orthant piecewise translation, so the same two-sided Laurent line-module
  mechanism is predicted to kill it at (G2). This is not verified. The attack dies at (G2), not at the new two-sided
  window (G1), whose status for these enumerations is not decided.
- **Deferred: product inputs `P_0 x Z`.** The route `boone-higman-via-infinite-shift-compiler` only needs such
  inputs. No enumeration of any input that is not virtually cyclic is known to have a finitely generated
  two-sided window. This lane is deferred until (G1) is decided for one explicit enumeration of `Z^2`.
- **Unequal-radix free products (bh-shell-arith, 2026-09-18).** The equal-radix arithmetic enumeration of `A*A`
  dies because every generator is an automorphism of one digit tree (`arithmetic-a5-near-group-is-not-finitely-presented`).
  For `A_0*A_1` with `|A_0| != |A_1|`, the least-significant-first mixed-radix enumeration is still arithmetic, so mixed
  relations hold. But its shift is a radix conversion and not a cone map, so that proof does not transfer. The candidate
  is `unequal-radix-free-product-near-group-passes-both-germ-gates` (OPEN). Its perfect instance is `A_5*A_6`. A route
  to it is `finite-index-in-a-kernel-fg-near-host-passes-both-germ-gates`: finite index in a finitely presented near host
  with finitely generated near-index kernel gives both (G1) and (G2). The open inputs are the finiteness of the two-radix
  odometer host and the generation question `[H:R_nu] < infinity`.
