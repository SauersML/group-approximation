---
rg: 2
id: shell-double-coset-intersection-obstruction-proof
kind: route
title: Restrict stabilizer orbits to a translate of the original infinite shell orbit
target: shell-finite-biindex-hosts-require-large-intersections
requires: []
artifacts:
  - research/artifacts/boone-higman-spatial-overgroup-and-coset-gate-2026-09-08.md
---

Fix gamma. Inside Gamma/H consider the subset gamma E/H. Two
points gamma e_1 H and gamma e_2 H lie in the same H orbit exactly
when there exist h in H and a in H with

    h gamma e_1 = gamma e_2 a.

Equivalently gamma^-1 h gamma = e_2 a e_1^-1 belongs to E.
Thus these intersections with H orbits correspond exactly to the
orbits on E/H of K_gamma=E intersect gamma^-1 H gamma.

If H\Gamma/H is finite, it bounds the number of these K_gamma
orbits. Since E/H is infinite, K_gamma cannot be finite: every
orbit of a finite group has at most its order many points. Also
K_gamma is contained in E intersect gamma^-1 E gamma. This proves
both asserted intersection requirements.

If E is proper and almost malnormal in Gamma, choose gamma outside
E. Then E intersect gamma^-1 E gamma is finite, contradicting the
requirement. In the malnormal case K_gamma is trivial, so the
distinct points of gamma E/H already give distinct H orbits.

The obstruction applies to a genuine available embedding method:
[Wagner, Theorem A](https://arxiv.org/pdf/2404.00841), version 2,
constructs a malnormal embedding of every finitely generated
recursively presented group into a finitely presented group,
preserving decidability of word problem when it holds. For a
non-finitely-presented shell envelope that embedding is necessarily
proper. Thus it provides a host but fails this induced-action
criterion. The elementary double-coset proof itself does not use
Wagner's theorem or finite presentability of either group.
