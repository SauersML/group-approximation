---
rg: 2
id: non-f3-short-detour-group-via-sb3-height-order
kind: route
title: SB_3 with the radial height-spread order would be a non-F_3 group with a short-detour enumeration
target: some-non-f3-group-has-a-short-detour-enumeration
requires:
  - sb3-radial-height-order-is-a-short-detour-enumeration
  - stallings-bieri-sb3-is-finitely-presented-not-f3
---

Immediate: the first required claim gives SB_3 a short-detour enumeration, and the second says that
SB_3 is not of type F_3. Together they witness the target.

Composed with `non-fn-qi-to-connected-space-via-short-detour-enumeration` and `zaremsky-1-03-by-no`,
this route would answer Zaremsky Problem 1.3 negatively under the geodesic reading. The only open input
is the detour condition in `sb3-radial-height-order-is-a-short-detour-enumeration`. Censuses support it
(`research/artifacts/zp-sb3-short-detour-2026-09-13-part3.md`), but it is not proved.
