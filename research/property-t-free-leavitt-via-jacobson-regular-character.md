---
rg: 2
id: property-t-free-leavitt-via-jacobson-regular-character
kind: route
title: Pull a surviving Leavitt MF character back to the regular character of EL_5 of the Jacobson ring and exclude it
target: property-t-free-leavitt-full-mf-radical
requires:
  - leavitt-mf-survivor-yields-jacobson-regular-character
  - jacobson-regular-character-not-mf-without-property-t
---

Suppose `Rad_MF(St_20(R))!=St_20(R)`.  The first prerequisite, proved
without property `(T)`, says that `delta_e` of `EL_5(J)` is an MF character.
The second prerequisite forbids exactly that.  So the radical is the whole
group.

Comparison with the neighbouring routes:
* `property-t-free-leavitt-via-jacobson-head-root` needs the head killed in
  every norm-corona representation of `EL_5(J)`.  This route needs only the
  regular-trace models excluded, and that requirement follows from the
  older hole (`jacobson-regular-character-not-mf-via-head-collapse`).
* `property-t-free-el20-collapse-via-regular-character` targets the simple
  group `EL_20(R)`.  This route targets the Steinberg group, whose scalar
  kernel disappears on pullback to `EL_5(J)`.
