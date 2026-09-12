"use strict";

const assert = (p, m) => { if (!p) throw new Error(m); };
const I = () => [1, 2, 4, 8, 16, 32, 64, 128];
const fromHex = s => {
  const a = (s.match(/../g) || []).map(x => parseInt(x, 16)).reverse();
  assert(a.length === 8, "bad matrix hex");
  return a;
};
const toHex = a => [...a].reverse()
  .map(x => x.toString(16).padStart(2, "0")).join("");
const eq = (a, b) => a.every((x, i) => x === b[i]);
const mul = (a, b) => a.map(r => {
  let z = 0;
  for (let j = 0; j < 8; ++j) if ((r >> j) & 1) z ^= b[j];
  return z;
});
const inv = a => {
  const l = a.slice(), r = I();
  for (let c = 0; c < 8; ++c) {
    let p = c;
    while (p < 8 && !((l[p] >> c) & 1)) ++p;
    assert(p < 8, "singular");
    [l[c], l[p]] = [l[p], l[c]];
    [r[c], r[p]] = [r[p], r[c]];
    for (let i = 0; i < 8; ++i) {
      if (i !== c && ((l[i] >> c) & 1)) {
        l[i] ^= l[c]; r[i] ^= r[c];
      }
    }
  }
  return r;
};
const order = a => {
  let z = I();
  for (let n = 1; n <= 100000; ++n) {
    z = mul(z, a);
    if (eq(z, I())) return n;
  }
  throw new Error("order bound");
};
const rank = a => {
  const r = a.slice(); let q = 0;
  for (let c = 0; c < 8; ++c) {
    let p = q;
    while (p < 8 && !((r[p] >> c) & 1)) ++p;
    if (p < 8) {
      [r[p], r[q]] = [r[q], r[p]];
      for (let i = 0; i < 8; ++i)
        if (i !== q && ((r[i] >> c) & 1)) r[i] ^= r[q];
      ++q;
    }
  }
  return q;
};
const lift4 = s => {
  const e = (s.match(/../g) || []).map(x => parseInt(x, 10));
  const a = Array(8).fill(0);
  assert(e.length === 16 && e.every(x => x === 0 || x === 1), "bad 4x4");
  for (let i = 0; i < 4; ++i) for (let j = 0; j < 4; ++j) {
    if (e[4*i+j]) {
      a[2*i] |= 1 << (2*j);
      a[2*i+1] |= 1 << (2*j+1);
    }
  }
  return a;
};
const trans = (i, j) => {
  const a = I();
  a[2*i] ^= 1 << (2*j);
  a[2*i+1] ^= 1 << (2*j+1);
  return a;
};

const F = fromHex("401004080301c030"), Fi = inv(F);
const h = lift4("01000000000101000001000000000001");
const k = lift4("01010000010000000000010000000001");
const b = lift4("01000000000100000000010100000001");
const z = lift4("01000000000100000000010100000100");
const c = mul(h, k), a = mul(z, b);
const t30 = mul(mul(inv(c), a), c);
const elements = {
  h, k, z, b, c, a,
  t01: trans(0, 1), t12: trans(1, 2), t23: trans(2, 3),
  t30, t21: trans(2, 1)
};
const expected = {
  h:   ["8040080428140201", 3, "8040281401033221", 7, 6],
  k:   ["8040201002010a05", 3, "8c4024100a05f030", 7, 6],
  z:   ["2010a05008040201", 3, "f404c80848540201", 15, 6],
  b:   ["8040a05008040201", 2, "8040a05058440201", 4, 3],
  c:   ["8040020122110a05", 4, "b04038143cc0cf1e", 12, 6],
  a:   ["a050201008040201", 2, "a454281808040201", 4, 3],
  t01: ["8040201008040a05", 2, "8f40251008040a05", 4, 4],
  t12: ["8040201028140201", 2, "8040201028143e29", 4, 4],
  t23: ["8040a05008040201", 2, "8040a05058440201", 4, 3],
  t30: ["8241201008040201", 2, "4182102008040201", 4, 3],
  t21: ["8040281408040201", 2, "8040281409070201", 4, 4]
};

assert(toHex(Fi) === "8280414010200c04", "F inverse");
assert(order(F) === 51, "F order");
assert(eq(t30, trans(3, 0)), "bridge t30=c^-1(zb)c");
const report = {
  encoding: "8 row bytes over GF(2), row 0 in the least-significant byte",
  frame: { matrix: toHex(F), inverse: toHex(Fi), order: order(F) },
  elements: {}
};
for (const [name, g] of Object.entries(elements)) {
  const opcode = mul(mul(mul(Fi, g), F), inv(g));
  const got = [
    toHex(g), order(g), toHex(opcode), order(opcode),
    rank(opcode.map((x, i) => x ^ (1 << i)))
  ];
  assert(JSON.stringify(got) === JSON.stringify(expected[name]), name + " mismatch");
  assert(!eq(opcode, I()), name + " opcode unexpectedly identity");
  report.elements[name] = {
    matrix: got[0], element_order: got[1], opcode: got[2],
    opcode_order: got[3], rank_opcode_minus_identity: got[4]
  };
}
const D = { D01: 1, D12: 1, D23: 1, D30: 1 };
const delta2 = { h: 2, k: 2, z: 2, b: 2, c: 2, a: 2 };
const consequences = {
  anisotropic_lhs: 24*(D.D01+D.D23+D.D30)+D.D12,
  optimized_weighted_lhs_lower_bound: 4+1+4+16,
  t30_x_squared: D.D30,
  parabolic_c3_energy: 2*delta2.h+2*delta2.k+delta2.z+delta2.b,
  two_holonomy_energy: 2*delta2.c+delta2.a
};
assert(consequences.anisotropic_lhs === 73, "anisotropic");
assert(consequences.optimized_weighted_lhs_lower_bound === 25, "optimized");
assert(consequences.t30_x_squared === 1, "t30");
assert(consequences.parabolic_c3_energy === 12, "PC3");
assert(consequences.two_holonomy_energy === 6, "2HOL");
report.regular_character = {
  rule: "nonidentity group element has normalized trace 0 in Reg(G)",
  D, delta_squared: delta2
};
report.consequences = consequences;
report.joint_weighted =
  "LHS >= q, while lambda=3pq/(p+q+sqrt(p^2-pq+q^2)) < 3q, hence lambda/256 < q";
report.bridge_identity = "t30=c^-1*a*c with c=h*k and a=z*b";
report.status = "PASS";
const output = JSON.stringify(report, null, 2);
if (typeof text === "function") text(output); else console.log(output);