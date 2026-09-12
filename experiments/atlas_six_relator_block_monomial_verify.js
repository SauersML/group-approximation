"use strict";

const fs = require("fs");
const assert = require("assert");

const names = ["s_0", "s_11", "s_30", "s_44", "s_55", "c_19243"];
const identity = [1, 2, 4, 8];

function multiply(left, right) {
  return left.map((row) => {
    let value = 0;
    for (let column = 0; column < 4; column += 1) {
      if ((row >>> column) & 1) value ^= right[column];
    }
    return value;
  });
}

function inverse(matrix) {
  const left = matrix.slice();
  const right = identity.slice();
  for (let column = 0; column < 4; column += 1) {
    let pivot = column;
    while (pivot < 4 && !((left[pivot] >>> column) & 1)) pivot += 1;
    if (pivot === 4) return null;
    [left[column], left[pivot]] = [left[pivot], left[column]];
    [right[column], right[pivot]] = [right[pivot], right[column]];
    for (let row = 0; row < 4; row += 1) {
      if (row !== column && ((left[row] >>> column) & 1)) {
        left[row] ^= left[column];
        right[row] ^= right[column];
      }
    }
  }
  return right;
}

function rank(matrix) {
  const rows = matrix.slice();
  let pivot = 0;
  for (let column = 0; column < 4; column += 1) {
    let found = pivot;
    while (found < 4 && !((rows[found] >>> column) & 1)) found += 1;
    if (found === 4) continue;
    [rows[pivot], rows[found]] = [rows[found], rows[pivot]];
    for (let row = 0; row < 4; row += 1) {
      if (row !== pivot && ((rows[row] >>> column) & 1)) {
        rows[row] ^= rows[pivot];
      }
    }
    pivot += 1;
  }
  return pivot;
}

function parseMatrix(encoded) {
  const entries = encoded.match(/../g).map(Number);
  assert.strictEqual(entries.length, 16);
  const matrix = [];
  for (let row = 0; row < 4; row += 1) {
    let value = 0;
    for (let column = 0; column < 4; column += 1) {
      assert(entries[4 * row + column] === 0 ||
             entries[4 * row + column] === 1);
      if (entries[4 * row + column]) value |= 1 << column;
    }
    matrix.push(value);
  }
  return matrix;
}

function rowHex(matrix) {
  return matrix.map((row) => row.toString(16)).join("");
}

const source = JSON.parse(fs.readFileSync(
  __dirname + "/atlas-six-relator-relative-pieces.json", "utf8"
));
const words = names.map((name) =>
  source.relators[name].word.map(([factor, encoded]) =>
    [factor, parseMatrix(encoded)])
);

function evaluate(frame, frameInverse) {
  return words.map((word) => {
    let value = identity;
    for (const [factor, letter] of word) {
      const moved = factor === 1
        ? letter
        : multiply(multiply(frameInverse, letter), frame);
      value = multiply(value, moved);
    }
    const residual = value.map((row, index) => row ^ identity[index]);
    return { value, rank: rank(residual) };
  });
}

const expectedHistogram = {
  1: 1, 2: 3, 3: 13, 4: 176, 5: 1033, 6: 3333,
  7: 3343, 8: 2940, 9: 3099, 10: 2368, 11: 1800,
  12: 1101, 13: 613, 14: 247, 15: 77, 16: 12, 17: 1
};

const mask64 = (1n << 64n) - 1n;
const fnvPrime = 1099511628211n;
let fnv = 14695981039346656037n;
function feed(byte) {
  fnv ^= BigInt(byte);
  fnv = (fnv * fnvPrime) & mask64;
}

let invertible = 0;
let boundaryZero = 0;
let collisionZero = 0;
let collisionZeroMinimumBoundaryRank = Infinity;
let collisionZeroMinimumAttainers = 0;
let minimum = Infinity;
let minimizers = [];
const histogram = {};

for (let packed = 0; packed < 65536; packed += 1) {
  const frame = [
    packed & 15,
    (packed >>> 4) & 15,
    (packed >>> 8) & 15,
    (packed >>> 12) & 15
  ];
  const frameInverse = inverse(frame);
  if (frameInverse === null) continue;

  const values = evaluate(frame, frameInverse);
  const ranks = values.map((entry) => entry.rank);
  const boundaryRank = ranks.slice(0, 5).reduce((a, b) => a + b, 0);
  const totalRank = boundaryRank + ranks[5];

  feed(packed & 255);
  feed((packed >>> 8) & 255);
  for (const value of ranks) feed(value);

  invertible += 1;
  histogram[totalRank] = (histogram[totalRank] || 0) + 1;
  if (boundaryRank === 0) boundaryZero += 1;
  if (ranks[5] === 0) {
    collisionZero += 1;
    if (boundaryRank < collisionZeroMinimumBoundaryRank) {
      collisionZeroMinimumBoundaryRank = boundaryRank;
      collisionZeroMinimumAttainers = 1;
    } else if (boundaryRank === collisionZeroMinimumBoundaryRank) {
      collisionZeroMinimumAttainers += 1;
    }
  }
  if (totalRank < minimum) {
    minimum = totalRank;
    minimizers = [{ packed, frame, ranks, values }];
  } else if (totalRank === minimum) {
    minimizers.push({ packed, frame, ranks, values });
  }
}

assert.strictEqual(invertible, 20160);
assert.deepStrictEqual(histogram, expectedHistogram);
assert.strictEqual(minimum, 1);
assert.strictEqual(minimizers.length, 1);
assert.strictEqual(minimizers[0].packed, 0x8421);
assert.deepStrictEqual(minimizers[0].ranks, [0, 0, 0, 0, 0, 1]);
assert.deepStrictEqual(
  minimizers[0].values.map((entry) => rowHex(entry.value)),
  ["1248", "1248", "1248", "1248", "1248", "1a48"]
);
assert.deepStrictEqual(
  multiply(minimizers[0].values[5].value, minimizers[0].values[5].value),
  identity
);
assert.strictEqual(boundaryZero, 1);
assert.strictEqual(collisionZero, 4176);
assert.strictEqual(collisionZeroMinimumBoundaryRank, 3);
assert.strictEqual(collisionZeroMinimumAttainers, 10);
assert.strictEqual(
  "0x" + fnv.toString(16).padStart(16, "0"),
  "0x1b1a97fd388e6e75"
);

const report = {
  field: "GF(2)",
  relators: names,
  atomic_dimension: 4,
  candidate_binary_matrices: 65536,
  invertible_alignments: invertible,
  ordered_record_encoding:
    "packed matrix uint16 little-endian, then six one-byte residual ranks",
  ordered_record_fnv1a64: "0x" + fnv.toString(16).padStart(16, "0"),
  total_rank_histogram: histogram,
  minimum_total_residual_rank: minimum,
  minimizer_count: minimizers.length,
  unique_minimizer_packed_hex: "0x8421",
  unique_minimizer_row_hex: "1248",
  unique_minimizer_rank_vector: minimizers[0].ranks,
  unique_minimizer_word_values_row_hex:
    minimizers[0].values.map((entry) => rowHex(entry.value)),
  boundary_zero_alignments: boundaryZero,
  collision_zero_alignments: collisionZero,
  collision_zero_minimum_boundary_rank_sum:
    collisionZeroMinimumBoundaryRank,
  collision_zero_minimum_attainers: collisionZeroMinimumAttainers,
  arbitrary_multiplicity_consequence:
    "For every k and F in GL4(2) wr Sym(k), sum_w rank(pi_F(w)-I) >= k.",
  equality_frames:
    "Exactly the pure permutations of the identical four-dimensional summands.",
  status: "PASS"
};

console.log(JSON.stringify(report, null, 2));
