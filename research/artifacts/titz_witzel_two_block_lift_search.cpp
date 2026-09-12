// Exhaustive search of two-block lifts of the two-generator Titz--Witzel gate.
//
// Build:
//   c++ -O3 -std=c++17 -Wall -Wextra -pedantic \
//     research/artifacts/titz_witzel_two_block_lift_search.cpp -o /tmp/tw2block
// Run:
//   /tmp/tw2block exhaust MAX_FIBRE_SIZE
//   /tmp/tw2block anneal FIBRE_SIZE STEPS SEED
//
// Every fixed-point-free involution e is conjugate to the pure swap of two
// equally sized blocks.  This program studies the extra requirement that u
// also swaps those blocks.  In that normal form
//
//   e(x,0)=(x,1), e(x,1)=(x,0),
//   u(x,0)=(A(x),1), u(x,1)=(B(x),0).
//
// Simultaneous fibre conjugacy permits A to be replaced by one canonical
// representative of each cycle type.  Enumerating every B then covers every
// pair (A,B) up to conjugacy.  The "transitive" rows additionally require
// <A,B> to act transitively on the fibre, excluding padded disjoint packets.
// This is a finite experiment, not an asymptotic impossibility proof.

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <vector>

using Perm = std::vector<int>;

static Perm identity(int n) {
  Perm p(n);
  std::iota(p.begin(), p.end(), 0);
  return p;
}

// Product left*right means left after right.
static Perm product(const Perm &left, const Perm &right) {
  Perm out(left.size());
  for (int i = 0; i < static_cast<int>(left.size()); ++i)
    out[i] = left[right[i]];
  return out;
}

static Perm inverse(const Perm &p) {
  Perm out(p.size());
  for (int i = 0; i < static_cast<int>(p.size()); ++i) out[p[i]] = i;
  return out;
}

static Perm power(Perm p, int exponent) {
  Perm out = identity(static_cast<int>(p.size()));
  while (exponent > 0) {
    if (exponent & 1) out = product(out, p);
    p = product(p, p);
    exponent >>= 1;
  }
  return out;
}

static int support(const Perm &p) {
  int out = 0;
  for (int i = 0; i < static_cast<int>(p.size()); ++i) out += p[i] != i;
  return out;
}

struct Score {
  int dc = 0, dr = 0, dp = 0, dj = 0, mark = 0;
  int total() const { return dc + dr + dp + dj; }
  int maximum() const { return std::max({dc, dr, dp, dj}); }
};

static Score score(const Perm &e, const Perm &u) {
  const Perm ui = inverse(u);
  const Perm u2 = product(u, u);
  const Perm h = product(product(u, e), ui);
  const Perm a = product(product(e, h), e);
  const Perm x = product(a, u2);
  const Perm c = product(product(u2, a), u2);
  const Perm xi = inverse(x);
  const Perm f = product(product(xi, h), x);
  const Perm d = product(product(e, inverse(a)), f);
  const Perm s = product(product(f, a), f);
  const Perm rho = product(product(xi, inverse(s)), inverse(c));
  const Perm beta = product(product(rho, e), inverse(rho));
  const Perm p = product(beta, a);

  const Perm rc = product(c, c);
  const Perm rr = product(product(product(rho, rho), e), ui);
  const Perm rp = product(product(p, u), inverse(d));
  const Perm rj = product(product(product(p, u), p), c);
  return {support(rc), support(rr), support(rp), support(rj),
          support(power(u, 8))};
}

static void partitions(int remaining, int largest, std::vector<int> &current,
                       std::vector<std::vector<int>> &out) {
  if (remaining == 0) {
    out.push_back(current);
    return;
  }
  for (int part = std::min(remaining, largest); part >= 1; --part) {
    current.push_back(part);
    partitions(remaining - part, part, current, out);
    current.pop_back();
  }
}

static Perm cycle_type_representative(const std::vector<int> &parts) {
  int n = std::accumulate(parts.begin(), parts.end(), 0);
  Perm out = identity(n);
  int first = 0;
  for (int length : parts) {
    for (int i = 0; i < length; ++i)
      out[first + i] = first + ((i + 1) % length);
    first += length;
  }
  return out;
}

static bool transitive(const Perm &a, const Perm &b) {
  const int n = static_cast<int>(a.size());
  const Perm ai = inverse(a), bi = inverse(b);
  std::vector<char> seen(n, 0);
  std::vector<int> queue{0};
  seen[0] = 1;
  for (std::size_t head = 0; head < queue.size(); ++head) {
    int x = queue[head];
    for (int y : {a[x], ai[x], b[x], bi[x]}) {
      if (!seen[y]) {
        seen[y] = 1;
        queue.push_back(y);
      }
    }
  }
  return static_cast<int>(queue.size()) == n;
}

static std::string table(const Perm &p) {
  std::string out;
  for (int x : p) {
    if (!out.empty()) out += ',';
    out += std::to_string(x);
  }
  return out;
}

struct Best {
  bool set = false;
  Score score;
  Perm a, b;
};

static bool better_total(const Score &candidate, const Score &old) {
  // First minimize total defect/mark, then maximum defect/mark, using exact
  // cross multiplication.  Larger mark wins the remaining tie.
  auto lhs_total = int64_t(candidate.total()) * old.mark;
  auto rhs_total = int64_t(old.total()) * candidate.mark;
  if (lhs_total != rhs_total) return lhs_total < rhs_total;
  auto lhs_max = int64_t(candidate.maximum()) * old.mark;
  auto rhs_max = int64_t(old.maximum()) * candidate.mark;
  if (lhs_max != rhs_max) return lhs_max < rhs_max;
  return candidate.mark > old.mark;
}

static bool better_max(const Score &candidate, const Score &old) {
  auto lhs_max = int64_t(candidate.maximum()) * old.mark;
  auto rhs_max = int64_t(old.maximum()) * candidate.mark;
  if (lhs_max != rhs_max) return lhs_max < rhs_max;
  auto lhs_total = int64_t(candidate.total()) * old.mark;
  auto rhs_total = int64_t(old.total()) * candidate.mark;
  if (lhs_total != rhs_total) return lhs_total < rhs_total;
  return candidate.mark > old.mark;
}

static void consider(Best &best, const Score &candidate, const Perm &a,
                     const Perm &b, bool by_maximum) {
  if (candidate.mark == 0) return;
  if (!best.set || (by_maximum ? better_max(candidate, best.score)
                               : better_total(candidate, best.score))) {
    best = {true, candidate, a, b};
  }
}

static void print_best(const char *label, const Best &best) {
  std::cout << ' ' << label << '=';
  if (!best.set) {
    std::cout << "none";
    return;
  }
  const Score &s = best.score;
  std::cout << s.dc << ',' << s.dr << ',' << s.dp << ',' << s.dj
            << "/mark" << s.mark << "/A=" << table(best.a)
            << "/B=" << table(best.b);
}

static void exhaustive_search(int maximum) {
  for (int m = 1; m <= maximum; ++m) {
    std::vector<std::vector<int>> types;
    std::vector<int> current;
    partitions(m, m, current, types);

    uint64_t normalized_pairs = 0, transitive_pairs = 0;
    uint64_t marked_pairs = 0, marked_transitive_pairs = 0;
    Best total_all, max_all, total_transitive, max_transitive;

    Perm b = identity(m);
    for (const auto &type : types) {
      const Perm a = cycle_type_representative(type);
      b = identity(m);
      do {
        ++normalized_pairs;
        const bool is_transitive = transitive(a, b);
        transitive_pairs += is_transitive;

        Perm e(2 * m), u(2 * m);
        for (int x = 0; x < m; ++x) {
          e[x] = m + x;
          e[m + x] = x;
          u[x] = m + a[x];
          u[m + x] = b[x];
        }
        const Score candidate = score(e, u);
        marked_pairs += candidate.mark != 0;
        marked_transitive_pairs += is_transitive && candidate.mark != 0;
        consider(total_all, candidate, a, b, false);
        consider(max_all, candidate, a, b, true);
        if (is_transitive) {
          consider(total_transitive, candidate, a, b, false);
          consider(max_transitive, candidate, a, b, true);
        }
      } while (std::next_permutation(b.begin(), b.end()));
    }

    std::cout << "m=" << m << " types=" << types.size()
              << " normalized_pairs=" << normalized_pairs
              << " transitive=" << transitive_pairs
              << " marked=" << marked_pairs
              << " marked_transitive=" << marked_transitive_pairs;
    print_best("best_total", total_all);
    print_best("best_max", max_all);
    print_best("best_total_transitive", total_transitive);
    print_best("best_max_transitive", max_transitive);
    std::cout << '\n';
  }
}

static Perm random_permutation(int n, std::mt19937_64 &rng) {
  Perm out = identity(n);
  std::shuffle(out.begin(), out.end(), rng);
  return out;
}

static void mutate(Perm &permutation, std::mt19937_64 &rng) {
  std::uniform_int_distribution<int> point(0, permutation.size() - 1);
  int first = point(rng), second = point(rng);
  while (first == second) second = point(rng);
  std::swap(permutation[first], permutation[second]);
}

static Score score_fibres(const Perm &a, const Perm &b) {
  const int m = static_cast<int>(a.size());
  Perm e(2 * m), u(2 * m);
  for (int x = 0; x < m; ++x) {
    e[x] = m + x;
    e[m + x] = x;
    u[x] = m + a[x];
    u[m + x] = b[x];
  }
  return score(e, u);
}

static void anneal(int m, uint64_t steps, uint64_t seed) {
  std::mt19937_64 rng(seed);
  Perm a = random_permutation(m, rng), b = random_permutation(m, rng);
  while (!transitive(a, b)) {
    a = random_permutation(m, rng);
    b = random_permutation(m, rng);
  }
  Score current = score_fibres(a, b), best;
  Perm best_a, best_b;
  bool have_best = false;
  auto energy = [m](const Score &candidate) {
    // Demand that u^8 move at least half of the full 2m-point carrier.
    return candidate.total() + 40 * std::max(0, m - candidate.mark);
  };
  std::uniform_real_distribution<double> uniform(0.0, 1.0);
  for (uint64_t step = 0; step < steps; ++step) {
    const bool change_a = rng() & 1;
    Perm old = change_a ? a : b;
    if (change_a)
      mutate(a, rng);
    else
      mutate(b, rng);
    if (!transitive(a, b)) {
      if (change_a) a = std::move(old); else b = std::move(old);
      continue;
    }
    Score candidate = score_fibres(a, b);
    const double progress = double(step) / std::max<uint64_t>(1, steps - 1);
    const double temperature = 10.0 * (1.0 - progress) + 0.03;
    const int delta = energy(candidate) - energy(current);
    if (delta <= 0 || uniform(rng) < std::exp(-delta / temperature)) {
      current = candidate;
      if (candidate.mark >= m &&
          (!have_best || better_total(candidate, best))) {
        have_best = true;
        best = candidate;
        best_a = a;
        best_b = b;
      }
    } else if (change_a) {
      a = std::move(old);
    } else {
      b = std::move(old);
    }
  }
  std::cout << "ANNEAL m=" << m << " steps=" << steps << " seed=" << seed;
  if (!have_best) {
    std::cout << " no-marked-state\n";
    return;
  }
  std::cout << " defects=" << best.dc << ',' << best.dr << ',' << best.dp
            << ',' << best.dj << " mark=" << best.mark
            << " A=" << table(best_a) << " B=" << table(best_b) << '\n';
}

int main(int argc, char **argv) {
  if (argc == 3 && std::string(argv[1]) == "exhaust") {
    exhaustive_search(std::stoi(argv[2]));
    return 0;
  }
  if (argc == 5 && std::string(argv[1]) == "anneal") {
    anneal(std::stoi(argv[2]), std::stoull(argv[3]), std::stoull(argv[4]));
    return 0;
  }
  std::cerr << "usage: " << argv[0]
            << " exhaust MAX_FIBRE_SIZE\n       " << argv[0]
            << " anneal FIBRE_SIZE STEPS SEED\n";
  return 2;
}
