// Exploratory search for the two-generator Titz--Witzel permutation gate.
//
// Build: c++ -O3 -std=c++17 titz_witzel_two_generator_search.cpp -o tw2
// Run:   ./tw2 DIM STEPS SEED [cycle|exhaust-cycle]
//
// This file is an experiment, not a proof.  Permutations are image tables;
// multiplication p*q means composition p after q, so words act right-to-left.

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <utility>
#include <vector>

using Perm = std::vector<int>;
using Word = std::vector<int>; // 1=e, 2=u; a negative letter is an inverse.

static Word inverse_word(const Word &w) {
  Word r;
  r.reserve(w.size());
  for (auto it = w.rbegin(); it != w.rend(); ++it) r.push_back(-*it);
  return r;
}

static Word multiply(std::initializer_list<Word> words) {
  Word out;
  for (const auto &w : words) out.insert(out.end(), w.begin(), w.end());
  // Free reduction using e=e^-1 and e^2=1.
  Word reduced;
  for (int letter : out) {
    if (std::abs(letter) == 1) letter = 1;
    if (!reduced.empty() &&
        (reduced.back() == -letter || (letter == 1 && reduced.back() == 1)))
      reduced.pop_back();
    else
      reduced.push_back(letter);
  }
  return reduced;
}

static Word power_word(const Word &w, int k) {
  if (k < 0) return power_word(inverse_word(w), -k);
  Word out;
  for (int i = 0; i < k; ++i) out = multiply({out, w});
  return out;
}

struct Gate {
  Word c, rho, r_c2, r_rho, r_bxud, r_acdb, mark;

  Gate() {
    Word e{1}, u{2};
    Word h = multiply({u, e, inverse_word(u)});
    Word a = multiply({e, h, e});
    Word x = multiply({a, power_word(u, 2)});
    c = multiply({power_word(u, 2), a, power_word(u, 2)});
    Word f = multiply({inverse_word(x), h, x});
    Word d = multiply({e, inverse_word(a), f});
    Word s = multiply({f, a, f});
    rho = multiply({inverse_word(x), inverse_word(s), inverse_word(c)});
    Word b = multiply({rho, inverse_word(u), rho});
    r_c2 = power_word(c, 2);
    r_rho = multiply({power_word(rho, 2), inverse_word(e), inverse_word(u)});
    r_bxud = multiply({b, x, inverse_word(u), inverse_word(d)});
    r_acdb = multiply({a, c, d, b});
    mark = power_word(u, 8);
  }
};

static Perm inverse_perm(const Perm &p) {
  Perm q(p.size());
  for (int i = 0; i < (int)p.size(); ++i) q[p[i]] = i;
  return q;
}

static int defect(const Word &w, const Perm &e, const Perm &u,
                  const Perm &uinv) {
  int moved = 0;
  for (int start = 0; start < (int)e.size(); ++start) {
    int point = start;
    for (auto it = w.rbegin(); it != w.rend(); ++it) {
      if (*it == 1 || *it == -1) point = e[point];
      else if (*it == 2) point = u[point];
      else point = uinv[point];
    }
    moved += point != start;
  }
  return moved;
}

struct Score {
  int total;
  int mark;
  int dc, dr, db, da;
};

static Score score(const Gate &g, const Perm &e, const Perm &u) {
  Perm ui = inverse_perm(u);
  int dc = defect(g.r_c2, e, u, ui);
  int dr = defect(g.r_rho, e, u, ui);
  int db = defect(g.r_bxud, e, u, ui);
  int da = defect(g.r_acdb, e, u, ui);
  int mark = defect(g.mark, e, u, ui);
  return {dc + dr + db + da, mark, dc, dr, db, da};
}

static Perm random_perm(int n, std::mt19937_64 &rng) {
  Perm p(n);
  std::iota(p.begin(), p.end(), 0);
  std::shuffle(p.begin(), p.end(), rng);
  return p;
}

static Perm random_involution(int n, std::mt19937_64 &rng) {
  Perm e(n);
  std::iota(e.begin(), e.end(), 0);
  Perm order = random_perm(n, rng);
  std::bernoulli_distribution pair(0.8);
  for (int i = 0; i + 1 < n;) {
    if (pair(rng)) {
      int a = order[i], b = order[i + 1];
      e[a] = b; e[b] = a; i += 2;
    } else {
      ++i;
    }
  }
  return e;
}

// Conjugate e by a transposition.  This preserves e^2=1 and explores all
// involutions of the current cycle type.  A second move toggles two fixed
// points against one transposition, allowing the cycle type to change.
static void mutate_e(Perm &e, std::mt19937_64 &rng) {
  std::uniform_int_distribution<int> point(0, e.size() - 1);
  int a = point(rng), b = point(rng);
  while (a == b) b = point(rng);
  if ((rng() & 7) == 0) {
    if (e[a] == a && e[b] == b) {
      e[a] = b; e[b] = a; return;
    }
    if (e[a] == b) {
      e[a] = a; e[b] = b; return;
    }
  }
  int ea = e[a], eb = e[b];
  auto swap_label = [a,b](int x) { return x == a ? b : (x == b ? a : x); };
  e[a] = swap_label(eb);
  e[b] = swap_label(ea);
  if (ea != a && ea != b) e[ea] = b;
  if (eb != b && eb != a) e[eb] = a;
}

static void mutate_u(Perm &u, std::mt19937_64 &rng) {
  std::uniform_int_distribution<int> point(0, u.size() - 1);
  int a = point(rng), b = point(rng);
  while (a == b) b = point(rng);
  std::swap(u[a], u[b]);
}

struct ExhaustState {
  const Gate &gate;
  const Perm &u;
  long long count = 0;
  Score best{INT32_MAX, 0, 0, 0, 0, 0};
  Perm best_e;

  ExhaustState(const Gate &gate_in, const Perm &u_in)
      : gate(gate_in), u(u_in) {}
};

static void enumerate_involutions(Perm &e, std::vector<char> &used,
                                  ExhaustState &state) {
  int a = 0;
  while (a < (int)e.size() && used[a]) ++a;
  if (a == (int)e.size()) {
    ++state.count;
    Score candidate = score(state.gate, e, state.u);
    if (candidate.total < state.best.total) {
      state.best = candidate;
      state.best_e = e;
    }
    return;
  }
  used[a] = 1;
  e[a] = a;
  enumerate_involutions(e, used, state);
  for (int b = a + 1; b < (int)e.size(); ++b) if (!used[b]) {
    used[b] = 1;
    e[a] = b; e[b] = a;
    enumerate_involutions(e, used, state);
    used[b] = 0;
  }
  used[a] = 0;
}

int main(int argc, char **argv) {
  if (argc != 4 && argc != 5) {
    std::cerr << "usage: " << argv[0]
              << " DIM STEPS SEED [cycle|exhaust-cycle]\n";
    return 2;
  }
  int n = std::stoi(argv[1]);
  long long steps = std::stoll(argv[2]);
  uint64_t seed = std::stoull(argv[3]);
  std::mt19937_64 rng(seed);
  Gate gate;
  std::cerr << "word lengths: " << gate.r_c2.size() << ','
            << gate.r_rho.size() << ',' << gate.r_bxud.size() << ','
            << gate.r_acdb.size() << " mark=" << gate.mark.size() << "\n";

  std::string mode = argc == 5 ? argv[4] : "anneal";
  bool fixed_cycle = mode == "cycle" || mode == "exhaust-cycle";
  Perm e = random_involution(n, rng), u = random_perm(n, rng);
  if (fixed_cycle) for (int i = 0; i < n; ++i) u[i] = (i + 1) % n;
  if (mode == "exhaust-cycle") {
    Perm candidate_e(n);
    std::vector<char> used(n, 0);
    ExhaustState state(gate, u);
    enumerate_involutions(candidate_e, used, state);
    std::cout << "EXHAUST n=" << n << " count=" << state.count
              << " total=" << state.best.total << " defects="
              << state.best.dc << ',' << state.best.dr << ','
              << state.best.db << ',' << state.best.da
              << " mark=" << state.best.mark << "\ne=";
    for (int value : state.best_e) std::cout << value << ',';
    std::cout << "\n";
    return 0;
  }
  Score cur = score(gate, e, u), best = cur;
  Perm best_e = e, best_u = u;
  auto energy = [n](const Score &s) {
    // Enforce macroscopic mark but do not reward mark beyond n/2.
    return s.total + 40 * std::max(0, n / 2 - s.mark);
  };
  std::uniform_real_distribution<double> uniform(0.0, 1.0);
  for (long long step = 0; step < steps; ++step) {
    bool change_e = fixed_cycle || (rng() & 1);
    Perm old = change_e ? e : u;
    if (change_e) mutate_e(e, rng); else mutate_u(u, rng);
    Score candidate = score(gate, e, u);
    double progress = double(step) / std::max<long long>(1, steps - 1);
    double temp = 8.0 * (1.0 - progress) + 0.03;
    int delta = energy(candidate) - energy(cur);
    if (delta <= 0 || uniform(rng) < std::exp(-delta / temp)) {
      cur = candidate;
      if (candidate.mark >= n / 2 && candidate.total < best.total) {
        best = candidate; best_e = e; best_u = u;
        std::cout << "step=" << step << " total=" << best.total
                  << " defects=" << best.dc << ',' << best.dr << ','
                  << best.db << ',' << best.da << " mark=" << best.mark
                  << "\n";
      }
    } else {
      if (change_e) e = std::move(old); else u = std::move(old);
    }
  }
  std::cout << "FINAL n=" << n << " seed=" << seed
            << " total=" << best.total << " defects=" << best.dc << ','
            << best.dr << ',' << best.db << ',' << best.da
            << " mark=" << best.mark << "\ne=";
  for (int x : best_e) std::cout << x << ',';
  std::cout << "\nu=";
  for (int x : best_u) std::cout << x << ',';
  std::cout << "\n";
}
