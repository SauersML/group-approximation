// Exact double-coset audit for the separately constrained finite packet.
// Run/compile only through MSI.  Arithmetic in the final ideal closure is
// over one odd prime and is only a redundant consistency check; the exact
// 44-dimensional ideal statement is transported from the integer H-corner
// calculation after the exact corner equality has been proved.

#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <deque>
#include <iostream>
#include <numeric>
#include <unordered_map>
#include <utility>
#include <vector>

using Matrix = std::uint64_t;
constexpr int N = 8;
constexpr std::int64_t PRIME = 1000003;

std::uint8_t row(Matrix x, int i) { return (x >> (8 * i)) & 255u; }
void set_row(Matrix& x, int i, std::uint8_t value) {
  x &= ~(Matrix(255) << (8 * i));
  x |= Matrix(value) << (8 * i);
}

Matrix identity() {
  Matrix x = 0;
  for (int i = 0; i < N; ++i) set_row(x, i, std::uint8_t(1u << i));
  return x;
}

Matrix multiply(Matrix left, Matrix right) {
  Matrix answer = 0;
  for (int i = 0; i < N; ++i) {
    std::uint8_t value = 0;
    auto mask = row(left, i);
    for (int j = 0; j < N; ++j)
      if ((mask >> j) & 1u) value ^= row(right, j);
    set_row(answer, i, value);
  }
  return answer;
}

Matrix transvection(int source, int target) {
  Matrix x = identity();
  set_row(x, target, row(x, target) ^ std::uint8_t(1u << source));
  return x;
}

Matrix swap_nodes(int a, int b) {
  Matrix x = identity();
  auto ra = row(x, a), rb = row(x, b);
  set_row(x, a, rb); set_row(x, b, ra);
  return x;
}

struct Normalized { Matrix representative; int phase; };

int main() {
  enum { q2, q4, q5, q6, u1, u2, u3, u4 };
  const Matrix one = identity();
  const std::vector<std::pair<int,int>> arrows = {
    {q5,q6},{q4,q5},{q2,q4},{q2,u2},{q4,u3},{q2,u3},
    {u1,u3},{u1,q5},{u1,q6},{u2,q6},{u2,q5},{u3,q6}
  };
  std::vector<Matrix> k_generators;
  for (auto [source,target] : arrows)
    k_generators.push_back(transvection(source,target));

  // Close K together with its signed character.
  std::unordered_map<Matrix,int> character;
  std::deque<Matrix> k_queue;
  character[one] = 0; k_queue.push_back(one);
  while (!k_queue.empty()) {
    Matrix current = k_queue.front(); k_queue.pop_front();
    for (int i = 0; i < int(k_generators.size()); ++i) {
      Matrix next = multiply(current, k_generators[i]);
      int phase = character[current] ^ (i < 3);
      auto [it, inserted] = character.emplace(next, phase);
      if (inserted) k_queue.push_back(next); else assert(it->second == phase);
    }
  }
  assert(character.size() == (1u << 15));

  const std::array<int,N> order = {q2,u1,q4,u2,u3,q5,q6,u4};
  const std::array<std::vector<int>,N> predecessors = {{
    {}, {q2}, {q2,q4,u1,u2}, {q2,q4,u1,u2,u3,q5},
    {}, {q2}, {q2,q4,u1}, {}
  }};
  auto normalize = [&](Matrix matrix) -> Normalized {
    Matrix multiplier = one;
    for (int target : order) {
      const auto& sources = predecessors[target];
      auto original = row(matrix,target), best = original;
      int best_mask = 0;
      for (int mask = 1; mask < (1 << int(sources.size())); ++mask) {
        auto candidate = original;
        for (int bit = 0; bit < int(sources.size()); ++bit)
          if ((mask >> bit) & 1) candidate ^= row(matrix,sources[bit]);
        if (candidate < best) { best = candidate; best_mask = mask; }
      }
      for (int bit = 0; bit < int(sources.size()); ++bit) if ((best_mask>>bit)&1) {
        set_row(matrix,target,row(matrix,target)^row(matrix,sources[bit]));
        set_row(multiplier,target,row(multiplier,target)^row(multiplier,sources[bit]));
      }
    }
    auto found = character.find(multiplier); assert(found != character.end());
    return {matrix, found->second};
  };

  Matrix j1 = swap_nodes(u1,u2), j2 = swap_nodes(u2,u3);
  Matrix b2 = transvection(q4,u2), b3 = transvection(q5,u3);
  Matrix g = multiply(j1,j2);
  std::vector<Matrix> packet_generators = k_generators;
  packet_generators.insert(packet_generators.end(), {j1,j2,b2,b3});

  // Enumerate K\P for P=<K,J1,J2,B2,B3>.
  std::vector<Matrix> reps = {one};
  std::unordered_map<Matrix,int> coset_index;
  coset_index[one] = 0;
  std::deque<int> queue = {0};
  while (!queue.empty()) {
    int state = queue.front(); queue.pop_front();
    for (Matrix generator : packet_generators) {
      Matrix next = normalize(multiply(reps[state],generator)).representative;
      auto [it, inserted] = coset_index.emplace(next,int(reps.size()));
      if (inserted) { reps.push_back(next); queue.push_back(it->second); }
    }
  }
  const int cosets = int(reps.size());

  // Twisted-compatible right-K orbits.
  std::vector<char> unseen(cosets,1);
  std::vector<std::vector<std::pair<int,int>>> compatible;
  std::vector<int> component(cosets,-1), component_sign(cosets,0);
  int double_cosets = 0, incompatible = 0;
  for (int start = 0; start < cosets; ++start) if (unseen[start]) {
    ++double_cosets;
    std::unordered_map<int,int> signs;
    std::deque<int> orbit_queue;
    signs[start]=0; orbit_queue.push_back(start);
    bool consistent=true;
    while (!orbit_queue.empty()) {
      int state=orbit_queue.front(); orbit_queue.pop_front();
      for (int i=0;i<int(k_generators.size());++i) {
        auto norm=normalize(multiply(reps[state],k_generators[i]));
        int target=coset_index.at(norm.representative);
        int target_sign=signs[state]^(i<3)^norm.phase;
        auto [it,inserted]=signs.emplace(target,target_sign);
        if (inserted) orbit_queue.push_back(target);
        else if (it->second!=target_sign) consistent=false;
      }
    }
    for (auto [state,sign] : signs) unseen[state]=0;
    if (!consistent) { ++incompatible; continue; }
    int index=int(compatible.size()); compatible.emplace_back();
    for (auto [state,sign] : signs) {
      compatible.back().push_back({state,sign});
      component[state]=index; component_sign[state]=sign;
    }
  }
  const int m=int(compatible.size());
  int identity_component=component[0];
  int h_component=component[coset_index.at(normalize(g).representative)];
  assert(identity_component>=0 && h_component>=0);

  // Exact signed-orbit multiplication, reduced modulo an odd prime.
  using Sparse = std::vector<std::pair<int,std::int64_t>>;
  std::vector<std::vector<Sparse>> table(m,std::vector<Sparse>(m));
  for (int i=0;i<m;++i) for (int j=0;j<m;++j) {
    std::unordered_map<int,std::int64_t> raw;
    for (auto [a,sa] : compatible[i]) for (auto [b,sb] : compatible[j]) {
      auto norm=normalize(multiply(reps[a],reps[b]));
      int state=coset_index.at(norm.representative);
      std::int64_t value=((sa^sb^norm.phase)?-1:1);
      raw[state]+=value;
    }
    std::unordered_map<int,std::int64_t> scalars;
    for (auto [state,value] : raw) if (value) {
      assert(component[state]>=0);
      std::int64_t scalar=component_sign[state]?-value:value;
      auto [it,inserted]=scalars.emplace(component[state],scalar);
      if (!inserted) assert(it->second==scalar);
    }
    for (auto [target,value] : scalars) {
      value%=PRIME; if(value<0)value+=PRIME;
      table[i][j].push_back({target,value});
    }
  }

  auto modpow=[](std::int64_t a,std::int64_t e){
    std::int64_t r=1;
    while(e){if(e&1)r=r*a%PRIME;a=a*a%PRIME;e>>=1;} return r;
  };
  std::vector<std::vector<std::int64_t>> echelon(m);
  std::deque<std::vector<std::int64_t>> pending;
  int ideal_dimension=0;
  auto add=[&](std::vector<std::int64_t> v){
    for(int p=0;p<m;++p) if(v[p] && !echelon[p].empty()) {
      auto factor=v[p];
      for(int q=p;q<m;++q) v[q]=(v[q]-factor*echelon[p][q])%PRIME;
      for(auto& x:v) if(x<0)x+=PRIME;
    }
    int p=0;while(p<m&&!v[p])++p;if(p==m)return false;
    auto inverse=modpow(v[p],PRIME-2);
    for(auto& x:v)x=x*inverse%PRIME;
    echelon[p]=v; pending.push_back(v); ++ideal_dimension; return true;
  };
  std::vector<std::int64_t> seed(m); seed[h_component]=1; add(seed);
  auto multiply_vector=[&](int basis,const std::vector<std::int64_t>& v,bool left){
    std::vector<std::int64_t> answer(m);
    for(int j=0;j<m;++j)if(v[j]) {
      const auto& product=left?table[basis][j]:table[j][basis];
      for(auto [target,value]:product)
        answer[target]=(answer[target]+v[j]*value)%PRIME;
    }
    return answer;
  };
  while(!pending.empty() && ideal_dimension<m) {
    auto v=std::move(pending.front());pending.pop_front();
    for(int i=0;i<m && ideal_dimension<m;++i) {
      add(multiply_vector(i,v,true));
      add(multiply_vector(i,v,false));
    }
  }

  std::cout << "K order / P:K / P order = " << character.size() << " "
            << cosets << " " << character.size()*std::uint64_t(cosets) << "\n";
  std::cout << "J1/J2/B2 already in H-coset count not audited separately\n";
  std::cout << "double cosets / compatible / incompatible = " << double_cosets
            << " " << m << " " << incompatible << "\n";
  std::cout << "identity component / h component = " << identity_component
            << " " << h_component << "\n";
  std::cout << "ideal dimension mod " << PRIME << " / full = "
            << ideal_dimension << " " << (ideal_dimension==m) << "\n";
}
