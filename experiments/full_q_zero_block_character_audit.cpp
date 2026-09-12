// Exact thin-normalizer audit for the full-Q separate-actor corner.
// Compile and run only through MSI.  The group calculation is over F_2;
// no floating point or random choices occur.

#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <deque>
#include <iomanip>
#include <iostream>
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
using Sparse = std::vector<std::pair<int,std::int64_t>>;

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
      for (int bit = 0; bit < int(sources.size()); ++bit)
        if ((best_mask >> bit) & 1) {
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

  std::vector<char> unseen(cosets,1);
  std::vector<std::vector<std::pair<int,int>>> compatible;
  std::vector<int> component(cosets,-1), component_sign(cosets,0);
  int incompatible = 0;
  for (int start = 0; start < cosets; ++start) if (unseen[start]) {
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
  const int identity_component=component[0];
  const int h_component=component[coset_index.at(normalize(g).representative)];
  assert(m==52 && identity_component>=0 && h_component>=0);

  std::vector<std::vector<Sparse>> table(m,std::vector<Sparse>(m));
  for (int i=0;i<m;++i) for (int j=0;j<m;++j) {
    std::unordered_map<int,std::int64_t> raw;
    for (auto [a,sa] : compatible[i]) for (auto [b,sb] : compatible[j]) {
      auto norm=normalize(multiply(reps[a],reps[b]));
      int state=coset_index.at(norm.representative);
      raw[state]+=((sa^sb^norm.phase)?-1:1);
    }
    std::unordered_map<int,std::int64_t> scalars;
    for (auto [state,value] : raw) if (value) {
      assert(component[state]>=0);
      std::int64_t scalar=component_sign[state]?-value:value;
      auto [it,inserted]=scalars.emplace(component[state],scalar);
      if (!inserted) assert(it->second==scalar);
    }
    for (auto [target,value] : scalars) table[i][j].push_back({target,value});
  }

  std::vector<int> thin, thick;
  std::vector<int> thin_state;
  for (int i=0;i<m;++i) {
    if (compatible[i].size()==1) {
      thin.push_back(i); thin_state.push_back(compatible[i][0].first);
    } else thick.push_back(i);
  }
  assert(thin.size()==8 && thick.size()==44);
  assert(std::find(thick.begin(),thick.end(),h_component)!=thick.end());

  // Exact support check: the 44-dimensional span of thick double-coset
  // sums is a two-sided ideal containing h.  Coefficients are ordinary
  // integers here, not reduced modulo a prime.
  std::vector<char> is_thick(m,0), is_thin(m,0);
  for (int i:thick) is_thick[i]=1;
  for (int i:thin) is_thin[i]=1;
  bool thick_span_is_ideal=true;
  for (int i=0;i<m;++i) for (int j:thick) {
    for (auto [target,value]:table[i][j])
      if (value && !is_thick[target]) thick_span_is_ideal=false;
    for (auto [target,value]:table[j][i])
      if (value && !is_thick[target]) thick_span_is_ideal=false;
  }

  // Rebuild the ideal generated by h modulo one odd prime, retaining the
  // actual product vectors.  A rank-52 certificate after adjoining the
  // eight thin unit vectors is an integer nonzero-minor certificate, hence
  // proves over Q that their subalgebra meets the exact 44-dimensional
  // ideal trivially.  Exact ideal dimension 44 is independently established
  // by the fraction-free relative-corner audit.
  auto modpow=[](std::int64_t a,std::int64_t exponent) {
    std::int64_t answer=1;
    while(exponent) {
      if(exponent&1) answer=answer*a%PRIME;
      a=a*a%PRIME; exponent>>=1;
    }
    return answer;
  };
  std::vector<std::vector<std::int64_t>> echelon(m);
  std::deque<std::vector<std::int64_t>> pending;
  int rank=0;
  auto add=[&](std::vector<std::int64_t> vector) {
    for(int pivot=0;pivot<m;++pivot)
      if(vector[pivot] && !echelon[pivot].empty()) {
        auto factor=vector[pivot];
        for(int column=pivot;column<m;++column)
          vector[column]=(vector[column]-factor*echelon[pivot][column])%PRIME;
        for(auto& value:vector) if(value<0) value+=PRIME;
      }
    int pivot=0; while(pivot<m && !vector[pivot]) ++pivot;
    if(pivot==m) return false;
    auto inverse=modpow(vector[pivot],PRIME-2);
    for(auto& value:vector) value=value*inverse%PRIME;
    echelon[pivot]=vector; pending.push_back(vector); ++rank; return true;
  };
  std::vector<std::int64_t> seed(m); seed[h_component]=1; add(seed);
  auto multiply_vector=[&](int basis,const std::vector<std::int64_t>& vector,
                           bool on_left) {
    std::vector<std::int64_t> answer(m);
    for(int other=0;other<m;++other) if(vector[other]) {
      const auto& product=on_left?table[basis][other]:table[other][basis];
      for(auto [target,value]:product) {
        value%=PRIME; if(value<0)value+=PRIME;
        answer[target]=(answer[target]+vector[other]*value)%PRIME;
      }
    }
    return answer;
  };
  while(!pending.empty() && rank<m) {
    auto vector=std::move(pending.front()); pending.pop_front();
    for(int basis=0;basis<m && rank<m;++basis) {
      add(multiply_vector(basis,vector,true));
      add(multiply_vector(basis,vector,false));
    }
  }
  const int ideal_rank=rank;
  const auto ideal_echelon=echelon;
  std::vector<int> quotient_basis;
  for(int index=0;index<m;++index)
    if(ideal_echelon[index].empty()) quotient_basis.push_back(index);
  assert(quotient_basis.size()==8);

  auto quotient_reduce=[&](std::vector<std::int64_t> vector) {
    for(int pivot=0;pivot<m;++pivot)
      if(vector[pivot] && !ideal_echelon[pivot].empty()) {
        auto factor=vector[pivot];
        for(int column=pivot;column<m;++column)
          vector[column]=(vector[column]-factor*ideal_echelon[pivot][column])%PRIME;
        for(auto& value:vector) if(value<0) value+=PRIME;
      }
    std::array<std::int64_t,8> answer{};
    for(int i=0;i<8;++i) answer[i]=vector[quotient_basis[i]];
    return answer;
  };

  std::array<std::array<std::array<std::int64_t,8>,8>,8> quotient_table{};
  for(int left=0;left<8;++left) for(int right=0;right<8;++right) {
    std::vector<std::int64_t> vector(m);
    for(auto [target,value]:table[quotient_basis[left]][quotient_basis[right]]) {
      value%=PRIME; if(value<0)value+=PRIME;
      vector[target]=(vector[target]+value)%PRIME;
    }
    quotient_table[left][right]=quotient_reduce(vector);
  }

  // Rank of the commutator equations for a central quotient element.
  std::vector<std::array<std::int64_t,8>> central_equations;
  for(int right=0;right<8;++right) for(int output=0;output<8;++output) {
    std::array<std::int64_t,8> equation{};
    for(int left=0;left<8;++left) {
      auto value=(quotient_table[left][right][output]
                 -quotient_table[right][left][output])%PRIME;
      if(value<0)value+=PRIME;
      equation[left]=value;
    }
    central_equations.push_back(equation);
  }
  int central_rank=0;
  for(int column=0;column<8;++column) {
    int pivot=central_rank;
    while(pivot<int(central_equations.size()) && !central_equations[pivot][column])
      ++pivot;
    if(pivot==int(central_equations.size())) continue;
    std::swap(central_equations[pivot],central_equations[central_rank]);
    auto inverse=modpow(central_equations[central_rank][column],PRIME-2);
    for(int j=column;j<8;++j)
      central_equations[central_rank][j]=
        central_equations[central_rank][j]*inverse%PRIME;
    for(int i=0;i<int(central_equations.size());++i)
      if(i!=central_rank && central_equations[i][column]) {
        auto factor=central_equations[i][column];
        for(int j=column;j<8;++j) {
          central_equations[i][j]=
            (central_equations[i][j]-factor*central_equations[central_rank][j])%PRIME;
          if(central_equations[i][j]<0) central_equations[i][j]+=PRIME;
        }
      }
    ++central_rank;
  }
  for(int basis:thin) {
    std::vector<std::int64_t> vector(m); vector[basis]=1; add(vector);
  }
  const int ideal_plus_thin_rank=rank;

  // The thin basis is the signed normalizer quotient.  Record its exact
  // multiplication, signs, and orders.
  std::unordered_map<int,int> thin_position;
  for (int i=0;i<int(thin.size());++i) thin_position[thin[i]]=i;
  std::array<std::array<std::pair<int,int>,8>,8> products{};
  int negative_products=0;
  for (int i=0;i<8;++i) for (int j=0;j<8;++j) {
    const auto& product=table[thin[i]][thin[j]];
    assert(product.size()==1 && is_thin[product[0].first]);
    products[i][j]={thin_position.at(product[0].first),int(product[0].second)};
    if (product[0].second<0) ++negative_products;
  }
  int thin_identity=thin_position.at(identity_component);
  std::array<int,8> orders{};
  for (int start=0;start<8;++start) {
    int state=start, scalar=1, order_value=1;
    while (state!=thin_identity || scalar!=1) {
      auto [next,step]=products[state][start]; state=next; scalar*=step;
      ++order_value; assert(order_value<=16);
    }
    orders[start]=order_value;
  }

  std::cout << "K order / P:K = " << character.size() << " " << cosets << "\n";
  std::cout << "compatible / incompatible = " << m << " " << incompatible << "\n";
  std::cout << "thin / thick / h-thick = " << thin.size() << " " << thick.size()
            << " " << is_thick[h_component] << "\n";
  std::cout << "thick span exact two-sided ideal = " << thick_span_is_ideal << "\n";
  std::cout << "ideal / ideal+thin rank mod " << PRIME << " = "
            << ideal_rank << " " << ideal_plus_thin_rank << "\n";
  std::cout << "quotient dimension / center-equation rank / center dimension = "
            << quotient_basis.size() << " " << central_rank << " "
            << quotient_basis.size()-central_rank << "\n";
  std::cout << "thin negative products = " << negative_products << "\n";
  std::cout << "thin orders =";
  for (int value:orders) std::cout << " " << value;
  std::cout << "\n";
  std::cout << "thin representatives (row bytes)\n";
  for (int position=0;position<8;++position) {
    Matrix x=reps[thin_state[position]];
    std::cout << position << ":";
    for (int i=0;i<N;++i)
      std::cout << (i?" ":" ") << std::hex << std::setw(2)
                << std::setfill('0') << int(row(x,i));
    std::cout << std::dec << "\n";
  }
  std::cout << "thin multiplication targets\n";
  for (int i=0;i<8;++i) {
    for (int j=0;j<8;++j) std::cout << (j?" ":"") << products[i][j].first;
    std::cout << "\n";
  }
}
