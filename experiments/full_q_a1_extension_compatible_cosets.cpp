// Exact compatible-double-coset screen after adjoining A1=x47(a1).
// Compile and run only through MSI.  This intentionally stops before Hecke
// multiplication so that the first extension signal is obtained quickly.

#include <array>
#include <cassert>
#include <cstdint>
#include <deque>
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
    std::uint8_t value = 0, mask = row(left, i);
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

  std::unordered_map<Matrix,int> character;
  std::deque<Matrix> k_queue;
  character[one] = 0; k_queue.push_back(one);
  while (!k_queue.empty()) {
    Matrix current = k_queue.front(); k_queue.pop_front();
    for (int i = 0; i < int(k_generators.size()); ++i) {
      Matrix next = multiply(current,k_generators[i]);
      int phase = character[current] ^ (i < 3);
      auto [it,inserted] = character.emplace(next,phase);
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
    return {matrix,found->second};
  };

  Matrix j1=swap_nodes(u1,u2), j2=swap_nodes(u2,u3);
  Matrix b2=transvection(q4,u2), b3=transvection(q5,u3);
  Matrix a1=transvection(u1,q4);
  std::vector<Matrix> generators=k_generators;
  generators.insert(generators.end(),{j1,j2,b2,b3,a1});

  std::vector<Matrix> reps={one};
  std::unordered_map<Matrix,int> index;
  index[one]=0;
  std::deque<int> queue={0};
  while(!queue.empty()) {
    int state=queue.front();queue.pop_front();
    for(Matrix generator:generators) {
      Matrix next=normalize(multiply(reps[state],generator)).representative;
      auto [it,inserted]=index.emplace(next,int(reps.size()));
      if(inserted){reps.push_back(next);queue.push_back(it->second);}
    }
  }

  std::vector<char> unseen(reps.size(),1);
  std::vector<std::vector<std::pair<int,int>>> compatible_orbits;
  std::vector<int> component(reps.size(),-1), component_sign(reps.size(),0);
  int doubles=0,compatible=0,incompatible=0;
  std::uint64_t compatible_states=0;
  int largest_compatible=0;
  for(int start=0;start<int(reps.size());++start) if(unseen[start]) {
    ++doubles;
    std::unordered_map<int,int> signs;
    std::deque<int> orbit;
    signs[start]=0;orbit.push_back(start);
    bool consistent=true;
    while(!orbit.empty()) {
      int state=orbit.front();orbit.pop_front();
      for(int i=0;i<int(k_generators.size());++i) {
        auto norm=normalize(multiply(reps[state],k_generators[i]));
        int target=index.at(norm.representative);
        int target_sign=signs[state]^(i<3)^norm.phase;
        auto [it,inserted]=signs.emplace(target,target_sign);
        if(inserted)orbit.push_back(target);
        else if(it->second!=target_sign)consistent=false;
      }
    }
    for(auto [state,_sign]:signs)unseen[state]=0;
    if(consistent) {
      ++compatible;
      compatible_states += signs.size();
      if (int(signs.size()) > largest_compatible)
        largest_compatible = int(signs.size());
      int compatible_index=int(compatible_orbits.size());
      compatible_orbits.emplace_back();
      for(auto [state,sign]:signs) {
        compatible_orbits.back().push_back({state,sign});
        component[state]=compatible_index;
        component_sign[state]=sign;
      }
    } else ++incompatible;
  }

  int corner_dimension=int(compatible_orbits.size());
  int identity_component=component[0];
  Matrix g=multiply(j1,j2);
  int g_state=index.at(normalize(g).representative);
  int h_component=component[g_state];
  assert(identity_component>=0 && h_component>=0);

  using Sparse=std::vector<std::pair<int,std::int64_t>>;
  std::vector<std::vector<Sparse>> table(
      corner_dimension,std::vector<Sparse>(corner_dimension));
  for(int i=0;i<corner_dimension;++i) for(int j=0;j<corner_dimension;++j) {
    std::unordered_map<int,std::int64_t> raw;
    for(auto [left_state,left_sign]:compatible_orbits[i])
      for(auto [right_state,right_sign]:compatible_orbits[j]) {
        auto norm=normalize(multiply(reps[left_state],reps[right_state]));
        int state=index.at(norm.representative);
        std::int64_t value=(left_sign^right_sign^norm.phase)?-1:1;
        raw[state]+=value;
      }
    std::unordered_map<int,std::int64_t> scalars;
    for(auto [state,value]:raw) if(value) {
      assert(component[state]>=0);
      std::int64_t scalar=component_sign[state]?-value:value;
      auto [it,inserted]=scalars.emplace(component[state],scalar);
      if(!inserted)assert(it->second==scalar);
    }
    for(auto [target,value]:scalars) {
      value%=PRIME;if(value<0)value+=PRIME;
      table[i][j].push_back({target,value});
    }
  }

  auto modpow=[](std::int64_t a,std::int64_t exponent) {
    std::int64_t answer=1;
    while(exponent) {
      if(exponent&1)answer=answer*a%PRIME;
      a=a*a%PRIME;exponent>>=1;
    }
    return answer;
  };
  std::vector<std::vector<std::int64_t>> echelon(corner_dimension);
  std::deque<std::vector<std::int64_t>> pending;
  int ideal_dimension=0;
  auto add_vector=[&](std::vector<std::int64_t> vector) {
    for(int pivot=0;pivot<corner_dimension;++pivot)
      if(vector[pivot]&&!echelon[pivot].empty()) {
        auto factor=vector[pivot];
        for(int column=pivot;column<corner_dimension;++column) {
          vector[column]=(vector[column]-factor*echelon[pivot][column])%PRIME;
          if(vector[column]<0)vector[column]+=PRIME;
        }
      }
    int pivot=0;
    while(pivot<corner_dimension&&!vector[pivot])++pivot;
    if(pivot==corner_dimension)return false;
    auto inverse=modpow(vector[pivot],PRIME-2);
    for(auto& value:vector)value=value*inverse%PRIME;
    echelon[pivot]=vector;pending.push_back(vector);++ideal_dimension;
    return true;
  };
  auto multiply_vector=[&](int basis,const std::vector<std::int64_t>& vector,
                           bool left) {
    std::vector<std::int64_t> answer(corner_dimension);
    for(int j=0;j<corner_dimension;++j)if(vector[j]) {
      const auto& product=left?table[basis][j]:table[j][basis];
      for(auto [target,value]:product)
        answer[target]=(answer[target]+vector[j]*value)%PRIME;
    }
    return answer;
  };
  std::vector<std::int64_t> seed(corner_dimension);seed[h_component]=1;
  add_vector(seed);
  while(!pending.empty()&&ideal_dimension<corner_dimension) {
    auto vector=std::move(pending.front());pending.pop_front();
    for(int basis=0;basis<corner_dimension&&ideal_dimension<corner_dimension;++basis) {
      add_vector(multiply_vector(basis,vector,true));
      add_vector(multiply_vector(basis,vector,false));
    }
  }

  std::cout << "extension index / group order = " << reps.size() << " "
            << std::uint64_t(reps.size())*character.size() << "\n";
  std::cout << "double cosets / compatible / incompatible = "
            << doubles << " " << compatible << " " << incompatible << "\n";
  std::cout << "compatible states / largest compatible orbit = "
            << compatible_states << " " << largest_compatible << "\n";
  std::cout << "identity / h component = " << identity_component << " "
            << h_component << "\n";
  std::cout << "h ideal dimension mod " << PRIME << " / corner = "
            << ideal_dimension << " " << corner_dimension << "\n";
}
