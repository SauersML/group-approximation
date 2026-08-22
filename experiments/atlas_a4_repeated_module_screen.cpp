#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <iomanip>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

using Matrix = std::uint64_t;

static constexpr Matrix identity() {
  Matrix value = 0;
  for (int i = 0; i < 8; ++i) value |= Matrix{1} << (8 * i + i);
  return value;
}

static Matrix multiply(Matrix left, Matrix right) {
  Matrix result = 0;
  for (int i = 0; i < 8; ++i) {
    std::uint8_t row = (left >> (8 * i)) & 255;
    std::uint8_t out = 0;
    for (int k = 0; k < 8; ++k)
      if ((row >> k) & 1) out ^= (right >> (8 * k)) & 255;
    result |= Matrix{out} << (8 * i);
  }
  return result;
}

static bool inverse(Matrix value, Matrix &result) {
  std::array<std::uint16_t, 8> rows{};
  for (int i = 0; i < 8; ++i)
    rows[i] = ((value >> (8 * i)) & 255) | (std::uint16_t{1} << (8 + i));
  for (int column = 0; column < 8; ++column) {
    int pivot = column;
    while (pivot < 8 && !((rows[pivot] >> column) & 1)) ++pivot;
    if (pivot == 8) return false;
    std::swap(rows[column], rows[pivot]);
    for (int row = 0; row < 8; ++row)
      if (row != column && ((rows[row] >> column) & 1)) rows[row] ^= rows[column];
  }
  result = 0;
  for (int i = 0; i < 8; ++i)
    result |= static_cast<Matrix>(rows[i] >> 8) << (8 * i);
  return true;
}

static std::vector<Matrix> nullspace(std::vector<Matrix> rows) {
  rows.erase(std::remove(rows.begin(), rows.end(), 0), rows.end());
  std::vector<int> pivots;
  int pivot_row = 0;
  for (int column = 0; column < 64 && pivot_row < static_cast<int>(rows.size()); ++column) {
    int found = pivot_row;
    while (found < static_cast<int>(rows.size()) && !((rows[found] >> column) & 1)) ++found;
    if (found == static_cast<int>(rows.size())) continue;
    std::swap(rows[pivot_row], rows[found]);
    for (int row = 0; row < static_cast<int>(rows.size()); ++row)
      if (row != pivot_row && ((rows[row] >> column) & 1)) rows[row] ^= rows[pivot_row];
    pivots.push_back(column);
    ++pivot_row;
  }
  std::array<bool, 64> is_pivot{};
  for (int pivot : pivots) is_pivot[pivot] = true;
  std::vector<Matrix> basis;
  for (int free = 0; free < 64; ++free) if (!is_pivot[free]) {
    Matrix vector = Matrix{1} << free;
    for (int row = 0; row < static_cast<int>(pivots.size()); ++row)
      if ((rows[row] >> free) & 1) vector |= Matrix{1} << pivots[row];
    basis.push_back(vector);
  }
  return basis;
}

static std::vector<Matrix> centralizer_basis(const std::vector<Matrix> &generators) {
  std::vector<Matrix> equations;
  for (Matrix generator : generators) {
    for (int i = 0; i < 8; ++i) for (int j = 0; j < 8; ++j) {
      Matrix row = 0;
      for (int k = 0; k < 8; ++k) {
        if ((generator >> (8 * k + j)) & 1) row ^= Matrix{1} << (8 * i + k);
        if ((generator >> (8 * i + k)) & 1) row ^= Matrix{1} << (8 * k + j);
      }
      equations.push_back(row);
    }
  }
  return nullspace(std::move(equations));
}

static std::vector<Matrix> units(const std::vector<Matrix> &basis) {
  assert(basis.size() < 31);
  std::vector<Matrix> result;
  Matrix value = 0;
  std::uint32_t previous_gray = 0;
  const std::uint32_t bound = std::uint32_t{1} << basis.size();
  for (std::uint32_t index = 1; index < bound; ++index) {
    std::uint32_t gray = index ^ (index >> 1);
    std::uint32_t changed = gray ^ previous_gray;
    value ^= basis[__builtin_ctz(changed)];
    previous_gray = gray;
    Matrix ignored;
    if (inverse(value, ignored)) result.push_back(value);
  }
  return result;
}

static bool cube_one(Matrix value) {
  return multiply(multiply(value, value), value) == identity();
}

static int matrix_order(Matrix value) {
  Matrix current = identity();
  for (int exponent = 1; exponent <= 4096; ++exponent) {
    current = multiply(current, value);
    if (current == identity()) return exponent;
  }
  return -1;
}

struct Data {
  std::string parity;
  std::vector<Matrix> h6, a8, source_i, source_t, fixed_i, fixed_t, conjugators;
  std::vector<std::pair<int, Matrix>> collision, q14;
};

struct Gauge {
  Matrix value;
  Matrix inverse;
  bool f4_linear_action;
};

static Matrix read_hex() {
  std::string token;
  std::cin >> token;
  return std::stoull(token, nullptr, 16);
}

static std::vector<Matrix> read_vector() {
  int count;
  std::cin >> count;
  std::vector<Matrix> values(count);
  for (Matrix &value : values) value = read_hex();
  return values;
}

static std::vector<std::pair<int, Matrix>> read_word() {
  int count;
  std::cin >> count;
  std::vector<std::pair<int, Matrix>> word;
  for (int index = 0; index < count; ++index) {
    std::string token;
    std::cin >> token;
    auto separator = token.find(':');
    word.emplace_back(std::stoi(token.substr(0, separator)),
                      std::stoull(token.substr(separator + 1), nullptr, 16));
  }
  return word;
}

static Data read_data() {
  Data data;
  std::string name;
  while (std::cin >> name && name != "END") {
    if (name == "PARITY") std::cin >> data.parity;
    else if (name == "H6") data.h6 = read_vector();
    else if (name == "A8") data.a8 = read_vector();
    else if (name == "SOURCE_H18_I") data.source_i = read_vector();
    else if (name == "SOURCE_H18_T") data.source_t = read_vector();
    else if (name == "FIXED_H18_I") data.fixed_i = read_vector();
    else if (name == "FIXED_H18_T") data.fixed_t = read_vector();
    else if (name == "COLLISION") data.collision = read_word();
    else if (name == "Q14") data.q14 = read_word();
    else if (name == "CONJUGATORS") data.conjugators = read_vector();
    else assert(false);
  }
  return data;
}

static Matrix evaluate(const std::vector<std::pair<int, Matrix>> &word,
                       Matrix conjugator, Matrix conjugator_inverse) {
  Matrix value = identity();
  for (auto [factor, letter] : word) {
    if (factor == 2) letter = multiply(multiply(conjugator_inverse, letter), conjugator);
    value = multiply(value, letter);
  }
  return value;
}

int main() {
  Data data = read_data();
  auto h6_units = units(centralizer_basis(data.h6));
  auto a8_units = units(centralizer_basis(data.a8));
  assert(h6_units.size() == 120960);
  assert(a8_units.size() == 6);

  std::unordered_set<Matrix> seen;
  seen.reserve(h6_units.size() * 2);
  Matrix field_structure = 0;
  for (Matrix value : a8_units)
    if (matrix_order(value) == 3) { field_structure = value; break; }
  assert(field_structure != 0);
  std::vector<Gauge> gauges;
  for (Matrix value : h6_units) if (!seen.count(value)) {
    Matrix value_inverse;
    assert(inverse(value, value_inverse));
    bool f4_linear_action = false;
    for (Matrix scalar : a8_units) {
      Matrix candidate = multiply(scalar, value);
      if (multiply(candidate, field_structure) == multiply(field_structure, candidate))
        f4_linear_action = true;
    }
    gauges.push_back({value, value_inverse, f4_linear_action});
    for (Matrix scalar : a8_units) seen.insert(multiply(scalar, value));
  }
  assert(seen.size() == h6_units.size());
  assert(gauges.size() == 20160);
  assert(std::count_if(gauges.begin(), gauges.end(),
                       [](const Gauge &gauge) { return gauge.f4_linear_action; }) == 180);
  assert(data.conjugators.size() == 1262);

  std::uint64_t packet = 0, collision_good = 0, q14_good = 0, joint = 0;
  std::uint64_t f4_packet = 0, f4_collision_good = 0, f4_q14_good = 0;
  Matrix first_escape = 0, first_escape_q14 = 0;
  Matrix first_escape_hub = 0;
  std::array<std::uint64_t, 4097> order_histogram{};
  for (Matrix base : data.conjugators) {
    Matrix base_inverse;
    assert(inverse(base, base_inverse));
    for (const Gauge &gauge : gauges) {
      Matrix conjugator = multiply(gauge.value, base);
      Matrix conjugator_inverse = multiply(base_inverse, gauge.inverse);
      bool good = true;
      for (Matrix source : data.source_i) {
        Matrix moved = multiply(multiply(conjugator_inverse, source), conjugator);
        for (Matrix fixed : data.fixed_t)
          if (!cube_one(multiply(moved, fixed))) { good = false; break; }
        if (!good) break;
      }
      if (!good) continue;
      for (Matrix source : data.source_t) {
        Matrix moved = multiply(multiply(conjugator_inverse, source), conjugator);
        for (Matrix fixed : data.fixed_i)
          if (!cube_one(multiply(fixed, moved))) { good = false; break; }
        if (!good) break;
      }
      if (!good) continue;
      ++packet;
      f4_packet += gauge.f4_linear_action;
      Matrix collision = evaluate(data.collision, conjugator, conjugator_inverse);
      Matrix q14 = evaluate(data.q14, conjugator, conjugator_inverse);
      bool cg = collision == identity(), qg = q14 == identity();
      collision_good += cg;
      q14_good += qg;
      joint += cg && qg;
      f4_collision_good += gauge.f4_linear_action && cg;
      f4_q14_good += gauge.f4_linear_action && qg;
      if (cg && first_escape == 0) {
        first_escape = conjugator;
        first_escape_q14 = q14;
        Matrix escape_inverse;
        assert(inverse(first_escape, escape_inverse));
        Matrix moved_hub = multiply(multiply(escape_inverse, data.a8[4]), first_escape);
        first_escape_hub = multiply(moved_hub, data.a8[4]);
        assert(!gauge.f4_linear_action);
        assert(!qg);
        if (data.parity == "inner") assert(first_escape_hub != identity());
      }
      int value_order = matrix_order(collision);
      assert(value_order > 0);
      ++order_histogram[value_order];
    }
  }
  assert(f4_packet == 2754);
  assert(f4_collision_good == 0);
  assert(f4_q14_good == (data.parity == "graph" ? 486 : 729));
  assert(first_escape != 0);
  assert(packet == 136728);
  assert(collision_good == 5184);
  assert(q14_good == (data.parity == "graph" ? 5184 : 10044));
  assert(joint == 0);
  assert(order_histogram[1] == 5184);
  assert(order_histogram[2] == 65448);
  assert(order_histogram[4] == 66096);
  assert(packet == order_histogram[1] + order_histogram[2] + order_histogram[4]);
  assert(first_escape == (data.parity == "graph" ? UINT64_C(0x401004080102c030)
                                                   : UINT64_C(0x401004080301c030)));
  std::cout << "{\n"
            << "  \"parity\": \"" << data.parity << "\",\n"
            << "  \"h6_centralizer_order\": " << h6_units.size() << ",\n"
            << "  \"a8_centralizer_order\": " << a8_units.size() << ",\n"
            << "  \"effective_gauges\": " << gauges.size() << ",\n"
            << "  \"f4_linear_gauges\": 180,\n"
            << "  \"f4_packet_crosscheck\": " << f4_packet << ",\n"
            << "  \"f4_collision_crosscheck\": " << f4_collision_good << ",\n"
            << "  \"f4_q14_crosscheck\": " << f4_q14_good << ",\n"
            << "  \"structured_candidates\": " << data.conjugators.size() * gauges.size() << ",\n"
            << "  \"packet_survivors\": " << packet << ",\n"
            << "  \"collision_survivors\": " << collision_good << ",\n"
            << "  \"q14_survivors\": " << q14_good << ",\n"
            << "  \"joint_survivors\": " << joint << ",\n"
            << "  \"first_collision_escape_conjugator\": \""
            << std::hex << std::setw(16) << std::setfill('0') << first_escape << "\",\n"
            << "  \"first_escape_q14_value\": \""
            << std::setw(16) << first_escape_q14 << "\",\n" << std::dec
            << "  \"first_escape_hub_value\": \""
            << std::hex << std::setw(16) << first_escape_hub << "\",\n" << std::dec
            << "  \"first_escape_hub_order\": " << matrix_order(first_escape_hub) << ",\n"
            << "  \"collision_orders\": {";
  bool first = true;
  for (int value_order = 1; value_order <= 4096; ++value_order)
    if (order_histogram[value_order]) {
      if (!first) std::cout << ", ";
      first = false;
      std::cout << "\"" << value_order << "\": " << order_histogram[value_order];
    }
  std::cout << "}\n}\n";
}
