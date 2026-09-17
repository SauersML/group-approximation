LCF := function(n, shifts)
  local E, i, j, s;
  E := List([0..n-1], i -> [i+1, ((i+1) mod n)+1]);
  for i in [0..n-1] do
    s := shifts[(i mod Length(shifts))+1];
    j := (i+s) mod n;
    if i < j then Add(E, [i+1, j+1]); fi;
  od;
  return E;
end;
petersen := Concatenation(List([0..4], i->[i+1, ((i+1) mod 5)+1]), List([0..4], i->[i+6, ((i+2) mod 5)+6]), List([1..5], i->[i, i+5]));
k4 := [[1,2],[1,3],[1,4],[2,3],[2,4],[3,4]];
k5 := Combinations([1..5], 2);
k44 := Cartesian([1..4],[5..8]);
moebiuskantor := LCF(16, [5,-5]);
pappus := LCF(18, [5,7,-7,7,-7,-5]);
desargues := LCF(20, [5,-5,9,-9]);
tutte8cage := LCF(30, [-13,-9,7,-7,9,13]);
