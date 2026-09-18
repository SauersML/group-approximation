# Check for m11-linear-activity-self-replicating-group.
# X = {1..11}, P = M_11 = Stab_{M_12}(12) in its natural action; right actions throughout:
#   (x w)^g = x^(pi_g) w^(g|_x),  (gh)|_x = g|_x * h|_(x^pi_g).
# Automaton states (sections listed at letters 1..11, then the root permutation):
#   a = (a, 1, ..., 1) alpha           alpha = the 11-cycle (1,...,11) in M_11   (odometer)
#   b = (b, alpha, beta, 1, ..., 1)    beta  = an element of order 5 moving 1       (bounded, from w7-030)
#   c = (c, a, 1, ..., 1)              trivial root permutation                   (linear activity)
# R = < M_11, a, b, c >.  The script checks, on the finite levels X^n:
#   (1) the level-1 identities  a*alpha^-1 = a@1,  b*(alpha@2)^-1*(beta@3)^-1 = b@1,  c*(a@2)^-1 = c@1;
#   (2) M_11@x lies in <M_11, b>  (the w7-030 pair-projection certificate, recomputed);
#   (3) orders of a and c on X^n (infinite order of a, hence of c);
#   (4) the activity of c (number of non-trivial sections at level n) from the state table.
M12 := MathieuGroup(12);; P := Stabilizer(M12, 12);;
alpha := (1,2,3,4,5,6,7,8,9,10,11);;
Print("alpha in M_11: ", alpha in P, "\n");
beta := First(Elements(P), g -> Order(g) = 5 and 1^g <> 1);;
Print("beta = ", beta, "\n");
d := 11;;
# state table: name -> [ root permutation, list of section names ]
one := "1";;
T := rec();;
T.("1") := [ (), List([1..d], i -> "1") ];;
T.a := [ alpha, Concatenation(["a"], List([2..d], i -> "1")) ];;
T.alpha := [ alpha, List([1..d], i -> "1") ];;
T.beta := [ beta, List([1..d], i -> "1") ];;
T.b := [ (), Concatenation(["b", "alpha", "beta"], List([4..d], i -> "1")) ];;
T.c := [ (), Concatenation(["c", "a"], List([3..d], i -> "1")) ];;
# permutation of X^n (word x_1..x_n  <->  1 + sum (x_i - 1) d^(n-i)) induced by a state
cache := rec();;
LevelPerm := function(s, n)
  local key, pi, secs, N, img, x, rest, sub;
  if n = 0 then return (); fi;
  key := Concatenation(s, "_", String(n));
  if IsBound(cache.(key)) then return cache.(key); fi;
  pi := T.(s)[1]; secs := T.(s)[2]; N := d^(n-1);
  sub := List([1..d], x -> LevelPerm(secs[x], n-1));
  img := [];
  for x in [1..d] do for rest in [1..N] do
    img[(x-1)*N + rest] := (x^pi - 1)*N + rest^sub[x];
  od; od;
  cache.(key) := PermList(img);
  return cache.(key);
end;;
# g@x on X^n: acts as g on the subtree x X^(n-1), trivially elsewhere
At := function(g, x, n)   # g a permutation of X^(n-1)
  local N, img, y, rest;
  N := d^(n-1); img := [1..d^n];
  for rest in [1..N] do img[(x-1)*N + rest] := (x-1)*N + rest^g; od;
  return PermList(img);
end;;
FinPerm := function(p, n)  # finitary element acting by p at the root only
  local N, img, x, rest; N := d^(n-1); img := [];
  for x in [1..d] do for rest in [1..N] do img[(x-1)*N+rest] := (x^p-1)*N + rest; od; od;
  return PermList(img);
end;;
n := 4;;
A := LevelPerm("a", n);; B := LevelPerm("b", n);; C := LevelPerm("c", n);;
Print("(1) a*alpha^-1 = a@1 on X^4: ", A*FinPerm(alpha, n)^-1 = At(LevelPerm("a", n-1), 1, n), "\n");
Print("    b*(alpha@2)^-1*(beta@3)^-1 = b@1 on X^4: ",
  B * At(FinPerm(alpha, n-1), 2, n)^-1 * At(FinPerm(beta, n-1), 3, n)^-1 = At(LevelPerm("b", n-1), 1, n), "\n");
Print("    c*(a@2)^-1 = c@1 on X^4: ", C * At(LevelPerm("a", n-1), 2, n)^-1 = At(LevelPerm("c", n-1), 1, n), "\n");
# (2) the w7-030 certificate: h_a = b^-1 a b a^-1 (a in Stab_{M_11}(1)) generate M_11^10 on coordinates 2..11
P1 := Stabilizer(P, 1);;
sec := function(x) if x = 2 then return alpha; elif x = 3 then return beta; else return (); fi; end;;
D := DirectProduct(List([2..11], i -> P));; emb := List([1..10], i -> Embedding(D, i));;
hgen := function(g) return Product([1..10], i -> Image(emb[i], sec(i+1)^-1 * sec((i+1)^Inverse(g)))); end;;
gens := List(Elements(P1), hgen);;   # all h_a, a in Stab_{M_11}(1), lie in R
Print("(2) <h_a> = M_11^10 on coordinates 2..11: ", Size(Group(gens)) = Size(P)^10, "\n");
# (3) orders
for m in [1..4] do
  Print("(3) level ", m, ": order(a) = ", Order(LevelPerm("a", m)), "  order(c) = ", Order(LevelPerm("c", m)),
        "  order(b) = ", Order(LevelPerm("b", m)), "\n");
od;
# (4) activity of c: count non-trivial states at level n, by walking the state table
Activity := function(s, n)
  local cur, k, nxt, t;
  cur := [s];
  for k in [1..n] do
    nxt := [];
    for t in cur do Append(nxt, Filtered(T.(t)[2], u -> u <> "1")); od;
    cur := nxt;
  od;
  return Length(cur);
end;;
Print("(4) activity of c at levels 1..8: ", List([1..8], k -> Activity("c", k)), "\n");
Print("    activity of a, b at levels 1..8: ", List([1..8], k -> Activity("a", k)), " ", List([1..8], k -> Activity("b", k)), "\n");
QUIT;
