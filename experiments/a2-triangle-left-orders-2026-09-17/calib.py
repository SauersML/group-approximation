from lo_sat import run
print("F2 radius4", run(2,[],4,4))
print("Z2 radius4", run(2,[(0,1,2,3)],4,4))   # a b a^-1 b^-1
print("Klein bottle radius4", run(2,[(0,1,2,1)],4,4))  # a b a^-1 b ; LO
print("Z/3 radius3", run(1,[(0,0,0)],3,3))
print("Promislow-like a^2 b^2 : <a,b | a b^2 a^-1 b^2, b a^2 b^-1 a^2>", run(2,[(0,1,1,2,1,1),(1,0,0,3,0,0)],5,5))
