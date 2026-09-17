from twisted_lift import *
T=[[0,1],[1,0]]; O=[[0,1],[1,1]]; I2=[[1,0],[0,1]]
# free group F2, S3 on F_2^2
run_case("F2 S3 both U", 2, 2, [], [T,O])
run_case("F2 S3 U=x only (sign-inflated)", 2, 2, [], [T,O], Usel=[0])
run_case("F2 S3 U=y only", 2, 2, [], [T,O], Usel=[1])
# F3 with trivial-on-third generator
run_case("F3 S3", 2, 3, [], [T,O,I2])
# trivial module sanity: F2, M=F_2 trivial -> Lackenby (n-u)u type
run_case("F2 trivial M", 2, 2, [], [[[1]],[[1]]])
