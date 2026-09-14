# Calibration of bal.g on presentations with known answers.
Read("bal.g");;
CAL := [
  ["x", "y", "TRIVIAL"],                       # trivial group
  ["xyXYY", "yxYXX", "TRIVIAL"],               # <x,y | x^y = y^2 ... > type: yx y^-1 = x^2, x y x^-1 = y^2 is trivial
  ["xxxYYYY", "xyxYXY", "TRIVIAL"],            # AK(3) = <x,y | x^3 = y^4, xyx = yxy>, trivial group (Havas--Ramsay)
  ["xxYYY", "xxYXYXYXYXYX", "FINITE"],         # <x,y | x^2 = y^3 = (xy)^5> as given to GAP earlier
  ["xxYYY", "yyyYXYXYXYXYX", "ANY"]            # sanity: another binary polyhedral-type presentation
];;
for c in CAL do
  Print(c[1], " ", c[2], " expect ", c[3], " -> ", Classify(c[1], c[2], 200000, 8), "\n");
od;
QUIT;
