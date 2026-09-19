import GroupApproximation.Sofic.LiteralBaseP13RotationReplay

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem o12_32Trace1 :
    rotationWord (word (rotationSignedWord "YxzYXXzYXZXyxyxyZx")) =
      rotationWord (word (rotationSignedWord "")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxzYxzYXZXyxyxyZx")) :=
      rotationStep "YxzYXXzYXZXyxyxyZx" "YxzYxzYXZXyxyxyZx" "YxzY" 0 true
    _ = rotationWord (word (rotationSignedWord "YxzYxzYXZxxyxyxyZx")) :=
      rotationStep "YxzYxzYXZXyxyxyZx" "YxzYxzYXZxxyxyxyZx" "YxzYxzYXZ" 0 true
    _ = rotationWord (word (rotationSignedWord "YxzYxzXzxyxyxyxyZx")) :=
      rotationStep "YxzYxzYXZxxyxyxyZx" "YxzYxzXzxyxyxyxyZx" "YxzYxz" 5 true
    _ = rotationWord (word (rotationSignedWord "YxzYxzXzYXYXZx")) :=
      rotationStep "YxzYxzXzxyxyxyxyZx" "YxzYxzXzYXYXZx" "YxzYxzXz" 7 false
    _ = rotationWord (word (rotationSignedWord "YxzYxzXzYXXzxy")) :=
      rotationStep "YxzYxzXzYXYXZx" "YxzYxzXzYXXzxy" "YxzYxzXzYX" 5 true
    _ = rotationWord (word (rotationSignedWord "YxzYxzXzYxzxy")) :=
      rotationStep "YxzYxzXzYXXzxy" "YxzYxzXzYxzxy" "YxzYxzXzY" 0 true
    _ = rotationWord (word (rotationSignedWord "YxzYxZXzYxzxy")) :=
      rotationStep "YxzYxzXzYxzxy" "YxzYxZXzYxzxy" "YxzYx" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzYxZXZYxzxy")) :=
      rotationStep "YxzYxZXzYxzxy" "YxzYxZXZYxzxy" "YxzYxZX" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzYxxzxYxzxy")) :=
      rotationStep "YxzYxZXZYxzxy" "YxzYxxzxYxzxy" "YxzYx" 3 true
    _ = rotationWord (word (rotationSignedWord "YxzYXzxYxzxy")) :=
      rotationStep "YxzYxxzxYxzxy" "YxzYXzxYxzxy" "YxzY" 0 false
    _ = rotationWord (word (rotationSignedWord "YxzYXZxYxzxy")) :=
      rotationStep "YxzYXzxYxzxy" "YxzYXZxYxzxy" "YxzYX" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzXzxxzxy")) :=
      rotationStep "YxzYXZxYxzxy" "YxzXzxxzxy" "Yxz" 5 true
    _ = rotationWord (word (rotationSignedWord "YxzXzXzxy")) :=
      rotationStep "YxzXzxxzxy" "YxzXzXzxy" "YxzXz" 0 false
    _ = rotationWord (word (rotationSignedWord "YxZXzXzxy")) :=
      rotationStep "YxzXzXzxy" "YxZXzXzxy" "Yx" 2 false
    _ = rotationWord (word (rotationSignedWord "YxZXZXzxy")) :=
      rotationStep "YxZXzXzxy" "YxZXZXzxy" "YxZX" 2 false
    _ = rotationWord (word (rotationSignedWord "Yxxzzxy")) :=
      rotationStep "YxZXZXzxy" "Yxxzzxy" "Yx" 3 true
    _ = rotationWord (word (rotationSignedWord "Yxxxy")) :=
      rotationStep "Yxxzzxy" "Yxxxy" "Yxx" 2 false
    _ = rotationWord (word (rotationSignedWord "")) :=
      rotationStep "Yxxxy" "" "Y" 0 false

end

end GroupApproximation.LiteralBaseP13RotationReplay
