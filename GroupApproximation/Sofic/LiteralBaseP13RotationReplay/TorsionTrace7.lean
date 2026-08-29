import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.TorsionTrace6

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem torsionTrace7 :
    rotationWord (word (rotationSignedWord "YxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX")) =
      rotationWord (word (rotationSignedWord "XYXZxxYxzYXyxYxzYXyxyxyzX")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "XzxzXyxYxzYXyxYxzYXyxyxyzX")) := torsionTrace6
    _ = rotationWord (word (rotationSignedWord "XXZXXyxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "XzxzXyxYxzYXyxYxzYXyxyxyzX" "XXZXXyxYxzYXyxYxzYXyxyxyzX" "Xz" 3 false
    _ = rotationWord (word (rotationSignedWord "xZXXyxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "XXZXXyxYxzYXyxYxzYXyxyxyzX" "xZXXyxYxzYXyxYxzYXyxyxyzX" "" 0 true
    _ = rotationWord (word (rotationSignedWord "xZxyxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "xZXXyxYxzYXyxYxzYXyxyxyzX" "xZxyxYxzYXyxYxzYXyxyxyzX" "xZ" 0 true
    _ = rotationWord (word (rotationSignedWord "xzxyxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "xZxyxYxzYXyxYxzYXyxyxyzX" "xzxyxYxzYXyxYxzYXyxyxyzX" "x" 2 true
    _ = rotationWord (word (rotationSignedWord "XXzxyxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "xzxyxYxzYXyxYxzYXyxyxyzX" "XXzxyxYxzYXyxYxzYXyxyxyzX" "" 0 false
    _ = rotationWord (word (rotationSignedWord "XYXZxxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "XXzxyxYxzYXyxYxzYXyxyxyzX" "XYXZxxYxzYXyxYxzYXyxyxyzX" "X" 5 false

end

end GroupApproximation.LiteralBaseP13RotationReplay
