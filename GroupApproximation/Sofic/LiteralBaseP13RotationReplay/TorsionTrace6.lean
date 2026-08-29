import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.TorsionTrace5

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem torsionTrace6 :
    rotationWord (word (rotationSignedWord "YxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX")) =
      rotationWord (word (rotationSignedWord "XzxzXyxYxzYXyxYxzYXyxyxyzX")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxZXyzyXyxYxzYXyxYxzYXyxyxyzX")) := torsionTrace5
    _ = rotationWord (word (rotationSignedWord "YxZXZYZXyxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "YxZXyzyXyxYxzYXyxYxzYXyxyxyzX" "YxZXZYZXyxYxzYXyxYxzYXyxyxyzX" "YxZX" 4 false
    _ = rotationWord (word (rotationSignedWord "YxxzxYZXyxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "YxZXZYZXyxYxzYXyxYxzYXyxyxyzX" "YxxzxYZXyxYxzYXyxYxzYXyxyxyzX" "Yx" 3 true
    _ = rotationWord (word (rotationSignedWord "YXzxYZXyxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "YxxzxYZXyxYxzYXyxYxzYXyxyxyzX" "YXzxYZXyxYxzYXyxYxzYXyxyxyzX" "Y" 0 false
    _ = rotationWord (word (rotationSignedWord "YXZxYZXyxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "YXzxYZXyxYxzYXyxYxzYXyxyxyzX" "YXZxYZXyxYxzYXyxYxzYXyxyxyzX" "YX" 2 false
    _ = rotationWord (word (rotationSignedWord "XzxZXyxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "YXZxYZXyxYxzYXyxYxzYXyxyxyzX" "XzxZXyxYxzYXyxYxzYXyxyxyzX" "" 5 true
    _ = rotationWord (word (rotationSignedWord "XzxzXyxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "XzxZXyxYxzYXyxYxzYXyxyxyzX" "XzxzXyxYxzYXyxYxzYXyxyxyzX" "Xzx" 2 true

end

end GroupApproximation.LiteralBaseP13RotationReplay
