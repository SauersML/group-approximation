import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.TorsionTrace4

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem torsionTrace5 :
    rotationWord (word (rotationSignedWord "YxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX")) =
      rotationWord (word (rotationSignedWord "YxZXyzyXyxYxzYXyxYxzYXyxyxyzX")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxzXYZyzYXyxYxzYXyxYxzYXyxyxyzX")) := torsionTrace4
    _ = rotationWord (word (rotationSignedWord "YxzXYzyzYXyxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "YxzXYZyzYXyxYxzYXyxYxzYXyxyxyzX" "YxzXYzyzYXyxYxzYXyxYxzYXyxyxyzX" "YxzXY" 2 true
    _ = rotationWord (word (rotationSignedWord "YxzXYYZYYXyxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "YxzXYzyzYXyxYxzYXyxYxzYXyxyxyzX" "YxzXYYZYYXyxYxzYXyxYxzYXyxyxyzX" "YxzXYz" 4 false
    _ = rotationWord (word (rotationSignedWord "YxzXyZYYXyxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "YxzXYYZYYXyxYxzYXyxYxzYXyxyxyzX" "YxzXyZYYXyxYxzYXyxYxzYXyxyxyzX" "YxzX" 1 true
    _ = rotationWord (word (rotationSignedWord "YxzXyZyXyxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "YxzXyZYYXyxYxzYXyxYxzYXyxyxyzX" "YxzXyZyXyxYxzYXyxYxzYXyxyxyzX" "YxzXyZ" 1 true
    _ = rotationWord (word (rotationSignedWord "YxZXyZyXyxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "YxzXyZyXyxYxzYXyxYxzYXyxyxyzX" "YxZXyZyXyxYxzYXyxYxzYXyxyxyzX" "Yx" 2 false
    _ = rotationWord (word (rotationSignedWord "YxZXyzyXyxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "YxZXyZyXyxYxzYXyxYxzYXyxyxyzX" "YxZXyzyXyxYxzYXyxYxzYXyxyxyzX" "YxZXy" 2 true

end

end GroupApproximation.LiteralBaseP13RotationReplay
