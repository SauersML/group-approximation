import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.RangeZTrace4

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem rangeZImage_eq_one :
    rotationWord (word (rotationSignedWord "YxzYXZXYXyXyZXyXYxzYzYXYXyZXyXXyZXyzYXYZ")) = 1 := by
  calc
    _ = rotationWord (word (rotationSignedWord "")) := rangeZTrace4
    _ = 1 := by rfl

end

end GroupApproximation.LiteralBaseP13RotationReplay
