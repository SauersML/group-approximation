import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.RangeXYTrace1

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem rangeXYImage_eq_one :
    rotationWord (word (rotationSignedWord "xyZXyyxyZYxzYxYX")) = 1 := by
  calc
    _ = rotationWord (word (rotationSignedWord "")) := rangeXYTrace1
    _ = 1 := by rfl

end

end GroupApproximation.LiteralBaseP13RotationReplay
