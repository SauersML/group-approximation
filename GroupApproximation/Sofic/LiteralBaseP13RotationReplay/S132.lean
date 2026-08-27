import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S132Trace2

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s132Image_eq_one :
    rotationWord (word (rotationSignedWord "xzYXYXzYXYXyxyZyxyZxxyZXy")) = 1 := by
  calc
    _ = rotationWord (word (rotationSignedWord "")) := s132Trace2
    _ = 1 := by rfl

end

end GroupApproximation.LiteralBaseP13RotationReplay
