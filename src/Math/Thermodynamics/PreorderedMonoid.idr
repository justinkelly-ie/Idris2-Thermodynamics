module Math.Thermodynamics.PreorderedMonoid

import public Core.Order.Preorder
import Core.BoxInt
import Core.UnixelFraction
import Core.Goh

%default total

--------------------------------------------------------------------------------
-- 1. BOXINT POSET ORDERING
--------------------------------------------------------------------------------

||| Monotonic BoxInt ordering implementation: x <= y in integer state space
public export
boxIntPreorder : BoxInt -> BoxInt -> Bool
boxIntPreorder b1 b2 = natLTE (boxToNat b1) (boxToNat b2)

||| Static compiler proof witness verifying preorder reflexivity (x <= x).
public export
0 verifyPreorderReflexivity : (v : Integer) -> boxIntPreorder (MkBoxInt v) (MkBoxInt v) = True
verifyPreorderReflexivity v = natLTERefl (boxToNat (MkBoxInt v))
