module Math.Thermodynamics.PreorderedMonoid

import Core.BoxInt
import Core.UnixelFraction
import Core.Goh

%default total

--------------------------------------------------------------------------------
-- 1. BOUNDED PRE-ORDERED MONOIDS & POSETS
--------------------------------------------------------------------------------

||| Pre-ordered Monoid interface combining a monoidal structure with a compatible preorder (<=)
public export
interface Monoid a => PreorderedMonoid a where
  ||| Reflexive and transitive pre-order relation
  preorder : a -> a -> Bool
  
  ||| Monotonicity axiom: a <= b => a + c <= b + c
  monotonicStep : (x : a) -> (y : a) -> (z : a) -> preorder x y = True -> preorder (x <+> z) (y <+> z) = True

--------------------------------------------------------------------------------
-- 2. POSET DIRECTIONAL STEP EVALUATION
--------------------------------------------------------------------------------

||| Type-level witness enforcing strict directional step evaluation along poset order
public export
data PosetStep : (order : a -> a -> Bool) -> (start : a) -> (endState : a) -> Type where
  MonotonicMove : {0 order : a -> a -> Bool} -> (start : a) -> (endState : a) ->
                  (0 prf : order start endState = True) -> PosetStep order start endState

||| Monotonic BoxInt ordering implementation: x <= y in integer state space
public export
boxIntPreorder : BoxInt -> BoxInt -> Bool
boxIntPreorder b1 b2 = natLTE (boxToNat b1) (boxToNat b2)

--------------------------------------------------------------------------------
-- 3. COMPILE-TIME POSET REFLEXIVITY PROOF
--------------------------------------------------------------------------------

||| Total constructive proof of Nat <= reflexivity without compiler escape hatches.
public export
natLTERefl : (n : Nat) -> natLTE n n = True
natLTERefl Z = Refl
natLTERefl (S k) = natLTERefl k

||| If x <= y then x <= S y in Nat order.
public export
natLTESuccRight : (x : Nat) -> (y : Nat) -> natLTE x y = True -> natLTE x (S y) = True
natLTESuccRight Z y prf = Refl
natLTESuccRight (S k) Z prf = case prf of {}
natLTESuccRight (S k) (S j) prf = natLTESuccRight k j prf

||| Total constructive proof that z <= j + z in Nat order.
public export
natLTEAddLeft : (j : Nat) -> (z : Nat) -> natLTE z (j + z) = True
natLTEAddLeft Z z = natLTERefl z
natLTEAddLeft (S k) z = natLTESuccRight z (k + z) (natLTEAddLeft k z)

||| Total constructive proof of Nat <= monotonicity under addition.
public export
natLTEMonotonic : (x : Nat) -> (y : Nat) -> (z : Nat) -> natLTE x y = True -> natLTE (x + z) (y + z) = True
natLTEMonotonic Z y z prf = natLTEAddLeft y z
natLTEMonotonic (S k) Z z prf = case prf of {}
natLTEMonotonic (S k) (S j) z prf = natLTEMonotonic k j z prf

||| Static compiler proof witness verifying preorder reflexivity (x <= x).
public export
0 verifyPreorderReflexivity : (v : Integer) -> boxIntPreorder (MkBoxInt v) (MkBoxInt v) = True
verifyPreorderReflexivity v = natLTERefl (boxToNat (MkBoxInt v))






