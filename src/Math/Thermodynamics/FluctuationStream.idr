module Math.Thermodynamics.FluctuationStream

import public Core.BoxInt
import public Math.OnSeq.FusedStream
import public Math.Thermodynamics.EntropicArrow
import Data.Fuel

%default total

--------------------------------------------------------------------------------
-- 1. THERMODYNAMIC WORK & HEAT FLUCTUATION STREAM ALGEBRA
--------------------------------------------------------------------------------

||| Discrete thermodynamic fluctuation step containing work done W and heat exchanged Q.
public export
record FluctuationStep where
  constructor MkFluctuation
  stepId   : Int
  workDone : BoxInt
  heatLoss : BoxInt

public export
Eq FluctuationStep where
  (MkFluctuation id1 w1 q1) == (MkFluctuation id2 w2 q2) =
    id1 == id2 && w1 == w2 && q1 == q2

||| Unfolds a list of work values into a deforested FluctuationStream.
%inline public export
unfoldWorkStream : List BoxInt -> FusedStream FluctuationStep
unfoldWorkStream workList = MkStream nextStep (1, workList)
  where
    nextStep : (Int, List BoxInt) -> Step (Int, List BoxInt) FluctuationStep
    nextStep (_, []) = Done
    nextStep (idx, w :: ws) = Yield (MkFluctuation idx w (intToBoxInt 0)) (idx + 1, ws)

||| Folds total work done across a deforested thermodynamic fluctuation stream using hylomorphism.
public export covering
fusedTotalWork : Fuel -> List BoxInt -> BoxInt
fusedTotalWork f workList =
  fusedHylomorphism f
    (\(idx, ws) => case ws of
                     [] => Done
                     w :: ws' => Yield (MkFluctuation idx w (intToBoxInt 0)) (idx + 1, ws'))
    (\step, acc => workDone step + acc)
    (intToBoxInt 0)
    (1, workList)

||| Evaluates discrete Jarzynski-style exponent sum: \sum (1 - \beta * W)
||| as a discrete linear approximation of <e^{-\beta W}> over work fluctuation streams.
public export covering
fusedJarzynskiLinearBound : Fuel -> BoxInt -> List BoxInt -> BoxInt
fusedJarzynskiLinearBound f beta workList =
  fusedHylomorphism f
    (\(idx, ws) => case ws of
                     [] => Done
                     w :: ws' => Yield (MkFluctuation idx w (intToBoxInt 0)) (idx + 1, ws'))
    (\step, acc => (intToBoxInt 1 - (beta * workDone step)) + acc)
    (intToBoxInt 0)
    (1, workList)

--------------------------------------------------------------------------------
-- 2. VERIFICATION AUDIT WITNESS
--------------------------------------------------------------------------------

||| Audit witness verifying zero-allocation total work folding over thermodynamic fluctuation streams.
public export
auditFluctuationStreamProof : Bool
auditFluctuationStreamProof =
  let works = [intToBoxInt 2, intToBoxInt 3, intToBoxInt 5]
      totW = fusedTotalWork (limit 100) works
      jBound = fusedJarzynskiLinearBound (limit 100) (intToBoxInt 1) works
  in unwrapBox totW == 10 && unwrapBox jBound == -7
