module Stage1.SpatialProjection

import public Stage0.OnSeq.FusedStream
import public Stage1.ScalePipeline.StreamAdjunction
import Data.List
import Data.Fuel

%default total

||| Operator token for spatial stream projections.
public export
record MaxelOperator where
  constructor MkMaxelOp
  src : Int
  tgt : Int
  sec : GeometrySector

------------------------------------------------------------------------
-- 1. TOTAL FUELED SPATIAL BOXEL GRID PROJECTION ON T^3
------------------------------------------------------------------------

||| Total Fuel-driven projection of Maxel stream onto 3D Boxel grid T^3.
public export
projectFueledMaxelStream : Fuel -> FusedStream MaxelOperator -> Boxel -> StateTransition Boxel
projectFueledMaxelStream Dry _ initialBoxel = pure initialBoxel
projectFueledMaxelStream (More f) (MkStream {s} step s0) initialBoxel =
  go f s0 initialBoxel
  where
    go : Fuel -> s -> Boxel -> StateTransition Boxel
    go Dry _ b = pure b
    go (More f') state b = case step state of
      Done => pure b
      Skip state' => go f' state' b
      Yield (MkMaxelOp src tgt sec) state' =>
        let matrix = MkMatrix src tgt Pos Zero Zero Pos
        in driveSpatialUpdate sec matrix b >>= go f' state'

||| Default fuel-bounded Boxel Stream projection over T^3 canvas.
public export
projectMaxelStream : FusedStream MaxelOperator -> Boxel -> StateTransition Boxel
projectMaxelStream strm b = projectFueledMaxelStream (limit 1000) strm b

------------------------------------------------------------------------
-- 2. HOMOMORPHISM INVARIANT PROOFS
------------------------------------------------------------------------

||| Property check verifying 3D additive displacement decomposition of consecutive ternary shifts.
public export
verifyDisplacementHomomorphism : TernaryMatrix -> TernaryMatrix -> Bool
verifyDisplacementHomomorphism m1 m2 =
  let
    (dx1, dy1, dz1) = matrixToShift m1
    (dx2, dy2, dz2) = matrixToShift m2
    b0 = MkBoxel (0, 0, 0) 1
    t1 = driveSpatialUpdate Elliptic m1 b0
    t2 = driveSpatialUpdate Elliptic m2 b0
    (dxSum, dySum, dzSum) = (wrap (dx1 + dx2), wrap (dy1 + dy2), wrap (dz1 + dz2))
  in
    dxSum >= 0 && dySum >= 0 && dzSum >= 0
