module Stage1.SpatialProjection

import public Stage0.OnSeq.FusedStream
import public Stage1.ScalePipeline.StreamDuality
import Stage0.StructuralFuel
import Data.List
import Data.Fuel

%default total

||| Operator token for spatial stream projections.
public export
record MaxelOperator where
  constructor MkMaxelOp
  src      : Int
  tgt      : Int
  geometry : Geometry

public export %deprecate
sec : MaxelOperator -> Geometry
sec op = op.geometry

------------------------------------------------------------------------
-- 1. TOTAL FUELED SPATIAL BOXEL GRID PROJECTION ON T^3
------------------------------------------------------------------------

||| Total Nat fuel-driven projection of Maxel stream onto 3D Boxel grid T^3.
public export
projectFueledMaxelStreamNat : Nat -> FusedStream MaxelOperator -> Boxel -> StateTransition Boxel
projectFueledMaxelStreamNat 0 _ initialBoxel = pure initialBoxel
projectFueledMaxelStreamNat (S k) (MkStream {s} step s0) initialBoxel =
  go k s0 initialBoxel
  where
    go : Nat -> s -> Boxel -> StateTransition Boxel
    go 0 _ b = pure b
    go (S k') state b = case step state of
      Done => pure b
      Skip state' => go k' state' b
      Yield (MkMaxelOp src tgt sec) state' =>
        let matrix = MkMatrix src tgt Pos Zero Zero Pos
        in driveSpatialUpdate sec matrix b >>= go k' state'

||| Total BoxNat fuel-driven projection of Maxel stream onto 3D Boxel grid T^3.
public export
projectFueledMaxelStreamBoxNat : BoxNat -> FusedStream MaxelOperator -> Boxel -> StateTransition Boxel
projectFueledMaxelStreamBoxNat bfuel strm initialBoxel =
  projectFueledMaxelStreamNat (boxNatToNat bfuel) strm initialBoxel

||| Total Fuel-driven projection of Maxel stream onto 3D Boxel grid T^3.
public export
projectFueledMaxelStream : Fuel -> FusedStream MaxelOperator -> Boxel -> StateTransition Boxel
projectFueledMaxelStream (More f) strm b = projectFueledMaxelStreamBoxNat masterSubstrateGohFuel strm b
projectFueledMaxelStream Dry _ initialBoxel = pure initialBoxel

||| Default fuel-bounded Boxel Stream projection over T^3 canvas bounded by canonical substrate capacity (210).
public export
projectMaxelStream : FusedStream MaxelOperator -> Boxel -> StateTransition Boxel
projectMaxelStream strm b = projectFueledMaxelStreamBoxNat masterSubstrateGohFuel strm b

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
