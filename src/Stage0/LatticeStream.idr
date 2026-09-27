module Stage0.LatticeStream

import Data.List
import Data.Fin
import Data.Fuel
import Stage0.OnSeq.FusedStream
import Stage0.LatticeTopology

%default total

------------------------------------------------------------------------
-- 1. DEFORESTED LATTICE STREAM GENERATION
------------------------------------------------------------------------

||| Deprecated: Use unfoldLatticeCoords for allocation-free FusedStream Coord3D.
public export
allLatticeCoords : List Coord3D
allLatticeCoords = map fin27ToCoord (allFin 27)
  where
    allFin : (n : Nat) -> List (Fin n)
    allFin 0 = []
    allFin (S k) = FZ :: map FS (allFin k)

||| Creates a deforested stream of all 27 3D lattice coordinates.
public export
streamLatticeCoords : FusedStream Coord3D
streamLatticeCoords = stream allLatticeCoords

||| Anamorphic generator step function for 27 lattice coordinates.
public export
stepFin27 : Nat -> Step Nat Coord3D
stepFin27 k =
  if k >= 27
    then Done
    else case natToFin k 27 of
      Just finIdx => Yield (fin27ToCoord finIdx) (S k)
      Nothing     => Done

||| Generates a deforested stream of all 27 3D lattice coordinates via direct anamorphism.
public export
unfoldLatticeCoords : FusedStream Coord3D
unfoldLatticeCoords = unfoldStream stepFin27 0

------------------------------------------------------------------------
-- 2. STREAMED LATTICE TRANSFORMATIONS & PIPELINES
------------------------------------------------------------------------

||| Deforested transformation of lattice coordinates along a direction.
public export
fusedStepLattice : CardinalDir -> FusedStream Coord3D -> FusedStream Coord3D
fusedStepLattice dir = mapStream (stepNeighbor dir)

||| Deforested filter retaining lattice coordinates satisfying a spatial predicate.
public export
fusedFilterLattice : (Coord3D -> Bool) -> FusedStream Coord3D -> FusedStream Coord3D
fusedFilterLattice = filterStream

||| Evaluates a lattice stream into a concrete List of 3D coordinates.
public export
runLatticeStream : Fuel -> FusedStream Coord3D -> List Coord3D
runLatticeStream = runFueledStream
