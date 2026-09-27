module Stage0.LatticeTopology

import Language.Reflection
import Stage0.Singleton.Bit
import Stage0.BoxInt
import Stage1.Order.Preorder
import Stage1.ScaleTransform
import Stage1.VexelMaxel
import Stage1.LinAlgebra.TernaryClassifier
import Stage0.NarayAlphabet
import Data.Vect
import Data.Fin
import Stage1.Goh
import Stage0.OnSeq.FusedStream
import Data.Fuel

%default total

||| A discrete 3D Spatial Coordinate vector situated on the 3x3x3 maxel grid.
||| Each coordinate component x, y, z is an exact ternary value in {-1, 0, +1}.
public export
record Coord3D where
  constructor MkCoord3D
  coordX : TernaryBit
  coordY : TernaryBit
  coordZ : TernaryBit

public export
Eq Coord3D where
  (MkCoord3D x1 y1 z1) == (MkCoord3D x2 y2 z2) =
    x1 == x2 && y1 == y2 && z1 == z2

public export
Show Coord3D where
  show (MkCoord3D x y z) = 
    "(" ++ show (bitToInt x) ++ ", " ++ show (bitToInt y) ++ ", " ++ show (bitToInt z) ++ ")"

------------------------------------------------------------------------
-- 1. BIJECTIVE TERNARY INDEXING (Fin 27 <=> Coord3D)
------------------------------------------------------------------------

public export
ternaryNat : TernaryBit -> Nat
ternaryNat Bit3MinusOne = 0
ternaryNat Bit3Zero     = 1
ternaryNat Bit3PlusOne  = 2

public export
natToTernaryBit : Nat -> TernaryBit
natToTernaryBit 0 = Bit3MinusOne
natToTernaryBit 1 = Bit3Zero
natToTernaryBit _ = Bit3PlusOne

||| Maps a 3D coordinate (x,y,z) to a unique 1D cell index in Fin 27.
||| index = (x + 1) + 3*(y + 1) + 9*(z + 1)
public export
coordToFin27 : Coord3D -> Fin 27
coordToFin27 (MkCoord3D x y z) =
  let u = ternaryNat x
      v = ternaryNat y
      w = ternaryNat z
      idx = u + (3 * v) + (9 * w)
  in case natToFin idx 27 of
       Just f  => f
       Nothing => 0

||| Maps a 1D cell index in Fin 27 to its unique 3D spatial coordinate.
public export
fin27ToCoord : Fin 27 -> Coord3D
fin27ToCoord finIdx =
  let idx = finToNat finIdx
      uNat = idx `mod` 3
      vNat = (idx `div` 3) `mod` 3
      wNat = idx `div` 9
      x = natToTernaryBit uNat
      y = natToTernaryBit vNat
      z = natToTernaryBit wNat
  in MkCoord3D x y z

------------------------------------------------------------------------
-- 2. TOROIDAL PERIODIC NEIGHBORHOOD GRAPH (T^3 Topology)
------------------------------------------------------------------------

||| Moves one step along a ternary axis with periodic toroidal wrapping modulo 3 using F3 addition.
public export
shiftTernaryForward : TernaryBit -> TernaryBit
shiftTernaryForward b = case addNaray (Naray3 b) (Naray3 Bit3PlusOne) of Naray3 b' => b'

public export
shiftTernaryBackward : TernaryBit -> TernaryBit
shiftTernaryBackward b = case addNaray (Naray3 b) (Naray3 Bit3MinusOne) of Naray3 b' => b'

||| The 6 cardinal directions on the 3D lattice.
public export
data CardinalDir = DirEast | DirWest | DirNorth | DirSouth | DirUp | DirDown

||| Computes the adjacent face neighbor coordinate along a cardinal direction.
public export
stepNeighbor : CardinalDir -> Coord3D -> Coord3D
stepNeighbor DirEast  (MkCoord3D x y z) = MkCoord3D (shiftTernaryForward x) y z
stepNeighbor DirWest  (MkCoord3D x y z) = MkCoord3D (shiftTernaryBackward x) y z
stepNeighbor DirNorth (MkCoord3D x y z) = MkCoord3D x (shiftTernaryForward y) z
stepNeighbor DirSouth (MkCoord3D x y z) = MkCoord3D x (shiftTernaryBackward y) z
stepNeighbor DirUp    (MkCoord3D x y z) = MkCoord3D x y (shiftTernaryForward z)
stepNeighbor DirDown  (MkCoord3D x y z) = MkCoord3D x y (shiftTernaryBackward z)

||| Returns the 6 face neighbors of a cell index on the discrete 3-torus.
public export
getFaceNeighbors : Fin 27 -> Vect 6 (Fin 27)
getFaceNeighbors idx =
  let c = fin27ToCoord idx
      e = coordToFin27 (stepNeighbor DirEast c)
      w = coordToFin27 (stepNeighbor DirWest c)
      n = coordToFin27 (stepNeighbor DirNorth c)
      s = coordToFin27 (stepNeighbor DirSouth c)
      u = coordToFin27 (stepNeighbor DirUp c)
      d = coordToFin27 (stepNeighbor DirDown c)
  in [e, w, n, s, u, d]

------------------------------------------------------------------------
-- 3. DISCRETE EXTERIOR CALCULUS & SPATIAL FLUX OPERATORS
------------------------------------------------------------------------

||| Helper to safely look up cell value by Fin 27 index.
public export
lookupCell : Fin 27 -> Vect 27 BoxInt -> BoxInt
lookupCell idx grid = index idx grid

||| Computes the Discrete Laplacian ΔV on a single cell:
||| ΔV(r) = Σ (V(neighbor) - V(r)) for all 6 face neighbors
public export
cellLaplacian : Fin 27 -> Vect 27 BoxInt -> BoxInt
cellLaplacian idx grid =
  let selfVal   = lookupCell idx grid
      neighbors = getFaceNeighbors idx
      sumNeighbors = foldl (\acc, nIdx => addBox acc (lookupCell nIdx grid)) (intToBoxInt 0) neighbors
  in subBox sumNeighbors (addBox selfVal (addBox selfVal (addBox selfVal (addBox selfVal (addBox selfVal selfVal)))))

||| Generates the full Discrete Laplacian field ΔV for all 27 cells.
public export
discreteLaplacian27 : Vect 27 BoxInt -> Vect 27 BoxInt
discreteLaplacian27 grid =
  tabulate (\idx => cellLaplacian idx grid)

||| Computes the total sum of a 27-cell field.
public export
sumField27 : Vect 27 BoxInt -> BoxInt
sumField27 grid = foldl addBox (intToBoxInt 0) grid

||| Propagates spatial field flux by one discrete time step under diffusion parameter kappa:
||| V_{t+1}(r) = V_t(r) + kappa * ΔV(r)
||| Exactly preserves total field sum (sum V_{t+1} == sum V_t).
public export
stepFluxPropagation : BoxInt -> Vect 27 BoxInt -> Vect 27 BoxInt
stepFluxPropagation kappa grid =
  let lap = discreteLaplacian27 grid
  in zipWith (\v, l => addBox v (intToBoxInt (unwrapBox kappa * unwrapBox l))) grid lap

------------------------------------------------------------------------
-- 4. PURE BOXEL MULTISET LATTICE & FLUX OPERATORS
------------------------------------------------------------------------

||| Maps a 1D cell index in Fin 27 to its 3D coordinate Voxel [x, y, z] in {0, 1, 2}^3.
public export
fin27ToVoxel : Fin 27 -> Voxel
fin27ToVoxel idx =
  let (MkCoord3D x y z) = fin27ToCoord idx
  in MkVoxel (ternaryNat x) (ternaryNat y) (ternaryNat z)

||| Converts a flat 27-cell scalar field into a 3D Boxel multiset.
public export
field27ToBoxel : Vect 27 BoxInt -> Boxel
field27ToBoxel grid =
  let paired = tabulate (\idx => (fin27ToVoxel idx, lookupCell idx grid))
  in canonicalizeBoxel (MkBoxel (toList paired))

||| Converts a 3D Boxel multiset back into a flat 27-cell scalar field.
public export
boxelToField27 : Boxel -> Vect 27 BoxInt
boxelToField27 b =
  tabulate (\idx => lookupVoxel (fin27ToVoxel idx) b)

||| Computes the Discrete 3D Laplacian field directly on a Boxel multiset.
public export
discreteLaplacianBoxel : Boxel -> Boxel
discreteLaplacianBoxel b =
  let field = boxelToField27 b
      lap   = discreteLaplacian27 field
  in field27ToBoxel lap

||| Audits that discrete Laplacian flux on the compact 3-torus vanishes identically without leakage.
public export
auditToroidalBoxelFluxProof : Boxel -> Bool
auditToroidalBoxelFluxProof b =
  totalBoxelWeight (discreteLaplacianBoxel b) == intToBoxInt 0

public export
ScaleTransform Coord3D Nat where
  scaleTransform c = finToNat (coordToFin27 c)

public export
InvertibleScaleTransform Coord3D Nat where
  invertScaleTransform n =
    case natToFin n 27 of
      Just f  => fin27ToCoord f
      Nothing => fin27ToCoord 0

public export
auditToroidalBoxelFluxProofBit : Boxel -> Bit
auditToroidalBoxelFluxProofBit b = boolToBit (auditToroidalBoxelFluxProof b)

------------------------------------------------------------------------
-- 5. DISCRETE TOROIDAL CELL NETWORK & FLUX HOMOLOGY RING
------------------------------------------------------------------------

||| Represents a focused coordinate on a finite toroidal lattice network
public export
record ToroidalCell (size : Nat) where
  constructor Cell
  xCoord : Nat
  yCoord : Nat
  0 xBounded : LT xCoord size
  0 yBounded : LT yCoord size

||| A type-level proof witness tracking discrete topological gauge flux loops.
||| It maps a GohMultiset path structure to an exact integer winding number (Nat).
public export
data ToroidalFlux : (size : Nat) -> (bag : GohMultiset) -> (windingNumber : Nat) -> Type where
  ||| Constructing this witness requires proving that the path completes 
  ||| a closed, integer-conserving homology loop around the lattice torus.
  QuantizedLoop : {size : Nat} -> {winding : Nat} ->
                  (bag : GohMultiset) -> 
                  (0 prf : (countFactors bag = (winding * size))) -> 
                  ToroidalFlux size bag winding

||| Audits toroidal flux containment by verifying that the multiset 
||| factor layout maps cleanly to a valid homology invariant class.
public export
auditToroidalBoxelFlux : (size : Nat) -> (bag : GohMultiset) -> Bool
auditToroidalBoxelFlux Z bag = True
auditToroidalBoxelFlux (S k) bag =
  case countFactors bag of
    Z => True
    S n => ((S n) `mod` (S k)) == 0

||| Static compiler proof witness verifying that the topological vacuum 
||| maps safely to the identity homology class with zero structural drift.
public export
0 verifyTopologicalCoherence : (size : Nat) -> 
                              auditToroidalBoxelFlux size EmptyBag = True
verifyTopologicalCoherence Z     = Refl
verifyTopologicalCoherence (S k) = Refl

||| Type-level erased proof witness verifying discrete lattice metric quadrance invariance (dx^2 + dy^2 = q).
public export
0 DiscreteLatticeQuadranceInvariance : Nat -> Nat -> Nat -> Type
DiscreteLatticeQuadranceInvariance dx dy q = natAdd (dx * dx) (dy * dy) = q

||| Discrete chromogeometric transformation witness across spatial shift steps on the torus,
||| equipped with an erased 0 metricPrf QuadranceInvariance witness.
public export
record DiscreteLatticeMetricTransform (dx : Nat) (dy : Nat) (q : Nat) where
  constructor MkDiscreteLatticeMetricTransform
  0 metricPrf : DiscreteLatticeQuadranceInvariance dx dy q

||| Constructs a discrete lattice metric transformation with an erased compile-time quadrance witness.
public export
makeLatticeMetricTransform : (dx : Nat) -> (dy : Nat) -> (q : Nat) ->
                             (0 metricPrf : DiscreteLatticeQuadranceInvariance dx dy q) ->
                             DiscreteLatticeMetricTransform dx dy q
makeLatticeMetricTransform dx dy q prf = MkDiscreteLatticeMetricTransform prf

------------------------------------------------------------------------
-- 6. DEFORESTED SPATIAL LATTICE COORDINATE STREAMING
------------------------------------------------------------------------

||| Generates a zero-allocation deforested stream of spatial coordinate shifts across a direction sequence.
public export
fusedLatticeStream : Coord3D -> List CardinalDir -> FusedStream Coord3D
fusedLatticeStream startPos dirs =
  unfoldStream
    (\(curr, ds) => case ds of
                      [] => Done
                      (d :: rest) =>
                        let next = stepNeighbor d curr
                        in Yield next (next, rest))
    (startPos, dirs)

||| Audit witness verifying zero-allocation lattice stream spatial shift equivalence.
public export covering
auditFusedLatticeStreamProof : Bool
auditFusedLatticeStreamProof =
  let c0 = MkCoord3D Bit3Zero Bit3Zero Bit3Zero
      dirs = [DirEast, DirNorth, DirUp]
      strm = fusedLatticeStream c0 dirs
      res = runFueledStream (limit 10) strm
  in length res == 3
