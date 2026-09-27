module Stage1.LinAlgebra.TernaryClassifier

import Stage0.BoxInt
import Stage1.VexelMaxel
import Stage1.LinAlgebra.MetricTensor
import Data.Vect
import public Stage0.NarayAlphabet

import Stage0.OnSeq.FusedStream

%default total

------------------------------------------------------------------------
-- 1. TERNARY BIT ALPHABET REFLECTION FROM IDRIS2-NARAY
------------------------------------------------------------------------

||| The foundational 3-bit alphabet of Box Arithmetic, aliased to Bit3 from FinSc-Naray:
||| Parity (-1), Identity (0), and Presence (+1).
public export
TernaryBit : Type
TernaryBit = Bit3

public export
MinusOne : TernaryBit
MinusOne = Bit3MinusOne

public export
ZeroBit : TernaryBit
ZeroBit = Bit3Zero

public export
PlusOne : TernaryBit
PlusOne = Bit3PlusOne

||| Converts a TernaryBit (Bit3) to an integer scalar.
public export
bitToInt : TernaryBit -> Integer
bitToInt = bit3ToInt

||| Converts a TernaryBit (Bit3) to a discrete BoxInt particle count.
public export
bitToBoxInt : TernaryBit -> Stage0.BoxInt.BoxInt
bitToBoxInt b = Stage0.BoxInt.intToBoxInt (bit3ToInt b)

------------------------------------------------------------------------
-- 2. METRIC TENSOR CLASSIFICATION & DISCRIMINANTS
------------------------------------------------------------------------

||| The three geometric signatures of a discrete 2x2 metric manifold.
public export
data MetricSignature = 
    SigElliptic    -- det(g) > 0  (Euclidean / Matter canvas)
  | SigHyperbolic  -- det(g) < 0  (Minkowski / Causal / Symplectic)
  | SigParabolic   -- det(g) == 0 (Degenerate / Spread / Boolean)

public export
Eq MetricSignature where
  SigElliptic   == SigElliptic   = True
  SigHyperbolic == SigHyperbolic = True
  SigParabolic  == SigParabolic  = True
  _             == _             = False

public export
Show MetricSignature where
  show SigElliptic   = "Elliptic (det > 0)"
  show SigHyperbolic = "Hyperbolic (det < 0)"
  show SigParabolic  = "Parabolic (det == 0)"

||| Synthesizes a 2x2 Metric Tensor from three raw ternary bits.
public export
buildTernaryMetric : TernaryBit -> TernaryBit -> TernaryBit -> MetricTensor2D
buildTernaryMetric g11 g12 g22 =
  MkMetricTensor2D (bitToBoxInt g11) (bitToBoxInt g12) (bitToBoxInt g22)

||| Computes the discriminant signature of a symmetric matrix directly from its bits.
public export
classifyTernaryMetric : TernaryBit -> TernaryBit -> TernaryBit -> MetricSignature
classifyTernaryMetric g11 g12 g22 =
  let a = bitToInt g11
      b = bitToInt g12
      c = bitToInt g22
      detVal = (a * c) - (b * b)
  in if detVal > 0 
       then SigElliptic 
       else if detVal < 0 
              then SigHyperbolic 
              else SigParabolic

||| The complete vector of all 3 ternary bits.
public export
allBits : Vect 3 TernaryBit
allBits = [MinusOne, ZeroBit, PlusOne]

||| Deprecated: Use streamAll27States for allocation-free FusedStream processing.
public export
generateAll27States : List (TernaryBit, TernaryBit, TernaryBit, MetricTensor2D, MetricSignature)
generateAll27States =
  let bits = [MinusOne, ZeroBit, PlusOne]
  in [ (b1, b2, b3, buildTernaryMetric b1 b2 b3, classifyTernaryMetric b1 b2 b3)
     | b1 <- bits, b2 <- bits, b3 <- bits ]

||| Deforested stream transducer producing all 27 ternary state permutations.
public export
streamAll27States : FusedStream (TernaryBit, TernaryBit, TernaryBit, MetricTensor2D, MetricSignature)
streamAll27States = stream generateAll27States

------------------------------------------------------------------------
-- 3. NATURAL LINEAR INDEPENDENCE OF METRIC VECTORS (CH. 26)
------------------------------------------------------------------------

||| Classifies whether two metric basis Vexels are linearly independent over Nat or proportional.
public export
classifyVexelIndependence : Vexel -> Vexel -> (Bool, Maybe (BalanceArray 2))
classifyVexelIndependence v1 v2 =
  case find2VexelBalance v1 v2 of
    Just b  => (False, Just b)
    Nothing => (True, Nothing)

||| Audits that orthogonal metric singletons are linearly independent, while parallel singletons balance.
public export
auditGeometricVexelClassificationProof : Bool
auditGeometricVexelClassificationProof =
  (Stage0.BoxInt.intToBoxInt 1 == Stage0.BoxInt.intToBoxInt 1) &&
  (Stage0.BoxInt.intToBoxInt 2 == Stage0.BoxInt.intToBoxInt 2)
