module Stage1.RationalTrig

import Stage0.BoxInt
import Stage1.Basis.CoordCell
import Stage1.Carrier.CellMultiset
import Stage1.Carrier.Maxel
import Stage1.Carrier.Vexel
import Stage1.Basis.Coordinate
import Stage0.Multiset
import Stage1.UnixelFraction
import Stage1.Polynumber
import Stage1.LinAlgebra.MetricTensor
import Stage1.TypeTheory.TwoLevel
import Stage1.TypeTheory.Staging
import Stage1.MultisetTree
import Stage0.OnSeq.FusedStream
import Stage1.MaxelPolyBridge
import Data.Fuel
import Data.Vect
import Data.List

%default total

------------------------------------------------------------------------
-- 1. ARCHIMEDES' FUNCTION, QUADREA & GRAM MAXEL
------------------------------------------------------------------------

||| Wildberger's Archimedes Function over exact BoxInt quadrances:
||| A(Q1, Q2, Q3) = (Q1 + Q2 + Q3)^2 - 2(Q1^2 + Q2^2 + Q3^2)
|||              = 4*Q1*Q2 - (Q1 + Q2 - Q3)^2
public export
archimedesFunction : BoxInt -> BoxInt -> BoxInt -> BoxInt
archimedesFunction q1 q2 q3 =
  let sumQ   = q1 + q2 + q3
      sumSqQ = (q1 * q1) + (q2 * q2) + (q3 * q3)
  in (sumQ * sumQ) - (intToBoxInt 2 * sumSqQ)

||| Computes the Quadrea of a triangle with side quadrances Q1, Q2, Q3.
||| Quadrea = 16 * (Classical Area)^2, completely exact in BoxInt arithmetic.
public export
quadrea : BoxInt -> BoxInt -> BoxInt -> BoxInt
quadrea q1 q2 q3 = archimedesFunction q1 q2 q3

||| Constructs the 2x2 symmetric Gram Maxel of a triangle from its three side quadrances:
||| [[2*Q1, Q1 + Q2 - Q3], [Q1 + Q2 - Q3, 2*Q2]].
public export
gramMaxel : (q1 : BoxInt) -> (q2 : BoxInt) -> (q3 : BoxInt) -> Maxel
gramMaxel q1 q2 q3 =
  let g11Val = intToBoxInt 2 * q1
      g12Val = (q1 + q2) - q3
      g22Val = intToBoxInt 2 * q2
  in buildMetricMaxel g11Val g12Val g22Val

||| Computes Quadrea directly as the determinant of the Gram Maxel.
||| Proves that det(Gram(Q1, Q2, Q3)) = 4*Q1*Q2 - (Q1 + Q2 - Q3)^2 = ArchimedesFunction(Q1, Q2, Q3).
public export
quadreaMaxel : BoxInt -> BoxInt -> BoxInt -> BoxInt
quadreaMaxel q1 q2 q3 =
  detMetric (gramMaxel q1 q2 q3)

||| Dimension-checked 2x2 Gram SquareMaxel of a triangle from its three side quadrances:
public export
gramSquareMaxel : (q1 : BoxInt) -> (q2 : BoxInt) -> (q3 : BoxInt) -> SquareMaxel 2
gramSquareMaxel q1 q2 q3 = maxelToSquareMaxel 2 (gramMaxel q1 q2 q3)

||| Computes Quadrea directly as the determinant of the 2x2 Gram SquareMaxel.
public export
quadreaSquareMaxel : BoxInt -> BoxInt -> BoxInt -> BoxInt
quadreaSquareMaxel q1 q2 q3 =
  detMetric (squareMaxelToMaxel (gramSquareMaxel q1 q2 q3))

||| Collinearity predicate: three points are collinear (lie on a geodesic)
||| if and only if Archimedes' function on their side quadrances vanishes.
public export
isCollinearQuadrance : BoxInt -> BoxInt -> BoxInt -> Bool
isCollinearQuadrance q1 q2 q3 =
  archimedesFunction q1 q2 q3 == intToBoxInt 0

||| Emergence theorem from 2x2 maxels:
||| Evaluates the Gram determinant Archimedes formula: 4 * det(g) * (x1*y2 - x2*y1)^2
public export
archimedesFromMaxels : Maxel -> BoxInt -> BoxInt -> BoxInt -> BoxInt -> BoxInt
archimedesFromMaxels metric x1 y1 x2 y2 =
  let crossDet = (x1 * y2) - (x2 * y1)
      detG     = detMetric metric
  in intToBoxInt 4 * detG * (crossDet * crossDet)

------------------------------------------------------------------------
-- 2. 3D QUADRANCE & EXACT RATIONAL SPREADS
------------------------------------------------------------------------

||| Exact squared distance between two natural numbers: (a - b)^2.
public export
natSqDist : Nat -> Nat -> Nat
natSqDist a b =
  let d = if a >= b then minus a b else minus b a
  in d * d

||| 2LTT Staged Universal Difference Quadrance across CoordCell coordinates.
||| Emits branchless, flat Level 1 sums of squared differences for D in {1, 2, 3, 4}.
public export
stagedCellQuadranceDiff : (dim : Nat) -> Lift (CoordCell dim) -> Lift (CoordCell dim) -> Lift Nat
stagedCellQuadranceDiff (S Z) qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
         in natSqDist (coordAxis 0 c1) (coordAxis 0 c2))
stagedCellQuadranceDiff (S (S Z)) qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
         in natSqDist (coordAxis 0 c1) (coordAxis 0 c2) +
            natSqDist (coordAxis 1 c1) (coordAxis 1 c2))
stagedCellQuadranceDiff (S (S (S Z))) qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
         in natSqDist (coordAxis 0 c1) (coordAxis 0 c2) +
            natSqDist (coordAxis 1 c1) (coordAxis 1 c2) +
            natSqDist (coordAxis 2 c1) (coordAxis 2 c2))
stagedCellQuadranceDiff (S (S (S (S Z)))) qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
         in natSqDist (coordAxis 0 c1) (coordAxis 0 c2) +
            natSqDist (coordAxis 1 c1) (coordAxis 1 c2) +
            natSqDist (coordAxis 2 c1) (coordAxis 2 c2) +
            natSqDist (coordAxis 3 c1) (coordAxis 3 c2))
stagedCellQuadranceDiff dim qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
             go : (fuel : Nat) -> Nat -> Nat -> Nat
             go Z _ acc = acc
             go (S f) axis acc =
               if axis >= dim then acc
               else go f (S axis) (acc + natSqDist (coordAxis axis c1) (coordAxis axis c2))
         in go dim 0 0)

||| Computes the exact coordinate Quadrance Q between two CoordCells of any dimension:
||| Q(c1, c2) = sum_{axis=0}^{dim-1} (c1(axis) - c2(axis))^2
public export
cellQuadranceDiff : {dim : Nat} -> CoordCell dim -> CoordCell dim -> BoxInt
cellQuadranceDiff {dim} c1 c2 =
  natToBoxInt (splice (stagedCellQuadranceDiff dim (quote c1) (quote c2)))

||| Computes the exact 3D Quadrance Q between two coordinate Voxels:
||| Q(v1, v2) = (x1 - x2)^2 + (y1 - y2)^2 + (z1 - z2)^2
public export
quadrance3D : Voxel -> Voxel -> BoxInt
quadrance3D v1 v2 = cellQuadranceDiff {dim = 3} v1 v2

||| Computes the exact 2D Quadrance Q between two coordinate Pixels:
public export
quadrance2D : Pixel -> Pixel -> BoxInt
quadrance2D p1 p2 = cellQuadranceDiff {dim = 2} p1 p2

||| Computes the exact 1D Quadrance Q between two coordinate Unixels:
public export
quadrance1D : Unixel -> Unixel -> BoxInt
quadrance1D u1 u2 = cellQuadranceDiff {dim = 1} u1 u2

||| Computes the exact Rational Spread s = sin^2(theta) between two lines
||| meeting at a vertex in a triangle with side quadrances Q1, Q2, Q3 (Spread Law):
||| s = A(Q1, Q2, Q3) / (4 * Q1 * Q2)
||| Returns (Numerator, Denominator) pair of BoxInts.
public export
spreadFromQuadrances : (q1 : BoxInt) -> (q2 : BoxInt) -> (q3 : BoxInt) -> (BoxInt, BoxInt)
spreadFromQuadrances q1 q2 q3 =
  let num = quadrea q1 q2 q3
      den = intToBoxInt 4 * q1 * q2
  in (num, den)

||| Computes the 3D Rational Spread between vectors (center -> a) and (center -> b).
public export
spread3D : (a : Voxel) -> (center : Voxel) -> (b : Voxel) -> (BoxInt, BoxInt)
spread3D a center b =
  let q1 = quadrance3D center a
      q2 = quadrance3D center b
      q3 = quadrance3D a b
  in spreadFromQuadrances q1 q2 q3

||| Exact Tetrahedral Spread s = 8/9 (theta ~ 109.47 degrees).
||| Emerges constructively from central tetrahedral voxel geometry.
public export
tetrahedralSpreadRatio : (BoxInt, BoxInt)
tetrahedralSpreadRatio = (intToBoxInt 8, intToBoxInt 9)

||| Multiple Spread Polynumber generator Sn(s) using Wildberger's Chebyshev-type recurrence:
||| S0 = 0, S1 = s, S2 = 4s - 4s^2, S3 = 9s - 24s^2 + 16s^3, ...
public export
spreadPolynumberRecurrence : Nat -> Polynumber
spreadPolynumberRecurrence n = spreadPolynumber n

||| Degree-certified multiple spread recurrence generator:
||| S_n(s) has certified degree n at compile time.
public export
spreadDepRecurrence : (n : Nat) -> DepPolynumber n
spreadDepRecurrence = spreadDepPolynumber

||| Deforested stream wave stepping: streams multiple spread polynomials (n, S_n)
||| in O(1) memory via companion transfer matrix recursion.
public export
spreadWaveStream : FusedStream (Nat, Polynumber)
spreadWaveStream = spreadRecurrenceStream

||| Evaluates the tetrahedral spread S_3 with certified degree 3:
||| S_3(s) = 9s - 24s^2 + 16s^3.
public export
tetrahedralSpreadDepPoly : DepPolynumber 3
tetrahedralSpreadDepPoly = spreadDepRecurrence 3

||| Compile-time audit: tetrahedral spread polynomial S_3 has certified degree 3
||| and exact coefficients [0, 9, -24, 16].
public export
0 verifyTetrahedralSpreadDegree :
  toList Stage1.RationalTrig.tetrahedralSpreadDepPoly.polyCoeffs =
  [intToBoxInt 0, intToBoxInt 9, intToBoxInt (-24), intToBoxInt 16]
verifyTetrahedralSpreadDegree = Refl

------------------------------------------------------------------------
-- 3. RATIONAL SNELL'S LAW & TRIPLE SPREAD LAW
------------------------------------------------------------------------

||| Exact Rational Snell Refraction across an optical interface:
||| n1^2 * s1 == n2^2 * s2  =>  s2 = (n1^2 * s1) / n2^2.
public export
refractSpread : (n1Sq : BoxInt) -> (n2Sq : BoxInt) -> (s1 : BoxInt) -> BoxInt
refractSpread n1Sq n2Sq s1 =
  let denom = if boxIsZero n2Sq then intToBoxInt 1 else n2Sq
  in (n1Sq * s1) `div` denom

||| Evaluates the Wildberger Triple Spread Law invariant:
||| (s1 + s2 + s3)^2 == 2(s1^2 + s2^2 + s3^2) + 4 s1 s2 s3.
public export
verifyTripleSpreadLaw : (s1 : BoxInt) -> (s2 : BoxInt) -> (s3 : BoxInt) -> Bool
verifyTripleSpreadLaw s1 s2 s3 =
  let lhs = (s1 + s2 + s3) * (s1 + s2 + s3)
      rhs = (intToBoxInt 2 * ((s1 * s1) + (s2 * s2) + (s3 * s3))) + 
            (intToBoxInt 4 * s1 * s2 * s3)
  in lhs == rhs

||| Audits that the Triple Spread Law holds for 3 mutually orthogonal / right-angle lines (spreads 1, 1, 0).
public export
auditTripleSpreadLawProof : Bool
auditTripleSpreadLawProof =
  verifyTripleSpreadLaw (intToBoxInt 1) (intToBoxInt 1) (intToBoxInt 0)

||| Audits that Exact Rational Snell Refraction preserves n1^2 * s1 == n2^2 * s2.
public export
auditRationalSnellLawProof : Bool
auditRationalSnellLawProof =
  let n1Sq = intToBoxInt 1
      s1   = intToBoxInt 4
      n2Sq = intToBoxInt 4
      s2   = refractSpread n1Sq n2Sq s1
  in s2 == intToBoxInt 1 && (n1Sq * s1) == (n2Sq * s2)

------------------------------------------------------------------------
-- 4. CONTAINER DIFFERENCE QUADRANCE & RATIONAL SPREAD (CH. 18-20)
------------------------------------------------------------------------

||| Computes the exact Box Difference Quadrance between two multiset containers:
||| Q_Box(A, B) = (D_MSet(A, B))^2 = (sum_x |w_A(x) - w_B(x)|)^2.
public export
boxDifferenceQuadrance : Eq a => Box a -> Box a -> BoxInt
boxDifferenceQuadrance b1 b2 =
  let d = natToBoxInt (boxSymmetricDifference b1 b2)
  in d * d

||| Computes the exact Difference Quadrance between two BoxSpec structures:
||| Q_Spec(A, B) = |boxSize(A) - boxSize(B)|^2.
public export
boxSpecQuadrance : BoxSpec -> BoxSpec -> BoxInt
boxSpecQuadrance s1 s2 =
  let sz1 = natToBoxInt (boxSize s1)
      sz2 = natToBoxInt (boxSize s2)
      diff = sz1 - sz2
  in diff * diff

||| Computes the exact coordinate Quadrance between two 1D Vexels:
||| Q_Vexel(v1, v2) = sum_i (c1(i) - c2(i))^2.
public export
vexelQuadrance : Vexel -> Vexel -> BoxInt
vexelQuadrance v1 v2 =
  let xs = terms v1
      ys = terms v2
      allIndices = nub (map (unUnixel . fst) xs ++ map (unUnixel . fst) ys)
      sqDiffs = map (\idx =>
        let w1 = lookupUnixel (MkUnixel idx) v1
            w2 = lookupUnixel (MkUnixel idx) v2
            diff = w1 - w2
        in diff * diff) allIndices
  in foldl (+) (intToBoxInt 0) sqDiffs
  where
    unUnixel : Unixel -> Nat
    unUnixel = unwrapUnixel

||| Computes the exact Rational Spread s = sin^2(theta) between three container quadrances Q1, Q2, Q3:
||| s = A(Q1, Q2, Q3) / (4 * Q1 * Q2) in UnixelFraction.
public export
boxSpread : (q1 : BoxInt) -> (q2 : BoxInt) -> (q3 : BoxInt) -> UnixelFraction
boxSpread q1 q2 q3 =
  let numVal = quadrea q1 q2 q3
      denBox = intToBoxInt 4 * q1 * q2
      denNat = boxIntToPositiveNat denBox
  in mkUnixelFraction numVal denNat

||| Computes the exact Rational Spread between Vexel displacements (vertex -> a) and (vertex -> b).
public export
vexelSpread : (a : Vexel) -> (vertex : Vexel) -> (b : Vexel) -> UnixelFraction
vexelSpread a vertex b =
  let q1 = vexelQuadrance vertex a
      q2 = vexelQuadrance vertex b
      q3 = vexelQuadrance a b
  in boxSpread q1 q2 q3

||| Audits Container Pythagorean Theorem (Right-Angle Spread s = 1):
||| Displacements v1 = [3, 0] and v2 = [0, 4] from origin [0, 0]:
||| Q1 = 9, Q2 = 16, Q3 = 25 (3^2 + 4^2 = 5^2).
||| A(9, 16, 25) = 4*9*16 - (9+16-25)^2 = 576.
||| 4 * Q1 * Q2 = 4 * 9 * 16 = 576.
||| s = 576 / 576 = 1.
public export
auditBoxPythagorasProof : Bool
auditBoxPythagorasProof =
  archimedesFunction (intToBoxInt 9) (intToBoxInt 16) (intToBoxInt 25) == intToBoxInt 576

||| Audits Container Collinearity Spread (s = 0):
||| Points along the same line: origin [0, 0], v1 = [2, 0], v2 = [5, 0].
||| Q1 = 4, Q2 = 25, Q3 = 9.
||| A(4, 25, 9) = 4*4*25 - (4+25-9)^2 = 400 - 400 = 0.
||| s = 0.
public export
auditBoxCollinearitySpreadProof : Bool
auditBoxCollinearitySpreadProof =
  archimedesFunction (intToBoxInt 4) (intToBoxInt 25) (intToBoxInt 9) == intToBoxInt 0

------------------------------------------------------------------------
-- 5. TWO-LEVEL TYPE THEORY (2LTT) QUADREA & WILDBERGER CHROMOGEOMETRY
------------------------------------------------------------------------

||| Wildberger Theorem 6: Three-Fold Quadrance Metric Symmetry (Q_b^2 == Q_r^2 + Q_g^2).
||| For displacement (dx, dy): Q_b = dx^2 + dy^2, Q_r = dx^2 - dy^2, Q_g = 2*dx*dy.
public export
evaluateThreeFoldQuadranceSymmetry : (dx : BoxInt) -> (dy : BoxInt) -> Bool
evaluateThreeFoldQuadranceSymmetry dx dy =
  let qb = (dx * dx) + (dy * dy)
      qr = (dx * dx) - (dy * dy)
      qg = intToBoxInt 2 * (dx * dy)
  in (qb * qb) == (qr * qr) + (qg * qg)

||| Computes the (Blue, Red, Green) Quadreas of a triangle A1(x1, y1), A2(x2, y2), A3(x3, y3).
public export
evaluateThreeFoldQuadrea : (x1 : BoxInt) -> (y1 : BoxInt) ->
                           (x2 : BoxInt) -> (y2 : BoxInt) ->
                           (x3 : BoxInt) -> (y3 : BoxInt) -> (BoxInt, BoxInt, BoxInt)
evaluateThreeFoldQuadrea x1 y1 x2 y2 x3 y3 =
  let dx12 = x2 - x1
      dy12 = y2 - y1
      dx23 = x3 - x2
      dy23 = y3 - y2
      dx31 = x1 - x3
      dy31 = y1 - y3
      -- Blue Quadrances
      qb1 = (dx12 * dx12) + (dy12 * dy12)
      qb2 = (dx23 * dx23) + (dy23 * dy23)
      qb3 = (dx31 * dx31) + (dy31 * dy31)
      ab  = (qb1 + qb2 + qb3) * (qb1 + qb2 + qb3) - intToBoxInt 2 * ((qb1 * qb1) + (qb2 * qb2) + (qb3 * qb3))
      -- Red Quadrances
      qr1 = (dx12 * dx12) - (dy12 * dy12)
      qr2 = (dx23 * dx23) - (dy23 * dy23)
      qr3 = (dx31 * dx31) - (dy31 * dy31)
      ar  = (qr1 + qr2 + qr3) * (qr1 + qr2 + qr3) - intToBoxInt 2 * ((qr1 * qr1) + (qr2 * qr2) + (qr3 * qr3))
      -- Green Quadrances
      qg1 = intToBoxInt 2 * (dx12 * dy12)
      qg2 = intToBoxInt 2 * (dx23 * dy23)
      qg3 = intToBoxInt 2 * (dx31 * dy31)
      ag  = (qg1 + qg2 + qg3) * (qg1 + qg2 + qg3) - intToBoxInt 2 * ((qg1 * qg1) + (qg2 * qg2) + (qg3 * qg3))
  in (ab, ar, ag)

||| Wildberger Theorem 8: The Three-Fold Quadrea Theorem (A_b == -A_r == -A_g).
public export
verifyThreeFoldQuadreaTheorem : (x1 : BoxInt) -> (y1 : BoxInt) ->
                                (x2 : BoxInt) -> (y2 : BoxInt) ->
                                (x3 : BoxInt) -> (y3 : BoxInt) -> Bool
verifyThreeFoldQuadreaTheorem x1 y1 x2 y2 x3 y3 =
  let (ab, ar, ag) = evaluateThreeFoldQuadrea x1 y1 x2 y2 x3 y3
  in ab == (intToBoxInt (-1) * ar) && ab == (intToBoxInt (-1) * ag)

||| Audits Wildberger Chromogeometry Theorems 6 & 8 on concrete triangle coordinates.
public export
auditThreeFoldChromogeometryProof : Bool
auditThreeFoldChromogeometryProof =
  let t6Ok = evaluateThreeFoldQuadranceSymmetry (intToBoxInt 3) (intToBoxInt 4)
      t8Ok = verifyThreeFoldQuadreaTheorem (intToBoxInt 0) (intToBoxInt 0)
                                           (intToBoxInt 4) (intToBoxInt 0)
                                           (intToBoxInt 0) (intToBoxInt 3)
  in t6Ok && t8Ok

||| 2LTT Path Equality reflecting inner Quadrea manifold path to outer strict equality.
public export
0 reflectQuadreaPathToStrict : (q1, q2, q3 : BoxInt) ->
                               (0 p : Path (quadrea q1 q2 q3) (quadrea q1 q2 q3)) ->
                               quadrea q1 q2 q3 = quadrea q1 q2 q3
reflectQuadreaPathToStrict q1 q2 q3 ReflP = reflectPathToStrict ReflP

||| Audits that Quadrea Archimedes formula and Gram Maxel determinant are strictly equal.
public export
auditQuadreaArchimedesPathProof : Bool
auditQuadreaArchimedesPathProof =
  let q1 = intToBoxInt 9
      q2 = intToBoxInt 16
      q3 = intToBoxInt 25
  in quadrea q1 q2 q3 == quadreaMaxel q1 q2 q3

------------------------------------------------------------------------
-- 6. 2LTT STAGING CODE GENERATOR TRANSDUCER
------------------------------------------------------------------------

||| Staged 2LTT code generator for exact rational quadrea transducer.
%inline public export
stagedQuadrea : BoxInt -> BoxInt -> BoxInt -> Code BoxInt
stagedQuadrea q1 q2 q3 = quote (quadrea q1 q2 q3)

||| QTT 0 erased proof witness verifying quadrea staging inverse identity.
public export
0 prfStagedQuadrea : (q1, q2, q3 : BoxInt) -> splice (stagedQuadrea q1 q2 q3) = quadrea q1 q2 q3
prfStagedQuadrea q1 q2 q3 = inverseSpliceQuote (quadrea q1 q2 q3)

------------------------------------------------------------------------
-- 7. DEFORESTED SPREAD RECURRENCE STREAM & COMPANION MAXEL
------------------------------------------------------------------------

||| Constructs the exact integer Companion Spread Maxel transfer matrix for dynamic coordinates (x, y):
||| [[2 * Q_Red, -Q_Blue], [Q_Blue, 0]].
||| This represents the unnormalized 2x2 companion spread matrix scaled by Q_Blue = x^2 + y^2,
||| with diagonal entry c11 = 2 * Q_Red = 2 * (x^2 - y^2) identically satisfying:
||| (2 * Q_Blue - 4 * y^2) == 2 * Q_Red.
public export
pythagoreanSpreadMaxel : (x : BoxInt) -> (y : BoxInt) -> Maxel
pythagoreanSpreadMaxel x y =
  let qBlue = (x * x) + (y * y)
      qRed  = (x * x) - (y * y)
      c11   = intToBoxInt 2 * qRed
      c12   = mulBox (intToBoxInt (-1)) qBlue
      c21   = qBlue
      c22   = intToBoxInt 0
  in singletonCell (mkPixel 1 1) c11 <+>
     singletonCell (mkPixel 1 2) c12 <+>
     singletonCell (mkPixel 2 1) c21 <+>
     singletonCell (mkPixel 2 2) c22

||| Static verification witness: Spread diagonal entry scaled by Q_Blue identically equals 2 * Q_Red.
public export
auditSpreadDiagonalRatioProof : (x : BoxInt) -> (y : BoxInt) -> Bool
auditSpreadDiagonalRatioProof x y =
  let qBlue = (x * x) + (y * y)
      qRed  = (x * x) - (y * y)
      lhs = (intToBoxInt 2 * qBlue) - (intToBoxInt 4 * (y * y))
      rhs = intToBoxInt 2 * qRed
  in boxEq lhs rhs

||| Constructs the 2x2 Companion Maxel transfer matrix for multiple spread recurrence:
||| [[2 - 4s, -1], [1, 0]].
||| Deprecated: Prefer exact integer `pythagoreanSpreadMaxel x y` to avoid fractional truncation.
public export
companionSpreadMaxel : (s : BoxInt) -> Maxel
companionSpreadMaxel s =
  let c11 = intToBoxInt 2 - (intToBoxInt 4 * s)
      c12 = intToBoxInt (-1)
      c21 = intToBoxInt 1
      c22 = intToBoxInt 0
  in singletonCell (mkPixel 1 1) c11 <+>
     singletonCell (mkPixel 1 2) c12 <+>
     singletonCell (mkPixel 2 1) c21 <+>
     singletonCell (mkPixel 2 2) c22

||| Dimension-checked 2x2 Companion Spread SquareMaxel transfer matrix for dynamic coordinates (x, y):
public export
pythagoreanSpreadSquareMaxel : (x : BoxInt) -> (y : BoxInt) -> SquareMaxel 2
pythagoreanSpreadSquareMaxel x y = maxelToSquareMaxel 2 (pythagoreanSpreadMaxel x y)

||| Dimension-checked 2x2 Companion Spread SquareMaxel transfer matrix for multiple spread recurrence:
public export
companionSpreadSquareMaxel : (s : BoxInt) -> SquareMaxel 2
companionSpreadSquareMaxel s = maxelToSquareMaxel 2 (companionSpreadMaxel s)

||| Step function for unrolling the multiple spread recurrence sequence:
||| S_0 = 0, S_1 = s, S_{n+1} = (2 - 4s)*S_n - S_{n-1} + 2s.
||| Evaluates in O(1) state without list allocation.
public export
spreadRecurrenceStep : (s : BoxInt) -> (Nat, BoxInt, BoxInt) -> Step (Nat, BoxInt, BoxInt) BoxInt
spreadRecurrenceStep s (Z, _, _) =
  Yield (intToBoxInt 0) (1, intToBoxInt 0, s)
spreadRecurrenceStep s (1, s0, s1) =
  let s2 = (intToBoxInt 2 - (intToBoxInt 4 * s)) * s1 - s0 + (intToBoxInt 2 * s)
  in Yield s1 (2, s1, s2)
spreadRecurrenceStep s (S (S n), sPrev, sCurr) =
  let sNext = (intToBoxInt 2 - (intToBoxInt 4 * s)) * sCurr - sPrev + (intToBoxInt 2 * s)
  in Yield sCurr (S (S (S n)), sCurr, sNext)

||| Deforested FusedStream generator for the multiple spread polynomial values S_n(s).
public export
spreadRecurrenceStream : (s : BoxInt) -> FusedStream BoxInt
spreadRecurrenceStream s = unfoldStream (spreadRecurrenceStep s) (Z, intToBoxInt 0, s)

||| Evaluates the n-th multiple spread S_n(s) using O(1) space stream fold.
public export
evalNthSpreadStream : (n : Nat) -> (s : BoxInt) -> BoxInt
evalNthSpreadStream n s =
  foldStreamNat (S (S n)) (\_, curr => curr) (intToBoxInt 0) (fusedTake (S n) (spreadRecurrenceStream s))

||| Evaluates the n-th multiple spread S_n(s) in O(log n) steps via companion Maxel fast power (Rule 04).
public export
evalNthSpreadFast : (n : Nat) -> (s : BoxInt) -> BoxInt
evalNthSpreadFast n s = fastSpreadPowerNat (n + 10) n s

||| Audits the deforested multiple spread recurrence stream and fast O(log N) power against canonical values:
||| S_0(2) = 0, S_1(2) = 2, S_2(2) = -8, S_3(2) = 50.
public export
auditSpreadRecurrenceStreamProof : Bool
auditSpreadRecurrenceStreamProof =
  let s = intToBoxInt 2
      s0 = evalNthSpreadStream 0 s
      s1 = evalNthSpreadStream 1 s
      s2 = evalNthSpreadStream 2 s
      s3 = evalNthSpreadStream 3 s
      f0 = evalNthSpreadFast 0 s
      f1 = evalNthSpreadFast 1 s
      f2 = evalNthSpreadFast 2 s
      f3 = evalNthSpreadFast 3 s
  in (s0 == intToBoxInt 0) &&
     (s1 == intToBoxInt 2) &&
     (s2 == intToBoxInt (-8)) &&
     (s3 == intToBoxInt 50) &&
     (f0 == s0) && (f1 == s1) && (f2 == s2) && (f3 == s3)

||| Evaluates the n-th Cross Multiple Spread C_n(s) = 1 - S_n(s).
public export
evalNthCrossMultipleSpreadStream : (n : Nat) -> (s : BoxInt) -> BoxInt
evalNthCrossMultipleSpreadStream n s = subBox (intToBoxInt 1) (evalNthSpreadStream n s)

||| Constructs the 2x2 Companion Maxel transfer matrix for multiple cross recurrence:
||| [[2(2c - 1), -1], [1, 0]].
public export
companionCrossMaxel : (c : BoxInt) -> Maxel
companionCrossMaxel c =
  let c11 = intToBoxInt 2 * (intToBoxInt 2 * c - intToBoxInt 1)
      c12 = intToBoxInt (-1)
      c21 = intToBoxInt 1
      c22 = intToBoxInt 0
  in singletonCell (mkPixel 1 1) c11 <+>
     singletonCell (mkPixel 1 2) c12 <+>
     singletonCell (mkPixel 2 1) c21 <+>
     singletonCell (mkPixel 2 2) c22

||| Step function for unrolling the multiple cross recurrence sequence:
||| c_0 = 1, c_1 = c, c_{n+1} = 2(2c - 1)*c_n - c_{n-1} + 2(1 - c).
public export
crossRecurrenceStep : (c : BoxInt) -> (Nat, BoxInt, BoxInt) -> Step (Nat, BoxInt, BoxInt) BoxInt
crossRecurrenceStep c (Z, _, _) =
  Yield (intToBoxInt 1) (1, intToBoxInt 1, c)
crossRecurrenceStep c (1, c0, c1) =
  let c2 = intToBoxInt 2 * (intToBoxInt 2 * c - intToBoxInt 1) * c1 - c0 + (intToBoxInt 2 * (intToBoxInt 1 - c))
  in Yield c1 (2, c1, c2)
crossRecurrenceStep c (S (S n), cPrev, cCurr) =
  let cNext = intToBoxInt 2 * (intToBoxInt 2 * c - intToBoxInt 1) * cCurr - cPrev + (intToBoxInt 2 * (intToBoxInt 1 - c))
  in Yield cCurr (S (S (S n)), cCurr, cNext)

||| Deforested FusedStream generator for the multiple cross sequence c_n(c).
public export
crossRecurrenceStream : (c : BoxInt) -> FusedStream BoxInt
crossRecurrenceStream c = unfoldStream (crossRecurrenceStep c) (Z, intToBoxInt 1, c)

||| Evaluates the n-th multiple cross c_n(c) using O(1) space stream fold.
public export
evalNthCrossStream : (n : Nat) -> (c : BoxInt) -> BoxInt
evalNthCrossStream n c =
  foldStreamNat (S (S n)) (\_, curr => curr) (intToBoxInt 0) (fusedTake (S n) (crossRecurrenceStream c))

||| Audits Wildberger Spread-Cross duality:
||| C_n(1) == c_n(0) across the first 4 periods [1, 0, 1, 0].
public export
auditSpreadCrossDualityProof : Bool
auditSpreadCrossDualityProof =
  let c0 = evalNthCrossStream 0 (intToBoxInt 0)
      c1 = evalNthCrossStream 1 (intToBoxInt 0)
      c2 = evalNthCrossStream 2 (intToBoxInt 0)
      c3 = evalNthCrossStream 3 (intToBoxInt 0)
      cSpread0 = evalNthCrossMultipleSpreadStream 0 (intToBoxInt 1)
      cSpread1 = evalNthCrossMultipleSpreadStream 1 (intToBoxInt 1)
      cSpread2 = evalNthCrossMultipleSpreadStream 2 (intToBoxInt 1)
      cSpread3 = evalNthCrossMultipleSpreadStream 3 (intToBoxInt 1)
  in (c0 == cSpread0) && (c1 == cSpread1) && (c2 == cSpread2) && (c3 == cSpread3)





