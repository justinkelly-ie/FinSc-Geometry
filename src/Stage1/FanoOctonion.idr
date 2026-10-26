module Stage1.FanoOctonion

import Stage0.BoxInt
import Stage1.Basis.Coordinate
import Stage1.MultisetTree
import Stage0.PrimeMultiset
import Stage1.TypeTheory.Staging
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. CONSTRUCTIVIST FANO PLANE P^2(F_2) & 7 IMAGINARY OCTONION UNITS
------------------------------------------------------------------------

||| The 7 imaginary basis units of the Octonion algebra O,
||| indexed canonically by the 7 points of the Fano plane P^2(F_2).
public export
data FanoPoint = E1 | E2 | E3 | E4 | E5 | E6 | E7

public export
Eq FanoPoint where
  E1 == E1 = True
  E2 == E2 = True
  E3 == E3 = True
  E4 == E4 = True
  E5 == E5 = True
  E6 == E6 = True
  E7 == E7 = True
  _  == _  = False

public export
Show FanoPoint where
  show E1 = "e1"
  show E2 = "e2"
  show E3 = "e3"
  show E4 = "e4"
  show E5 = "e5"
  show E6 = "e6"
  show E7 = "e7"

||| Zero-based Nat index of a Fano point (0 to 6).
public export
fanoPointToNat : FanoPoint -> Nat
fanoPointToNat E1 = 0
fanoPointToNat E2 = 1
fanoPointToNat E3 = 2
fanoPointToNat E4 = 3
fanoPointToNat E5 = 4
fanoPointToNat E6 = 5
fanoPointToNat E7 = 6

||| All 7 points of the Fano plane.
public export
allFanoPoints : Vect 7 FanoPoint
allFanoPoints = [E1, E2, E3, E4, E5, E6, E7]

||| A cyclically oriented line in the Fano plane: (a -> b -> c -> a).
public export
record FanoLine where
  constructor MkFanoLine
  ptA : FanoPoint
  ptB : FanoPoint
  ptC : FanoPoint

public export
Show FanoLine where
  show (MkFanoLine a b c) = "(" ++ show a ++ "->" ++ show b ++ "->" ++ show c ++ ")"

||| The canonical 7 oriented lines of the Fano plane:
||| L1 = (1, 2, 4), L2 = (2, 3, 5), L3 = (3, 4, 6), L4 = (4, 5, 7),
||| L5 = (5, 6, 1), L6 = (6, 7, 2), L7 = (7, 1, 3).
public export
fanoLines : Vect 7 FanoLine
fanoLines =
  [ MkFanoLine E1 E2 E4
  , MkFanoLine E2 E3 E5
  , MkFanoLine E3 E4 E6
  , MkFanoLine E4 E5 E7
  , MkFanoLine E5 E6 E1
  , MkFanoLine E6 E7 E2
  , MkFanoLine E7 E1 E3
  ]

||| Tests if a point lies on an oriented Fano line.
public export
pointOnLine : FanoPoint -> FanoLine -> Bool
pointOnLine p (MkFanoLine a b c) = p == a || p == b || p == c

------------------------------------------------------------------------
-- 2. FANO INCIDENCE MATRIX & 2LTT STAGING
------------------------------------------------------------------------

||| Computes the 7x7 binary incidence matrix of the Fano plane:
||| M_{p, l} = 1 if point p is incident to line l, else 0.
||| Supported on exactly 21 active non-zero pixels (3 points * 7 lines).
public export
fanoIncidenceMaxel : BoxSquareMaxel 7
fanoIncidenceMaxel =
  let pts = toList allFanoPoints
      indexedLines : List (Nat, FanoLine)
      indexedLines = [ (0, MkFanoLine E1 E2 E4)
                     , (1, MkFanoLine E2 E3 E5)
                     , (2, MkFanoLine E3 E4 E6)
                     , (3, MkFanoLine E4 E5 E7)
                     , (4, MkFanoLine E5 E6 E1)
                     , (5, MkFanoLine E6 E7 E2)
                     , (6, MkFanoLine E7 E1 E3)
                     ]
      pairs = [ (p, lIdx, line) | p <- pts, (lIdx, line) <- indexedLines ]
      step : BoxMultisetTree Pixel -> (FanoPoint, Nat, FanoLine) -> BoxMultisetTree Pixel
      step acc (p, lIdx, line) =
        if pointOnLine p line
           then setBoxTree (MkPixel (fanoPointToNat p) lIdx) (intToBoxInt 1) acc
           else acc
      tree = foldl step BoxLeaf pairs
  in MkBoxSquareMaxel tree

||| 2LTT Staged compilation of the Fano incidence matrix at Level 1.
public export
stagedFanoIncidenceMaxel : Code (BoxSquareMaxel 7)
stagedFanoIncidenceMaxel = quote fanoIncidenceMaxel

------------------------------------------------------------------------
-- 3. OCTONION MULTIPLICATION & FANO ORIENTATION
------------------------------------------------------------------------

||| Evaluates the product of two imaginary Fano units:
||| e_i * e_i = -1 (sign -1, no unit).
||| e_i * e_j = +e_k if (i, j, k) is a cyclically ordered Fano line.
||| e_i * e_j = -e_k if (j, i, k) is a cyclically ordered Fano line.
public export
mulFanoPoints : FanoPoint -> FanoPoint -> (BoxInt, Maybe FanoPoint)
mulFanoPoints p1 p2 =
  if p1 == p2
     then (intToBoxInt (-1), Nothing)
     else case findLine p1 p2 of
            Just (sign, p3) => (intToBoxInt sign, Just p3)
            Nothing         => (intToBoxInt 0, Nothing)
  where
    checkLine : FanoPoint -> FanoPoint -> FanoLine -> Maybe (Integer, FanoPoint)
    checkLine a b (MkFanoLine x y z) =
      if a == x && b == y then Just (1, z)
      else if a == y && b == z then Just (1, x)
      else if a == z && b == x then Just (1, y)
      else if a == y && b == x then Just (-1, z)
      else if a == z && b == y then Just (-1, x)
      else if a == x && b == z then Just (-1, y)
      else Nothing

    findLine : FanoPoint -> FanoPoint -> Maybe (Integer, FanoPoint)
    findLine a b =
      foldl (\acc, l => case acc of
                          Just res => Just res
                          Nothing  => checkLine a b l)
            Nothing
            fanoLines

||| Complete 8D Octonion algebra (1 real scalar + 7 imaginary units):
||| X = x0 + x1 e1 + x2 e2 + x3 e3 + x4 e4 + x5 e5 + x6 e6 + x7 e7.
public export
record Octonion where
  constructor MkOctonion
  s0 : BoxInt
  e1 : BoxInt
  e2 : BoxInt
  e3 : BoxInt
  e4 : BoxInt
  e5 : BoxInt
  e6 : BoxInt
  e7 : BoxInt

public export
Eq Octonion where
  (MkOctonion a0 a1 a2 a3 a4 a5 a6 a7) == (MkOctonion b0 b1 b2 b3 b4 b5 b6 b7) =
    a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3 &&
    a4 == b4 && a5 == b5 && a6 == b6 && a7 == b7

public export
Show Octonion where
  show (MkOctonion a0 a1 a2 a3 a4 a5 a6 a7) =
    "Oct(" ++ show a0 ++ " + " ++
    show a1 ++ "e1 + " ++ show a2 ++ "e2 + " ++ show a3 ++ "e3 + " ++
    show a4 ++ "e4 + " ++ show a5 ++ "e5 + " ++ show a6 ++ "e6 + " ++
    show a7 ++ "e7)"

public export
zeroOctonion : Octonion
zeroOctonion =
  MkOctonion 0 0 0 0 0 0 0 0

public export
unitOctonion : Octonion
unitOctonion =
  MkOctonion 1 0 0 0 0 0 0 0

public export
basisOctonion : FanoPoint -> Octonion
basisOctonion E1 = MkOctonion 0 1 0 0 0 0 0 0
basisOctonion E2 = MkOctonion 0 0 1 0 0 0 0 0
basisOctonion E3 = MkOctonion 0 0 0 1 0 0 0 0
basisOctonion E4 = MkOctonion 0 0 0 0 1 0 0 0
basisOctonion E5 = MkOctonion 0 0 0 0 0 1 0 0
basisOctonion E6 = MkOctonion 0 0 0 0 0 0 1 0
basisOctonion E7 = MkOctonion 0 0 0 0 0 0 0 1

public export
addOctonion : Octonion -> Octonion -> Octonion
addOctonion (MkOctonion a0 a1 a2 a3 a4 a5 a6 a7) (MkOctonion b0 b1 b2 b3 b4 b5 b6 b7) =
  MkOctonion (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3)
             (a4 + b4) (a5 + b5) (a6 + b6) (a7 + b7)

public export
negateOctonion : Octonion -> Octonion
negateOctonion (MkOctonion a0 a1 a2 a3 a4 a5 a6 a7) =
  MkOctonion (-a0) (-a1) (-a2) (-a3) (-a4) (-a5) (-a6) (-a7)

||| Octonion Conjugate: (s, v)* = (s, -v).
public export
conjugateOctonion : Octonion -> Octonion
conjugateOctonion (MkOctonion a0 a1 a2 a3 a4 a5 a6 a7) =
  MkOctonion a0 (-a1) (-a2) (-a3) (-a4) (-a5) (-a6) (-a7)

||| Multiplies two full 8D Octonions using the Fano plane multiplication rules.
public export
mulOctonion : Octonion -> Octonion -> Octonion
mulOctonion x y =
  let -- Scalar-scalar
      r0 = x.s0 * y.s0 - (x.e1 * y.e1 + x.e2 * y.e2 + x.e3 * y.e3 +
                          x.e4 * y.e4 + x.e5 * y.e5 + x.e6 * y.e6 + x.e7 * y.e7)
      -- Lines: (1,2,4), (2,3,5), (3,4,6), (4,5,7), (5,6,1), (6,7,2), (7,1,3)
      r1 = x.s0 * y.e1 + x.e1 * y.s0 + (x.e2 * y.e4 - x.e4 * y.e2) +
           (x.e5 * y.e6 - x.e6 * y.e5) + (x.e7 * y.e3 - x.e3 * y.e7)
      r2 = x.s0 * y.e2 + x.e2 * y.s0 + (x.e3 * y.e5 - x.e5 * y.e3) +
           (x.e6 * y.e7 - x.e7 * y.e6) + (x.e4 * y.e1 - x.e1 * y.e4)
      r3 = x.s0 * y.e3 + x.e3 * y.s0 + (x.e4 * y.e6 - x.e6 * y.e4) +
           (x.e7 * y.e1 - x.e1 * y.e7) + (x.e5 * y.e2 - x.e2 * y.e5)
      r4 = x.s0 * y.e4 + x.e4 * y.s0 + (x.e5 * y.e7 - x.e7 * y.e5) +
           (x.e1 * y.e2 - x.e2 * y.e1) + (x.e6 * y.e3 - x.e3 * y.e6)
      r5 = x.s0 * y.e5 + x.e5 * y.s0 + (x.e6 * y.e1 - x.e1 * y.e6) +
           (x.e2 * y.e3 - x.e3 * y.e2) + (x.e7 * y.e4 - x.e4 * y.e7)
      r6 = x.s0 * y.e6 + x.e6 * y.s0 + (x.e7 * y.e2 - x.e2 * y.e7) +
           (x.e3 * y.e4 - x.e4 * y.e3) + (x.e1 * y.e5 - x.e5 * y.e1)
      r7 = x.s0 * y.e7 + x.e7 * y.s0 + (x.e1 * y.e3 - x.e3 * y.e1) +
           (x.e4 * y.e5 - x.e5 * y.e4) + (x.e2 * y.e6 - x.e6 * y.e2)
  in MkOctonion r0 r1 r2 r3 r4 r5 r6 r7

------------------------------------------------------------------------
-- 4. 2LTT STAGED VERIFICATION OF OCTONION NON-ASSOCIATIVITY
------------------------------------------------------------------------

||| Proves that the Octonion division algebra is strictly non-associative:
||| (e1 * e2) * e3 /= e1 * (e2 * e3).
||| Specifically: (e1 * e2) * e3 = e4 * e3 = -e6, while e1 * (e2 * e3) = e1 * e5 = +e6.
||| The associator is [e1, e2, e3] = -2 e6 /= 0.
public export
auditOctonionNonAssociativity : Bool
auditOctonionNonAssociativity =
  let o1 = basisOctonion E1
      o2 = basisOctonion E2
      o3 = basisOctonion E3
      lhs = mulOctonion (mulOctonion o1 o2) o3
      rhs = mulOctonion o1 (mulOctonion o2 o3)
      associator = addOctonion lhs (negateOctonion rhs)
  in (lhs /= rhs) && associator == MkOctonion 0 0 0 0 0 0 (-2) 0

||| Verified Invariant: Fano incidence matrix has exactly 21 active entries (3 per line).
public export
auditFanoIncidenceCount : Bool
auditFanoIncidenceCount =
  let MkBoxSquareMaxel tree = fanoIncidenceMaxel
      entries = boxTreeToList tree
  in length entries == 21
