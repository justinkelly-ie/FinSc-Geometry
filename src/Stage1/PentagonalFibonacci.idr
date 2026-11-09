module Stage1.PentagonalFibonacci

import Stage0.BoxInt
import Stage0.Token
import Stage1.Basis.Coordinate
import Stage1.MultisetTree
import Stage0.PrimeMultiset
import Stage1.UnixelFraction
import Stage1.TypeTheory.Staging
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. 2x2 FIBONACCI COMPANION TRANSFER MAXEL & GOLDEN RATIO CONVERGENCE
------------------------------------------------------------------------

||| 2x2 Fibonacci Companion Transfer Matrix:
||| M_Fib = [[1, 1], [1, 0]]
||| Satisfies M_Fib^N = [[F_{N+1}, F_N], [F_N, F_{N-1}]].
public export
fibonacciCompanionMaxel : SquareMaxel 2
fibonacciCompanionMaxel =
  let tree0 = setCellMultiset (MkPixel 0 0) (intToBoxInt 1) BoxLeaf
      tree1 = setCellMultiset (MkPixel 0 1) (intToBoxInt 1) tree0
      tree2 = setCellMultiset (MkPixel 1 0) (intToBoxInt 1) tree1
      tree3 = setCellMultiset (MkPixel 1 1) (intToBoxInt 0) tree2
  in MkSquareMaxel tree3

||| Computes M_Fib^N using repeated matrix multiplication via symbolic (*).
public export
powerFibonacciMaxel : Nat -> SquareMaxel 2
powerFibonacciMaxel 0 = 1
powerFibonacciMaxel (S k) =
  fibonacciCompanionMaxel * (powerFibonacciMaxel k)

||| Reads the element weight at pixel coordinate p in a SquareMaxel.
public export
lookupSquareMaxel : Pixel -> SquareMaxel dim -> BoxInt
lookupSquareMaxel p (MkSquareMaxel tree) = lookupCellMultiset p tree

||| Extracts the N-th Fibonacci number F_N from M_Fib^N at pixel (0, 1).
public export
fibonacciNumber : Nat -> BoxInt
fibonacciNumber n =
  lookupSquareMaxel (MkPixel 0 1) (powerFibonacciMaxel n)

||| Extracts the exact constructivist Stern-Brocot rational convergent of the Golden Ratio:
||| phi_N = F_{N+1} / F_N as an exact UnixelFraction.
public export
goldenRatioConvergent : Nat -> UnixelFraction
goldenRatioConvergent n =
  let fN   = fibonacciNumber n
      fNP1 = fibonacciNumber (S n)
  in if fN <= intToBoxInt 0
       then mkUnixelFraction (intToBoxInt 1) 1
       else mkUnixelFraction fNP1 (boxToNat fN)

------------------------------------------------------------------------
-- 2. PENTAGONAL 5-CYCLE PERMUTATION MAXEL (Z_5 SYMMETRY)
------------------------------------------------------------------------

||| 5-Cycle Cyclic Permutation Matrix:
||| sigma_5 : (0 -> 1 -> 2 -> 3 -> 4 -> 0).
||| Supported on exactly 5 active non-zero pixels in a 5x5 matrix.
public export
pentagonalPermutationMaxel : SquareMaxel 5
pentagonalPermutationMaxel =
  let step : BoxMultisetTree Pixel -> (Nat, Nat) -> BoxMultisetTree Pixel
      step acc (r, c) = setCellMultiset (MkPixel r c) (intToBoxInt 1) acc
      edges = the (List (Nat, Nat)) [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]
      tree = foldl step BoxLeaf edges
  in MkSquareMaxel tree

||| Computes sigma_5^k cyclic shift matrix via symbolic (*).
public export
powerPentagonalMaxel : Nat -> SquareMaxel 5
powerPentagonalMaxel 0 = 1
powerPentagonalMaxel (S k) =
  pentagonalPermutationMaxel * (powerPentagonalMaxel k)

------------------------------------------------------------------------
-- 3. 2LTT STAGED FIBONACCI STEPPING & COMPILED CLOSURE
------------------------------------------------------------------------

||| 2LTT Staged Fibonacci Matrix:
||| Pre-computes M_Fib^N at compile time (Level 1) into an exact runtime constant (Level 0).
public export
stagedFibonacciMaxel : (n : Nat) -> Code (SquareMaxel 2)
stagedFibonacciMaxel n = quote (powerFibonacciMaxel n)

||| 2LTT Staged 5-Cycle Closure:
||| Quotes the compile-time identity closure sigma_5^5 = I_5.
public export
stagedPentagonalClosure : Code (SquareMaxel 5)
stagedPentagonalClosure = quote (powerPentagonalMaxel 5)

------------------------------------------------------------------------
-- 4. VERIFIED INVARIANTS & AUDITS
------------------------------------------------------------------------

||| Verified Invariant: F_0 = 0, F_1 = 1, F_2 = 1, F_3 = 2, F_4 = 3, F_5 = 5, F_6 = 8, F_7 = 13.
||| Exactly matches the constructivist Fibonacci sequence up to the 13-smooth horizon.
public export
auditFibonacciSequence : Bool
auditFibonacciSequence =
  fibonacciNumber 1 == intToBoxInt 1 &&
  fibonacciNumber 2 == intToBoxInt 1 &&
  fibonacciNumber 3 == intToBoxInt 2 &&
  fibonacciNumber 4 == intToBoxInt 3 &&
  fibonacciNumber 5 == intToBoxInt 5 &&
  fibonacciNumber 6 == intToBoxInt 8 &&
  fibonacciNumber 7 == intToBoxInt 13

||| Verified Invariant: 5-cycle permutation closes identically at power 5: sigma_5^5 = I_5.
public export
auditPentagonal5CycleClosure : Bool
auditPentagonal5CycleClosure =
  splice stagedPentagonalClosure == identitySquareMaxel 5

||| Verified Invariant: Golden ratio convergent phi_7 = 21 / 13 on the 13-smooth horizon.
public export
auditGoldenRatio13Smooth : Bool
auditGoldenRatio13Smooth =
  let phi7 = goldenRatioConvergent 7
  in phi7.num == intToBoxInt 21 && phi7.den == MkUnixel 13

public export
0 prfFibonacciSequenceQTT : Stage1.PentagonalFibonacci.auditFibonacciSequence = True
prfFibonacciSequenceQTT = Refl

public export
0 prfGoldenRatio13SmoothQTT : Stage1.PentagonalFibonacci.auditGoldenRatio13Smooth = True
prfGoldenRatio13SmoothQTT = Refl
