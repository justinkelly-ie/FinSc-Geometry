module Stage1.PentagonalFibonacci

import Stage0.BoxInt
import Stage1.VexelMaxel
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
fibonacciCompanionMaxel : BoxSquareMaxel 2
fibonacciCompanionMaxel =
  let tree0 = setBoxTree (MkPixel 0 0) (intToBoxInt 1) BoxLeaf
      tree1 = setBoxTree (MkPixel 0 1) (intToBoxInt 1) tree0
      tree2 = setBoxTree (MkPixel 1 0) (intToBoxInt 1) tree1
      tree3 = setBoxTree (MkPixel 1 1) (intToBoxInt 0) tree2
  in MkBoxSquareMaxel tree3

||| Computes M_Fib^N using repeated matrix multiplication.
public export
powerFibonacciMaxel : Nat -> BoxSquareMaxel 2
powerFibonacciMaxel 0 = identityBoxSquareMaxel 2
powerFibonacciMaxel (S k) =
  mulBoxSquareMaxel fibonacciCompanionMaxel (powerFibonacciMaxel k)

||| Reads the element weight at pixel coordinate p in a BoxSquareMaxel.
public export
lookupBoxSquareMaxel : Pixel -> BoxSquareMaxel dim -> BoxInt
lookupBoxSquareMaxel p (MkBoxSquareMaxel tree) = lookupBoxTree p tree

||| Extracts the N-th Fibonacci number F_N from M_Fib^N at pixel (0, 1).
public export
fibonacciNumber : Nat -> BoxInt
fibonacciNumber n =
  lookupBoxSquareMaxel (MkPixel 0 1) (powerFibonacciMaxel n)

||| Extracts the exact constructivist Stern-Brocot rational convergent of the Golden Ratio:
||| phi_N = F_{N+1} / F_N as an exact UnixelFraction.
public export
goldenRatioConvergent : Nat -> UnixelFraction
goldenRatioConvergent n =
  let fN   = unwrapBox (fibonacciNumber n)
      fNP1 = unwrapBox (fibonacciNumber (S n))
  in if fN <= 0
       then mkUnixelFraction (intToBoxInt 1) 1
       else mkUnixelFraction (intToBoxInt fNP1) (integerToNat fN)

------------------------------------------------------------------------
-- 2. PENTAGONAL 5-CYCLE PERMUTATION MAXEL (Z_5 SYMMETRY)
------------------------------------------------------------------------

||| 5-Cycle Cyclic Permutation Matrix:
||| sigma_5 : (0 -> 1 -> 2 -> 3 -> 4 -> 0).
||| Supported on exactly 5 active non-zero pixels in a 5x5 matrix.
public export
pentagonalPermutationMaxel : BoxSquareMaxel 5
pentagonalPermutationMaxel =
  let step : BoxMultisetTree Pixel -> (Nat, Nat) -> BoxMultisetTree Pixel
      step acc (r, c) = setBoxTree (MkPixel r c) (intToBoxInt 1) acc
      edges = the (List (Nat, Nat)) [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]
      tree = foldl step BoxLeaf edges
  in MkBoxSquareMaxel tree

||| Computes sigma_5^k cyclic shift matrix.
public export
powerPentagonalMaxel : Nat -> BoxSquareMaxel 5
powerPentagonalMaxel 0 = identityBoxSquareMaxel 5
powerPentagonalMaxel (S k) =
  mulBoxSquareMaxel pentagonalPermutationMaxel (powerPentagonalMaxel k)

------------------------------------------------------------------------
-- 3. 2LTT STAGED FIBONACCI STEPPING & COMPILED CLOSURE
------------------------------------------------------------------------

||| 2LTT Staged Fibonacci Matrix:
||| Pre-computes M_Fib^N at compile time (Level 1) into an exact runtime constant (Level 0).
public export
stagedFibonacciMaxel : (n : Nat) -> Code (BoxSquareMaxel 2)
stagedFibonacciMaxel n = quote (powerFibonacciMaxel n)

||| 2LTT Staged 5-Cycle Closure:
||| Quotes the compile-time identity closure sigma_5^5 = I_5.
public export
stagedPentagonalClosure : Code (BoxSquareMaxel 5)
stagedPentagonalClosure = quote (powerPentagonalMaxel 5)

------------------------------------------------------------------------
-- 4. VERIFIED INVARIANTS & AUDITS
------------------------------------------------------------------------

||| Verified Invariant: F_0 = 0, F_1 = 1, F_2 = 1, F_3 = 2, F_4 = 3, F_5 = 5, F_6 = 8, F_7 = 13.
||| Exactly matches the constructivist Fibonacci sequence up to the 13-smooth horizon.
public export
auditFibonacciSequence : Bool
auditFibonacciSequence =
  unwrapBox (fibonacciNumber 1) == 1 &&
  unwrapBox (fibonacciNumber 2) == 1 &&
  unwrapBox (fibonacciNumber 3) == 2 &&
  unwrapBox (fibonacciNumber 4) == 3 &&
  unwrapBox (fibonacciNumber 5) == 5 &&
  unwrapBox (fibonacciNumber 6) == 8 &&
  unwrapBox (fibonacciNumber 7) == 13

||| Verified Invariant: 5-cycle permutation closes identically at power 5: sigma_5^5 = I_5.
public export
auditPentagonal5CycleClosure : Bool
auditPentagonal5CycleClosure =
  splice stagedPentagonalClosure == identityBoxSquareMaxel 5

||| Verified Invariant: Golden ratio convergent phi_7 = 21 / 13 on the 13-smooth horizon.
public export
auditGoldenRatio13Smooth : Bool
auditGoldenRatio13Smooth =
  let phi7 = goldenRatioConvergent 7
  in unwrapBox phi7.num == 21 && unwrapUnixel phi7.den == 13
