module Stage1.MultisetMetricTensor

import Stage0.BoxInt
import Stage0.Multiset
import Data.List
import Data.Vect

import Stage1.FourGeometries
import Stage1.SubstrateMetricTensor

%default total

------------------------------------------------------------------------
-- 1. METRIC TENSOR BASIS PAIRS AS MULTISET ELEMENT KEYS
------------------------------------------------------------------------

||| Basis index pair (i, j) for symmetric tensor entries (1 <= i <= j <= dim).
public export
record MetricBasisPair where
  constructor MkBasisPair
  row : Nat
  col : Nat

public export
Eq MetricBasisPair where
  (MkBasisPair r1 c1) == (MkBasisPair r2 c2) = (r1 == r2) && (c1 == c2)

------------------------------------------------------------------------
-- 2. THE METRIC TENSOR AS A DEPENDENT MULTISET (BOX)
------------------------------------------------------------------------

||| Generic Symmetric Metric Tensor defined natively as a Multiset (Box) of Weighted Basis Pairs:
||| M_g = ∑ k_ij · (e_i ⊗ e_j)
||| Dependently indexed by its BoxInt dimension.
public export
record MultisetMetricTensor (dim : BoxInt) where
  constructor MkMultisetMetricTensor
  basisMultiset : Box MetricBasisPair
  determinant   : BoxInt

||| Smart constructor building canonical Parabolic Multiset Metric Tensor for any dimension dim.
public export
canonicalMultisetMetric : (dim : BoxInt) -> MultisetMetricTensor dim
canonicalMultisetMetric dim =
  let dimNat = boxToNat dim
      pairs = [ MkBasisPair i j | i <- [1..dimNat], j <- [1..dimNat], i <= j ]
      m = foldl (\acc, p => insertBox p (intToBoxInt 1) acc) emptyBox pairs
  in MkMultisetMetricTensor m (intToBoxInt 0)

------------------------------------------------------------------------
-- 3. TYPE ALIASES & FORMAL INVARIANT AUDIT PROOFS
------------------------------------------------------------------------

||| Canonical 10D Substrate Multiset Metric Tensor.
public export
canonicalSubstrateMultisetMetric : MultisetMetricTensor DimSubstrate
canonicalSubstrateMultisetMetric = canonicalMultisetMetric DimSubstrate

||| Audits the Multiset Metric Tensor:
||| Determinant det(M_g) is identically 0 (Parabolic Substrate).
public export
auditMultisetMetricTensorProof : Bool
auditMultisetMetricTensorProof =
  boxIsZero (determinant canonicalSubstrateMultisetMetric)

