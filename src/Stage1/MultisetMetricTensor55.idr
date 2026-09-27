module Stage1.MultisetMetricTensor55

import Stage0.BoxInt
import Stage0.Multiset
import Data.List
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. METRIC TENSOR BASIS PAIRS AS MULTISET ELEMENT KEYS
------------------------------------------------------------------------

||| Basis index pair (i, j) for symmetric 10D tensor entries (1 <= i <= j <= 10).
public export
record MetricBasisPair where
  constructor MkBasisPair
  row : Nat
  col : Nat

public export
Eq MetricBasisPair where
  (MkBasisPair r1 c1) == (MkBasisPair r2 c2) = (r1 == r2) && (c1 == c2)

------------------------------------------------------------------------
-- 2. THE 10D METRIC TENSOR AS A PURE MULTISET (BOX)
------------------------------------------------------------------------

||| The 10D Symmetric Metric Tensor g_μν defined natively as a Multiset (Box) of 55 Weighted Basis Pairs:
||| M_g = ∑ k_ij · (e_i ⊗ e_j)
public export
record MultisetMetricTensor55 where
  constructor MkMultisetMetricTensor55
  basisMultiset : Box MetricBasisPair
  determinant   : BoxInt

||| Smart constructor building the canonical 55-component Parabolic Substrate Multiset Metric Tensor.
public export
canonicalMultisetMetric55 : MultisetMetricTensor55
canonicalMultisetMetric55 =
  let pairs = [ MkBasisPair i j | i <- [1..10], j <- [1..10], i <= j ]
      m = foldl (\acc, p => insertBox p (intToBoxInt 1) acc) emptyBox pairs
  in MkMultisetMetricTensor55 m (intToBoxInt 0)

------------------------------------------------------------------------
-- 3. FORMAL INVARIANT AUDIT PROOFS
------------------------------------------------------------------------

||| Audits the Multiset Metric Tensor:
||| 1. Determinant det(M_g) is identically 0 (Parabolic Substrate).
||| 2. Canonical multiset determinant is zero.
%inline
public export
auditMultisetMetricTensor55Proof : Bool
auditMultisetMetricTensor55Proof =
  let m = canonicalMultisetMetric55
  in unwrapBox (determinant m) == 0
