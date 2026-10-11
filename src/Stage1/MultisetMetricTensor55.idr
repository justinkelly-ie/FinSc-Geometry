module Stage1.MultisetMetricTensor55

import public Stage1.MultisetMetricTensor
import Stage1.SubstrateMetricTensor
import Stage0.BoxInt
import Stage0.Multiset
import Data.List
import Data.Vect

import Stage1.FourGeometries

%default total

------------------------------------------------------------------------
-- BACKWARD COMPATIBILITY ALIASES
------------------------------------------------------------------------

||| Legacy type alias for MultisetMetricTensor (dim = 10).
public export
MultisetMetricTensor55 : Type
MultisetMetricTensor55 = MultisetMetricTensor DimSubstrate

||| Legacy smart constructor alias.
public export
canonicalMultisetMetric55 : MultisetMetricTensor55
canonicalMultisetMetric55 = canonicalSubstrateMultisetMetric

||| Legacy audit proof function.
%inline
public export
auditMultisetMetricTensor55Proof : Bool
auditMultisetMetricTensor55Proof =
  unwrapBox (determinant canonicalMultisetMetric55) == 0

||| Legacy compile-time proof witness.
public export
0 prfMultisetMetric55DimensionMatchesPhaseSpaceBasis : Stage1.FourGeometries.darkMatterTriangularResidue = 55
prfMultisetMetric55DimensionMatchesPhaseSpaceBasis = Refl
