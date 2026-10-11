module Stage1.SubstrateMetricTensor55

import public Stage1.SubstrateMetricTensor
import Stage0.BoxInt
import Stage0.StructuralFuel
import Stage1.VexelMaxel
import Data.List
import Data.Vect

import Stage1.FourGeometries

%default total

------------------------------------------------------------------------
-- BACKWARD COMPATIBILITY ALIASES
------------------------------------------------------------------------

||| Legacy 10D phase space coordinate basis.
public export
data PhaseBasis10 = X1 | X2 | X3 | X4 | CR | CG | CB | S1 | S2 | S3

public export
Eq PhaseBasis10 where
  X1 == X1 = True; X2 == X2 = True; X3 == X3 = True; X4 == X4 = True
  CR == CR = True; CG == CG = True; CB == CB = True
  S1 == S1 = True; S2 == S2 = True; S3 == S3 = True
  _  == _  = False

||| Evaluates linear component index (1..55) for upper triangular entry (i, j).
%inline
public export
metricComponentIndex55 : Nat -> Nat -> Nat
metricComponentIndex55 i j = metricComponentIndex DimSubstrate i j

||| Legacy type alias for SubstrateMetricTensor (SymmetricMetricTensor dimSubstrate).
public export
SubstrateMetricTensor55 : Type
SubstrateMetricTensor55 = SubstrateMetricTensor

||| Legacy canonical smart constructor alias.
public export
canonicalSubstrateMetric55 : SubstrateMetricTensor55
canonicalSubstrateMetric55 = canonicalSubstrateMetric

||| Legacy audit proof function.
%inline
public export
auditSubstrateMetricTensor55Proof : Bool
auditSubstrateMetricTensor55Proof =
  (unwrapBox (determinant canonicalSubstrateMetric55) == 0) &&
  (metricComponentIndex55 1 1 == 1) &&
  (metricComponentIndex55 10 10 == Stage1.FourGeometries.darkMatterTriangularResidue)

||| Legacy compile-time proof witness.
public export
0 prfSubstrateMetric55DimensionMatchesPhaseSpaceBasis : Stage1.FourGeometries.darkMatterTriangularResidue = 55
prfSubstrateMetric55DimensionMatchesPhaseSpaceBasis = Refl
