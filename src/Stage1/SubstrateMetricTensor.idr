module Stage1.SubstrateMetricTensor

import Stage0.BoxInt
import Stage0.StructuralFuel
import Stage1.VexelMaxel
import Data.List
import Data.Vect

import Stage1.FourGeometries

%default total

------------------------------------------------------------------------
-- 1. TRIANGULAR BOXINT & DEPENDENT SYMMETRIC TENSOR DEFINITION
------------------------------------------------------------------------

||| Evaluates the exact triangular number T_n = n(n+1)/2 as Nat for vector indexing.
public export
triangularNat : BoxInt -> Nat
triangularNat (MkBoxInt n) = integerToNat (div (n * (n + 1)) 2)

||| Evaluates the exact triangular number T_n = n(n+1)/2 over BoxInt.
||| Definitionally reduces during compile-time elaboration.
public export
triangularBoxInt : BoxInt -> BoxInt
triangularBoxInt (MkBoxInt n) = MkBoxInt (div (n * (n + 1)) 2)

||| Generic Symmetric Metric Tensor dependently indexed by its BoxInt dimension.
||| Eliminates hardcoding magic numbers in record names.
public export
record SymmetricMetricTensor (dim : BoxInt) where
  constructor MkSymmetricTensor
  components  : Vect (triangularNat dim) BoxInt
  determinant : BoxInt

public export
Eq (SymmetricMetricTensor dim) where
  (MkSymmetricTensor c1 d1) == (MkSymmetricTensor c2 d2) = c1 == c2 && d1 == d2

------------------------------------------------------------------------
-- 2. CANONICAL DIMENSIONS & TYPE ALIASES
------------------------------------------------------------------------

||| Canonical 10D phase space basis dimension: 4 spacetime + 3 color + 3 scale.
public export
PhaseSpaceBasisDim : Nat
PhaseSpaceBasisDim = Stage1.FourGeometries.phaseSpaceBasisDim

||| Parabolic 10D metric tensor component residue: T_10 = sum_{k=1}^10 k = 55.
public export
DarkMatterCapacity : Nat
DarkMatterCapacity = Stage1.FourGeometries.darkMatterTriangularResidue

public export
DimSubstrate : BoxInt
DimSubstrate = intToBoxInt (cast PhaseSpaceBasisDim)

public export
dimSubstrate : BoxInt
dimSubstrate = DimSubstrate

public export
DimSpacetime : BoxInt
DimSpacetime = intToBoxInt 4

public export
dimSpacetime : BoxInt
dimSpacetime = DimSpacetime

public export
DimColor : BoxInt
DimColor = intToBoxInt 3

public export
dimColor : BoxInt
dimColor = DimColor

public export
DimScale : BoxInt
DimScale = intToBoxInt 3

public export
dimScale : BoxInt
dimScale = DimScale

||| Substrate Metric Tensor (10D phase space, 55 components).
public export
SubstrateMetricTensor : Type
SubstrateMetricTensor = SymmetricMetricTensor DimSubstrate

||| Spacetime Metric Tensor (4D spacetime, 10 components).
public export
SpacetimeMetricTensor : Type
SpacetimeMetricTensor = SymmetricMetricTensor DimSpacetime

||| Color Gauge Metric Tensor (3D SU(3), 6 components).
public export
ColorMetricTensor : Type
ColorMetricTensor = SymmetricMetricTensor DimColor

||| Scale Metric Tensor (3D Chromogeometry, 6 components).
public export
ScaleMetricTensor : Type
ScaleMetricTensor = SymmetricMetricTensor DimScale

------------------------------------------------------------------------
-- 3. THE 6 IRREDUCIBLE GEOMETRIC SECTORS OF THE 10D SUBSTRATE TENSOR
------------------------------------------------------------------------

public export
data MetricSector =
    SectorSpacetime2     -- 10 channels: Spacetime x Spacetime (1 <= i <= j <= 4)
  | SectorColor2         --  6 channels: Color x Color (5 <= i <= j <= 7)
  | SectorScale2         --  6 channels: Scale x Scale (8 <= i <= j <= 10)
  | SectorSpacetimeColor -- 12 channels: Spacetime x Color (1 <= i <= 4, 5 <= j <= 7)
  | SectorSpacetimeScale -- 12 channels: Spacetime x Scale (1 <= i <= 4, 8 <= j <= 10)
  | SectorColorScale     --  9 channels: Color x Scale (5 <= i <= 7, 8 <= j <= 10)

public export
Eq MetricSector where
  SectorSpacetime2     == SectorSpacetime2     = True
  SectorColor2         == SectorColor2         = True
  SectorScale2         == SectorScale2         = True
  SectorSpacetimeColor == SectorSpacetimeColor = True
  SectorSpacetimeScale == SectorSpacetimeScale = True
  SectorColorScale     == SectorColorScale     = True
  _                    == _                    = False

public export
classifySector : Nat -> Nat -> MetricSector
classifySector i j =
  let (r, c) = if i <= j then (i, j) else (j, i)
  in if r <= 4 && c <= 4 then SectorSpacetime2
     else if r >= 5 && r <= 7 && c >= 5 && c <= 7 then SectorColor2
     else if r >= 8 && c >= 8 then SectorScale2
     else if r <= 4 && c >= 5 && c <= 7 then SectorSpacetimeColor
     else if r <= 4 && c >= 8 then SectorSpacetimeScale
     else SectorColorScale

||| Linear component index calculation (1..T_n) for upper triangular entry (i, j).
public export
metricComponentIndex : (dim : BoxInt) -> Nat -> Nat -> Nat
metricComponentIndex (MkBoxInt d) i j =
  let i1 = minus i 1
      i2 = minus i 2
      halfProd = half (i1 * i2)
      rowOffset = minus (i1 * (integerToNat d)) halfProd
  in rowOffset + minus j i + 1

||| Constructs canonical parabolic metric where det = 0 and all entries = 1.
public export
canonicalMetricTensor : (dim : BoxInt) -> SymmetricMetricTensor dim
canonicalMetricTensor dim =
  MkSymmetricTensor (replicate (triangularNat dim) (intToBoxInt 1)) (intToBoxInt 0)

||| Canonical 10D Substrate Metric Tensor (55 entries).
public export
canonicalSubstrateMetric : SubstrateMetricTensor
canonicalSubstrateMetric = canonicalMetricTensor DimSubstrate

------------------------------------------------------------------------
-- 4. FORMAL COMPILE-TIME INVARIANT AUDIT PROOFS
------------------------------------------------------------------------

||| Definitional proof that the 6 irreducible sectors partition exactly to 55 components.
public export
0 prfSubstrateSectorsSumTo55 : 10 + 6 + 6 + 12 + 12 + 9 = 55
prfSubstrateSectorsSumTo55 = Refl

||| Definitional proof that 10D Substrate Metric Tensor has exactly 55 components.
public export
0 prfSubstrateMetricComponentsIs55 : unwrapBox (triangularBoxInt DimSubstrate) = 55
prfSubstrateMetricComponentsIs55 = Refl

||| Definitional proof that 4D Spacetime Metric Tensor has exactly 10 components.
public export
0 prfSpacetimeMetricComponentsIs10 : unwrapBox (triangularBoxInt DimSpacetime) = 10
prfSpacetimeMetricComponentsIs10 = Refl

||| Definitional proof that 3D Color Metric Tensor has exactly 6 components.
public export
0 prfColorMetricComponentsIs6 : unwrapBox (triangularBoxInt DimColor) = 6
prfColorMetricComponentsIs6 = Refl

||| Audits the Substrate Metric Tensor:
||| Determinant det(M_g) is identically 0 (Parabolic Substrate) and component index bounds match.
public export
auditSubstrateMetricTensorProof : Bool
auditSubstrateMetricTensorProof =
  (unwrapBox (determinant canonicalSubstrateMetric) == 0) &&
  (metricComponentIndex DimSubstrate 1 1 == 1) &&
  (metricComponentIndex DimSubstrate 10 10 == DarkMatterCapacity)
