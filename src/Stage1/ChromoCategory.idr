module Stage1.ChromoCategory

import public Stage0.BoxInt
import public Stage1.VexelMaxel
import public Stage1.LinAlgebra.MetricTensor

%default total

------------------------------------------------------------------------
-- 1. CHROMOGEOMETRIC METRIC COLOR SIGNATURE
------------------------------------------------------------------------

||| A Chromogeometric Metric Color Signature (The "Color" of the Space)
||| - Blue:  Euclidean Metric g = [[1, 0], [0, 1]]
||| - Red:   Minkowski Relativistic Metric g = [[1, 0], [0, -1]]
||| - Green: Split-Complex Metric g = [[0, 1], [1, 0]]
public export
data MetricColor = Blue | Red | Green

public export
Eq MetricColor where
  Blue  == Blue  = True
  Red   == Red   = True
  Green == Green = True
  _     == _     = False

public export
Show MetricColor where
  show Blue  = "Blue"
  show Red   = "Red"
  show Green = "Green"

||| Returns the canonical sparse Maxel metric tensor for a given MetricColor.
public export
colorMetricTensor : MetricColor -> Maxel
colorMetricTensor Blue  = gBlue
colorMetricTensor Red   = gRed
colorMetricTensor Green = gGreen

------------------------------------------------------------------------
-- 2. FINITE-DIMENSIONAL VECTOR SPACE OBJECT BOUND TO METRIC FORM
------------------------------------------------------------------------

||| A finite-dimensional vector space object bound strictly to its dimension and sparse metric tensor.
||| Uses QTT 0 multiplicity for the metric tensor witness to enable zero-runtime-overhead erasure.
public export
record VexelSpace (dim : Nat) (color : MetricColor) where
  constructor Space
  ||| Sparse metric tensor Maxel carrying the chromogeometric form as a type witness
  0 metricTensor : Maxel

||| Constructs a default VexelSpace for a dimension and color.
public export
defaultSpace : (dim : Nat) -> (color : MetricColor) -> VexelSpace dim color
defaultSpace dim color = Space (colorMetricTensor color)

------------------------------------------------------------------------
-- 3. CHROMOCATEGORY INTERFACE (FINITIST MATRIX MORPHISMS)
------------------------------------------------------------------------

||| A strictly finite, constructive category where objects are VexelSpaces
||| and morphisms are sparse Maxel transition matrices.
public export
interface ChromoCategory where
  ||| Objects are finite-dimensional vector space descriptors
  Object : Type

  ||| Extract dimension of an object
  dimOf : Object -> Nat

  ||| Extract metric color of an object
  colorOf : Object -> MetricColor

  ||| Extract metric tensor witness Maxel
  formOf : (obj : Object) -> Maxel

||| Morphisms are sparse Maxel transition matrices mapping between vector spaces
public export
ChromoHom : Maxel
ChromoHom = identityMaxel

||| Composition maps directly to sparse multiset matrix multiplication mulMaxel
public export
composeChromo : Maxel -> Maxel -> Maxel
composeChromo m2 m1 = mulMaxel m2 m1

||| Canonical identity morphism for an object
public export
idChromo : Maxel
idChromo = identityMaxel

------------------------------------------------------------------------
-- 4. EXACT QUADRANCE EVALUATION VIA METRICINNERVEXEL
------------------------------------------------------------------------

||| Computes exact rational quadrance (squared metric distance) of a Vexel
||| strictly according to the space's sparse metric tensor using metricInnerVexel.
||| Executes in O(K) sparse multiset matrix performance with zero floating-point drift.
public export
quadranceVexelSpace : {d : Nat} -> {c : MetricColor} ->
                      (0 space : VexelSpace d c) ->
                      (vector : Vexel) ->
                      BoxInt
quadranceVexelSpace {c} space vector =
  metricInnerVexel (colorMetricTensor c) vector vector
