module Stage1.LinAlgebra.MetricTensor

import public Stage0.BoxInt
import public Stage1.VexelMaxel

%default total

||| A 2x2 Metric is a symmetric Maxel (multiset of Pixels).
public export
buildMetricMaxel : (g11 : BoxInt) -> (g12 : BoxInt) -> (g22 : BoxInt) -> Maxel
buildMetricMaxel a b c =
  MkMaxel [ (MkPixel 1 1, a)
          , (MkPixel 1 2, b)
          , (MkPixel 2 1, b)
          , (MkPixel 2 2, c)
          ]

||| Extract g11 component from a Maxel.
public export
g11 : Maxel -> BoxInt
g11 m = lookupPixel (MkPixel 1 1) m

||| Extract g12 component from a Maxel.
public export
g12 : Maxel -> BoxInt
g12 m = lookupPixel (MkPixel 1 2) m

||| Extract g22 component from a Maxel.
public export
g22 : Maxel -> BoxInt
g22 m = lookupPixel (MkPixel 2 2) m

||| Metric Determinant: det(M) = g11 * g22 - g12^2
%inline public export
detMetric : Maxel -> BoxInt
detMetric m = detSymmetricMatrix2D (g11 m) (g12 m) (g22 m)

||| Metric Trace: tr(M) = g11 + g22
public export
traceMetric : Maxel -> BoxInt
traceMetric m = g11 m + g22 m

||| Primary Euclidean Blue Metric Maxel: g = [[1, 0], [0, 1]]
public export
gBlue : Maxel
gBlue = buildMetricMaxel (intToBoxInt 1) (intToBoxInt 0) (intToBoxInt 1)

||| Primary Relativistic Red Metric Maxel: g = [[1, 0], [0, -1]]
public export
gRed : Maxel
gRed = buildMetricMaxel (intToBoxInt 1) (intToBoxInt 0) (intToBoxInt (-1))

||| Primary Split-Complex Green Metric Maxel: g = [[0, 1], [1, 0]]
public export
gGreen : Maxel
gGreen = buildMetricMaxel (intToBoxInt 0) (intToBoxInt 1) (intToBoxInt 0)

||| Causal Poset Substrate Metric Maxel: g = [[1, 1], [1, 0]]
public export
gSubstrate : Maxel
gSubstrate = buildMetricMaxel (intToBoxInt 1) (intToBoxInt 1) (intToBoxInt 0)

||| Electromagnetism Spacetime Metric Maxel: g = [[1, 0], [0, -1]]
public export
gEM : Maxel
gEM = gRed

||| Symplectic Phase Space Metric Maxel: g = [[0, 1], [1, 0]]
public export
gToroidal : Maxel
gToroidal = gGreen

||| Rational Spread Trigonometric Metric Maxel: g = [[1, -1], [-1, 1]]
public export
gTrigonometry : Maxel
gTrigonometry = buildMetricMaxel (intToBoxInt 1) (intToBoxInt (-1)) (intToBoxInt 1)

||| Boolean Bit Projection Metric Maxel: g = [[1, 0], [0, 0]]
public export
gBoole : Maxel
gBoole = buildMetricMaxel (intToBoxInt 1) (intToBoxInt 0) (intToBoxInt 0)

||| Backward-compatible aliases mapping MetricTensor2D to Maxel.
public export
MetricTensor2D : Type
MetricTensor2D = Maxel

public export
MkMetricTensor2D : BoxInt -> BoxInt -> BoxInt -> Maxel
MkMetricTensor2D = buildMetricMaxel
