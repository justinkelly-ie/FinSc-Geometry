module Stage1.LinAlgebra.BilinearProduct

import Stage0.BoxInt
import Stage1.VexelMaxel
import Stage1.LinAlgebra.MetricTensor
import Stage1.Math.Infinitesimal

%default total

||| An infinitesimal 2D displacement vector (dx, dy) where each component
||| is a Dual Number Maxel tracking position and velocity.
public export
record InfinitesimalStep2D where
  constructor MkStep2D
  dx : Maxel
  dy : Maxel

public export
Eq InfinitesimalStep2D where
  (MkStep2D x1 y1) == (MkStep2D x2 y2) = x1 == x2 && y1 == y2

public export
Show InfinitesimalStep2D where
  show (MkStep2D x y) = "Step2D(dx=" ++ show x ++ ", dy=" ++ show y ++ ")"

||| Computes the infinitesimal bilinear inner product (ds^2) under a metric Maxel.
||| ds^2 = g11 * dx^2 + 2 * g12 * dx * dy + g22 * dy^2
public export
bilinearInnerProduct : Maxel -> InfinitesimalStep2D -> Maxel
bilinearInnerProduct g (MkStep2D dx dy) =
  let g11Val = g11 g
      g12Val = g12 g
      g22Val = g22 g
      dx2  = mulDual dx dx
      dy2  = mulDual dy dy
      dxdy = mulDual dx dy
      term1 = scaleDual g11Val dx2
      term2 = scaleDual (intToBoxInt 2 * g12Val) dxdy
      term3 = scaleDual g22Val dy2
  in addDual (addDual term1 term2) term3
