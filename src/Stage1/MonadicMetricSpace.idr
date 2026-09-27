module Stage1.MonadicMetricSpace

import Data.Vect
import Stage0.BoxInt
import Stage1.UnixelFraction
import Stage1.Goh
import Stage1.Order.Preorder
import Stage0.Applicative
import Stage1.MetricalBounds

%default total

--------------------------------------------------------------------------------
-- UNIFIED MONADIC METRIC SPACE CONTRACT
--------------------------------------------------------------------------------

||| Unified Interface combining Applicative envelopes with preordered monoidal bounds
||| and poset directional steps.
public export
interface Applicative m => MonadicMetricSpace (0 m : Type -> Type) where
  ||| Metric signature constraint validator
  validateMetricBound : {0 a : Type} -> m a -> Bool

public export
implementation {dim : Nat} -> {color : MetricColor} -> MonadicMetricSpace (GeometricEnvelope dim color) where
  validateMetricBound _ = True

public export
implementation {dim : Nat} -> {color : MetricColor} -> MonadicMetricSpace (MetricalEnvelope dim color) where
  validateMetricBound _ = True
