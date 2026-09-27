module Stage1.FourGeometriesActions

import Stage0.OnSeq.FusedStream
import Stage0.LatticeTopology
import Data.Fuel
import Data.Fin
import public Stage0.BoxInt
import public Stage1.Order.Preorder
import public Stage1.VexelMaxel
import public Stage1.UnixelFraction
import public Stage1.ScaleTransform
import public Stage1.FourGeometries
import public Stage1.LinAlgebra.MetricTensor
import public Stage1.LinAlgebra.TernaryClassifier

%default total



------------------------------------------------------------------------
-- 2. CANONICAL MAXEL METRIC TENSORS
------------------------------------------------------------------------

||| Maps each fundamental geometry to its canonical Maxel metric tensor.
%inline
public export
geometryMetric : FundamentalGeometry -> Stage1.VexelMaxel.Maxel
geometryMetric EllipticGeom   = gBlue
geometryMetric HyperbolicGeom = gRed
geometryMetric ParabolicGeom  = gBoole
geometryMetric SubstrateGeom  = gSubstrate

||| Computes the exact metric determinant for a fundamental geometry.
%inline
public export
geometryDeterminant : FundamentalGeometry -> Stage0.BoxInt.BoxInt
geometryDeterminant geom = detMetric (geometryMetric geom)

||| Computes the exact metric trace for a fundamental geometry.
%inline
public export
geometryTrace : FundamentalGeometry -> Stage0.BoxInt.BoxInt
geometryTrace geom = traceMetric (geometryMetric geom)

||| Evaluates the algebraic Quadrance Q_g(v) of a 2D Vexel under a fundamental geometry:
||| Q_g(v) = v1^2 * g11 + 2 * v1 * v2 * g12 + v2^2 * g22.
%inline
public export
evaluateQuadrance : FundamentalGeometry -> (v1 : Stage0.BoxInt.BoxInt) -> (v2 : Stage0.BoxInt.BoxInt) -> Stage0.BoxInt.BoxInt
evaluateQuadrance geom v1 v2 =
  let g = geometryMetric geom
      g11Val = g11 g
      g12Val = g12 g
      g22Val = g22 g
      term1 = (v1 * v1) * g11Val
      term2 = (intToBoxInt 2 * (v1 * v2)) * g12Val
      term3 = (v2 * v2) * g22Val
  in term1 + term2 + term3

------------------------------------------------------------------------
-- 3. THE 4 GEOMETRIC ACTION THEOREMS
--    Each geometry governs a distinct, non-negotiable physical law
------------------------------------------------------------------------

||| 1. Elliptic Action: Confinement & Positive Quadrance.
||| For any non-zero spatial displacement (1, 0), Q_Elliptic = +1 (strictly positive).
%inline
public export
ellipticConfinementAction : (v1 : Stage0.BoxInt.BoxInt) -> (v2 : Stage0.BoxInt.BoxInt) -> Stage0.BoxInt.BoxInt
ellipticConfinementAction v1 v2 = evaluateQuadrance EllipticGeom v1 v2

||| 2. Hyperbolic Action: Non-Abelian Quantum Phase & Lightcones.
||| Admits lightlike null vectors with zero quadrance (e.g. (1, 1) -> 1 - 1 = 0).
%inline
public export
hyperbolicPhaseAction : (v1 : Stage0.BoxInt.BoxInt) -> (v2 : Stage0.BoxInt.BoxInt) -> Stage0.BoxInt.BoxInt
hyperbolicPhaseAction v1 v2 = evaluateQuadrance HyperbolicGeom v1 v2

||| 3. Parabolic Action: Degenerate Dissipation Channel.
||| Disregards orthogonal direction components (g22 = 0, g12 = 0) allowing remainder drainage.
%inline
public export
parabolicDissipationAction : (v1 : Stage0.BoxInt.BoxInt) -> (v2 : Stage0.BoxInt.BoxInt) -> Stage0.BoxInt.BoxInt
parabolicDissipationAction v1 v2 = evaluateQuadrance ParabolicGeom v1 v2

||| 4. Substrate Action: Irreversible Causal Arrow.
||| Satisfies g22 = 0 (no temporal feedback) and g12 = 1 (unidirectional matter bias).
%inline
public export
substrateCausalArrowAction : Stage1.VexelMaxel.Maxel -> Bool
substrateCausalArrowAction g =
  unwrapBox (g22 g) == 0 && unwrapBox (g12 g) == 1

public export
substrateCausalArrowActionBit : Stage1.VexelMaxel.Maxel -> Bit
substrateCausalArrowActionBit g =
  if unwrapBox (g22 g) == 0 && unwrapBox (g12 g) == 1 then One else Zero


------------------------------------------------------------------------
-- 4. COSMIC BUDGET DECOMPOSITION ACROSS THE 4 GEOMETRIES
------------------------------------------------------------------------

||| Decomposes the 4th Primorial budget across the Chromogeometric Triad and Substrate:
||| - Elliptic Blue Sector     = 27  (3^3 Spacetime Lattice Basis)
||| - Hyperbolic Red Sector    = 128 (2^7 Symplectic Law ROM)
||| - Parabolic Green Sector   = 55  (Accumulated Dark Matter Residue, T_10)
||| Total Budget = 27 + 128 + 55 = 210 = 2 * 3 * 5 * 7.
%inline
public export
cosmicBudgetByGeometry : FundamentalGeometry -> Nat
cosmicBudgetByGeometry EllipticGeom   = ellipticLatticeCapacity
cosmicBudgetByGeometry HyperbolicGeom = hyperbolicRomCapacity
cosmicBudgetByGeometry ParabolicGeom  = darkMatterTriangularResidue
cosmicBudgetByGeometry SubstrateGeom  = primorial210Budget

||| Evaluates the exact rational chance proportion of each geometry.
%inline
public export
cosmicChanceByGeometry : FundamentalGeometry -> UnixelFraction
cosmicChanceByGeometry geom =
  let tally = cosmicBudgetByGeometry geom
  in if geom == SubstrateGeom
       then unitUnixelFraction
       else hehnerTallyToChance tally primorial210Budget

||| Foundational Pythagorean bond coordinate (4, 3) in H2O geometry.
public export
pythagoreanBondCoordinate : (BoxInt, BoxInt)
pythagoreanBondCoordinate = (intToBoxInt 4, intToBoxInt 3)

||| Computes the tri-metric chromogeometric gate fingerprint (25, 7, 24) algebraically from (4, 3).
public export
chromogeometricGateFingerprint : (BoxInt, BoxInt, BoxInt)
chromogeometricGateFingerprint =
  let (x, y) = pythagoreanBondCoordinate
      qE = (x * x) + (y * y)
      qH = (x * x) - (y * y)
      qP = intToBoxInt 2 * (x * y)
  in (qE, qH, qP)

------------------------------------------------------------------------
-- 5. CONSTRUCTIVE FORMAL AUDIT PROOFS
------------------------------------------------------------------------

||| Audits the Determinant Classification of the 4 Geometries:
||| det(Elliptic)   = +1
||| det(Hyperbolic) = -1
||| det(Parabolic)  = 0
||| det(Substrate)  = -1 (with asymmetric g22 = 0)
%inline
public export
auditFourGeometriesDeterminantsProof : Bool
auditFourGeometriesDeterminantsProof =
  let detEll = geometryDeterminant EllipticGeom
      detHyp = geometryDeterminant HyperbolicGeom
      detPar = geometryDeterminant ParabolicGeom
      detSub = geometryDeterminant SubstrateGeom
  in unwrapBox detEll == 1 &&
     unwrapBox detHyp == (-1) &&
     unwrapBox detPar == 0 &&
     unwrapBox detSub == (-1)

||| Audits the Cosmic Synthesis of the 4 Geometries:
||| 1. Quadrance of (1, 1) under Hyperbolic is exactly 0 (Lightcone).
||| 2. Quadrance of (1, 0) under Elliptic is exactly 1 (Confinement).
||| 3. Budget partition 27 + 128 + 55 == 210 (Primorial 210).
public export
auditFourGeometriesCosmicSynthesisProof : Bool
auditFourGeometriesCosmicSynthesisProof =
  let one = intToBoxInt 1
      zero = intToBoxInt 0
      qHyp = hyperbolicPhaseAction one one
      qEll = ellipticConfinementAction one zero
      bTotal = cosmicBudgetByGeometry EllipticGeom +
               cosmicBudgetByGeometry HyperbolicGeom +
               cosmicBudgetByGeometry ParabolicGeom
      okHyp = case unwrapBox qHyp of
                0 => True
                _ => False
      okEll = case unwrapBox qEll of
                1 => True
                _ => False
      okTot = natEq bTotal 210
  in okHyp && okEll && okTot

------------------------------------------------------------------------
-- 6. WILDBERGER PLANAR CHROMOGEOMETRY THEOREMS (THEOREMS 6 & 8)
------------------------------------------------------------------------

||| Wildberger Theorem 6: Three-Fold Quadrance Metric Symmetry (Q_b^2 == Q_r^2 + Q_g^2).
||| For displacement (dx, dy): Q_b = dx^2 + dy^2, Q_r = dx^2 - dy^2, Q_g = 2*dx*dy.
public export
evaluateThreeFoldQuadranceSymmetry : (dx : BoxInt) -> (dy : BoxInt) -> Bool
evaluateThreeFoldQuadranceSymmetry dx dy =
  let qb = (dx * dx) + (dy * dy)
      qr = (dx * dx) - (dy * dy)
      qg = intToBoxInt 2 * (dx * dy)
  in (qb * qb) == (qr * qr) + (qg * qg)

||| Type-level proof witness certifying Wildberger 3-Metric Quadrance Identity: Q_b^2 = Q_r^2 + Q_g^2.
public export
0 ThreeFoldQuadranceIdentity : (qb : BoxInt) -> (qr : BoxInt) -> (qg : BoxInt) -> Type
ThreeFoldQuadranceIdentity qb qr qg = (qb * qb) = (qr * qr) + (qg * qg)

||| Type-level proof witness certifying Wildberger 3-Metric Quadrea Identity: A_b = -A_r = -A_g.
public export
0 ThreeFoldQuadreaIdentity : (ab : BoxInt) -> (ar : BoxInt) -> (ag : BoxInt) -> Type
ThreeFoldQuadreaIdentity ab ar ag = (ab = negate ar, ab = negate ag)

||| Monomorphic erased proof witness for Wildberger 3-metric quadrance conservation (b + r = g).
public export
0 MonomorphicQuadranceConservation : Nat -> Nat -> Nat -> Type
MonomorphicQuadranceConservation b r g = natAdd b r = g

||| Constructive erased witness verifying that the chromogeometric triad (27 + 128 + 55) sums to 210.
public export
0 prfThreeFoldBudgetConservation : MonomorphicQuadranceConservation (Stage1.FourGeometries.ellipticLatticeCapacity + Stage1.FourGeometries.hyperbolicRomCapacity) Stage1.FourGeometries.darkMatterTriangularResidue Stage1.FourGeometries.primorial210Budget
prfThreeFoldBudgetConservation = Refl

||| Evaluates chromogeometric transformations equipped with an erased compile-time metricPrf witness.
public export
transformChromogeometricQuadrance : {b, r, g : Nat} ->
                                    (0 metricPrf : MonomorphicQuadranceConservation b r g) ->
                                    (blueVal : Nat) -> (redVal : Nat) -> Nat
transformChromogeometricQuadrance {b, r, g} prf blueVal redVal = natAdd blueVal redVal

||| Computes the (Blue, Red, Green) Quadreas of a triangle A1(x1, y1), A2(x2, y2), A3(x3, y3).
public export
evaluateThreeFoldQuadrea : (x1 : BoxInt) -> (y1 : BoxInt) ->
                           (x2 : BoxInt) -> (y2 : BoxInt) ->
                           (x3 : BoxInt) -> (y3 : BoxInt) -> (BoxInt, BoxInt, BoxInt)
evaluateThreeFoldQuadrea x1 y1 x2 y2 x3 y3 =
  let dx12 = x2 - x1
      dy12 = y2 - y1
      dx23 = x3 - x2
      dy23 = y3 - y2
      dx31 = x1 - x3
      dy31 = y1 - y3
      -- Blue Quadrances
      qb1 = (dx12 * dx12) + (dy12 * dy12)
      qb2 = (dx23 * dx23) + (dy23 * dy23)
      qb3 = (dx31 * dx31) + (dy31 * dy31)
      ab  = (qb1 + qb2 + qb3) * (qb1 + qb2 + qb3) - intToBoxInt 2 * ((qb1 * qb1) + (qb2 * qb2) + (qb3 * qb3))
      -- Red Quadrances
      qr1 = (dx12 * dx12) - (dy12 * dy12)
      qr2 = (dx23 * dx23) - (dy23 * dy23)
      qr3 = (dx31 * dx31) - (dy31 * dy31)
      ar  = (qr1 + qr2 + qr3) * (qr1 + qr2 + qr3) - intToBoxInt 2 * ((qr1 * qr1) + (qr2 * qr2) + (qr3 * qr3))
      -- Green Quadrances
      qg1 = intToBoxInt 2 * (dx12 * dy12)
      qg2 = intToBoxInt 2 * (dx23 * dy23)
      qg3 = intToBoxInt 2 * (dx31 * dy31)
      ag  = (qg1 + qg2 + qg3) * (qg1 + qg2 + qg3) - intToBoxInt 2 * ((qg1 * qg1) + (qg2 * qg2) + (qg3 * qg3))
  in (ab, ar, ag)

||| Wildberger Theorem 8: The Three-Fold Quadrea Theorem (A_b == -A_r == -A_g).
public export
verifyThreeFoldQuadreaTheorem : (x1 : BoxInt) -> (y1 : BoxInt) ->
                                (x2 : BoxInt) -> (y2 : BoxInt) ->
                                (x3 : BoxInt) -> (y3 : BoxInt) -> Bool
verifyThreeFoldQuadreaTheorem x1 y1 x2 y2 x3 y3 =
  let (ab, ar, ag) = evaluateThreeFoldQuadrea x1 y1 x2 y2 x3 y3
  in ab == (intToBoxInt (-1) * ar) && ab == (intToBoxInt (-1) * ag)

||| Audits Wildberger Chromogeometry Theorems 6 & 8 on concrete triangle coordinates.
public export
auditThreeFoldChromogeometryProof : Bool
auditThreeFoldChromogeometryProof =
  let t6Ok = evaluateThreeFoldQuadranceSymmetry (intToBoxInt 3) (intToBoxInt 4)
      t8Ok = verifyThreeFoldQuadreaTheorem (intToBoxInt 0) (intToBoxInt 0)
                                           (intToBoxInt 4) (intToBoxInt 0)
                                           (intToBoxInt 0) (intToBoxInt 3)
  in t6Ok && t8Ok

------------------------------------------------------------------------
-- 7. DEFORESTED 3-METRIC CHROMOGEOMETRIC TRIAD TRANSDUCERS (PHASE 9)
------------------------------------------------------------------------

||| Single-pass stream transducer evaluating Blue Elliptic (Q_E), Red Hyperbolic (Q_H),
||| and Green Parabolic (Q_P) quadrances concurrently for (x, y) grid coordinates.
public export
chromogeometricTriadTransducer : StreamTransducer (BoxInt, BoxInt) (BoxInt, BoxInt, BoxInt)
chromogeometricTriadTransducer = MkTransducer step ()
  where
    step : () -> (BoxInt, BoxInt) -> Step () (BoxInt, BoxInt, BoxInt)
    step () (x, y) =
      let qE = (x * x) + (y * y)
          qH = (x * x) - (y * y)
          qP = intToBoxInt 2 * (x * y)
      in Yield (qE, qH, qP) ()

||| Applies single-pass chromogeometric triad transducer over a deforested stream of (x, y) coordinates.
%inline public export
streamChromogeometricTriad : FusedStream (BoxInt, BoxInt) -> FusedStream (BoxInt, BoxInt, BoxInt)
streamChromogeometricTriad strm = transduceStream chromogeometricTriadTransducer strm

||| Zero-heap deforested accumulator verifying Wildberger 3-metric quadrance identity Q_E^2 == Q_H^2 + Q_P^2
||| across a stream of grid coordinates.
public export covering
fusedChromogeometricTriadIdentityCheck : Fuel -> FusedStream (BoxInt, BoxInt) -> Bool
fusedChromogeometricTriadIdentityCheck fuel strm =
  let (MkStream next seed) = streamChromogeometricTriad strm
  in fusedHylomorphism fuel
       next
       (\(qE, qH, qP), acc => ((qE * qE) == ((qH * qH) + (qP * qP))) && acc)
       True
       seed


