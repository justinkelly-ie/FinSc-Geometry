# FinSc-Geometry

[![Idris 2 Verification](https://img.shields.io/badge/Idris_2-0.8.0-blue.svg)](https://www.idris-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

**Layer 3 Emergent Chromogeometry, Monadic Metric Spaces & Grassmann Calculus for Idris 2**

`FinSc-Geometry` forms **Layer 3** of the 10-layer constructive non-linear multiset science framework. It provides emergent metric spaces, applicative geometric envelopes across the 4 fundamental metrics (Elliptic, Hyperbolic, Parabolic, Substrate), unified monadic metric contracts (`MonadicMetricSpace`), discrete Grassmann calculus, dual flat information geometry, and Wildberger's Rational Trigonometry primitives.

---

## 📦 Core Library Architecture & Modules

### 1. `Geometry.Applicative`
- **Applicative Geometric Envelopes:** `GeometricEnvelope dim color` wrapping non-interacting geometric particle propagation.
- **4 Fundamental Metrics:** Discrete metric signature partitioning:
  - **Elliptic Geometry (Blue, signature $[1, 1, 1]$):** Bounded positive curvature space (27 degrees of freedom).
  - **Hyperbolic Geometry (Red, signature $[1, 1, -1]$):** Relativistic Minkowski spacetime (128 degrees of freedom).
  - **Parabolic Geometry (Green, signature $[1, 1, 0]$):** Classical Euclidean flat space (55 degrees of freedom).
  - **Substrate Geometry (Substrate, signature $[0, 0, 0]$):** Vacuum baseline state.

### 2. `Geometry.MetricalBounds` & `Geometry.MonadicMetricSpace`
- **Metrical Bounds:** Quadrance ($Q$, squared distance) and Spread ($S$, rational angular separation) bounds (`MetricalEnvelope dim color`).
- **Unified Monadic Metric Contract:** `MonadicMetricSpace` interface combining Applicative envelopes with preordered monoidal bounds and metric signature validation (`validateMetricBound`).

### 3. `Geometry.GrassmannCalculus` & `Geometry.LatticeTopology`
- **Discrete Exterior Algebra:** Wedge products ($\wedge$), interior product contraction, and Grassmannian cell complexes over discrete vector spaces.
- **Lattice Topology:** Discrete multiset cell boundaries enforcing contour containment ($\partial^2 = 0$).

### 4. `Geometry.InformationGeometry`
- **Dual Flat Information Manifolds:** Amari dual connections ($\nabla, \nabla^*$), Fisher-Rao metric tensors, and Pythagorean theorem over information quadrance.

### 5. `Math.RationalTrig` & `Math.Infinitesimal`
- **Rational Trigonometry Primitives:** Exact polynomial quadrance and spread calculations bypassing transcendental functions ($\sin, \cos, \pi$) and continuous square roots.
- **Constructive Infinitesimals:** Non-standard rational infinitesimal fields over characteristic zero.

---

## 🚀 Building & Installing

```bash
idris2 --build FinSc-Geometry.ipkg
idris2 --install FinSc-Geometry.ipkg
```

---

## 🔬 Architectural Principles

- **Total Constructivism:** Enforces `%default total` across all geometric calculation modules.
- **Coordinate-Free Chromogeometry:** Spatial signatures encoded directly into type parameters (`MetricColor`).
- **Zero Floating-Point Drift:** Pure rational arithmetic over Quadrance ($Q$) and Spread ($S$).
