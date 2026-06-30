/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Geometric.Basic
public import Physlib.SpaceAndTime.Time.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
/-!
# Geometric trajectories of the harmonic oscillator

## i. Overview

A trajectory of the harmonic oscillator is a time-parametrized curve in the configuration
manifold `Q`. Since this model of `Q` has a single global coordinate valued in
`EuclideanSpace ℝ (Fin 1)`, every geometric trajectory has an associated coordinate curve.

The coordinate diffeomorphism from `Q` to its model space lets smoothness of a geometric
trajectory be tested as ordinary smoothness of its coordinate curve.

## ii. Key results

- `Trajectory` : a curve from `Time` into the configuration manifold.
- `Trajectory.coord` : the global Euclidean coordinate curve of a trajectory.
- `Trajectory.toSpace` : the physical-space position along a trajectory.
- `Trajectory.contMDiff_iff_contDiff_coord` : geometric smoothness of a trajectory is
  equivalent to ordinary smoothness of its coordinate curve.

## iii. Table of contents

- A. The trajectory type and coordinate projection
- B. Smoothness of trajectories

## iv. References

- Ivo Terek, Introductory Variational Calculus on Manifolds, pages 1-2 (Section 1, Basic
  definitions and examples).
-/

@[expose] public section

namespace ClassicalMechanics

namespace HarmonicOscillator

open scoped Manifold

/-!
## A. The trajectory type and coordinate projection

A trajectory is a curve in the configuration manifold `Q`, parametrized by `Time`. The
coordinate projection reads the same curve in the chosen global coordinate, while `toSpace`
forgets the manifold structure and returns the corresponding physical-space position.
-/

/-- A trajectory of the oscillator: a curve in the configuration manifold `Q`. -/
abbrev Trajectory := Time → ConfigurationSpace

namespace Trajectory

/-- The coordinate curve of a trajectory: its reading in the global Euclidean coordinate. -/
def coord (γ : Trajectory) : Time → EuclideanSpace ℝ (Fin 1) := fun t => (γ t).val

/-- The physical position of the oscillator along a trajectory, over time. -/
def toSpace (γ : Trajectory) : Time → Space 1 := fun t => (γ t).toSpace

lemma coord_apply (γ : Trajectory) (t : Time) : coord γ t = (γ t).val := rfl

/-!
## B. Smoothness of trajectories

Because the global coordinate is a diffeomorphism, composing a trajectory with it preserves
and reflects manifold smoothness. Since both `Time` and the coordinate model are normed
spaces, this manifold-smoothness statement then becomes ordinary `ContDiff` smoothness.
-/

/-- A trajectory is smooth as a curve in `Q` iff its coordinate curve is ordinarily smooth. -/
lemma contMDiff_iff_contDiff_coord {n : WithTop ℕ∞} (γ : Trajectory) :
    ContMDiff 𝓘(ℝ, Time) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) n γ ↔
      ContDiff ℝ n (coord γ) := by
  rw [show coord γ = ConfigurationSpace.valDiffeomorph ∘ γ from rfl]
  rw [← contMDiff_iff_contDiff]
  exact (ConfigurationSpace.valDiffeomorph.contMDiff_diffeomorph_comp_iff
    (m := n) (f := γ) le_top).symm

end Trajectory

end HarmonicOscillator

end ClassicalMechanics
