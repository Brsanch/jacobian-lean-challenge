-- Library entry point. New module files must be added to this import list.
import JacobianChallenge.Basic
import JacobianChallenge.Manifold.Cotangent
import JacobianChallenge.Manifold.HolomorphicOneForm
-- import JacobianChallenge.Manifold.MeromorphicAt
-- ^ Temporarily unwired pending fix-up of pinned-mathlib API mismatches.
-- File still in tree; first compile attempt produced ~50 type-mismatch
-- errors (mostly `MeromorphicAt.comp_analyticAt` and friends having
-- different argument shapes at this pin than the agent assumed).
