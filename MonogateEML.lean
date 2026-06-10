import MonogateEML.AddLowerBound
import MonogateEML.ChainOrderAdditivity
import MonogateEML.DivLowerBound
import MonogateEML.DivLowerBound3
import MonogateEML.EMLDepth
import MonogateEML.EMLDuality
import MonogateEML.Float64
import MonogateEML.Gamma
import MonogateEML.HyperbolicPreservation
import MonogateEML.InfiniteZerosBarrier
import MonogateEML.ModelAudit
import MonogateEML.MulLowerBound
import MonogateEML.Runtime
import MonogateEML.SelfMapConjugacy
import MonogateEML.SinNotInEMLDepthBounds
import MonogateEML.SubLowerBound
import MonogateEML.Tactics
import MonogateEML.Universality
import MonogateEML.UpperBounds

/-!
# MonogateEML — top-level aggregator

This file imports every submodule under `MonogateEML/` so that
`lake build` (with no target) verifies the entire formalization
in a single pass. Without this file, `lake build` is a no-op
because the lakefile's `roots := #[MonogateEML]` resolves to a
non-existent module.

When adding a new file under `MonogateEML/`, append the
corresponding `import` line above in alphabetical order.
-/
