-- This module serves as the root of the `Math` library.
-- Import modules here that should be built as part of the library.
import Mathlib
import Smt

import Math.NeqScales
import Math.Tactics

@[inherit_doc] prefix:max "sqrt" => Real.sqrt
