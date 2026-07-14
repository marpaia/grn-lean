import GRN.Certificate

/-!
# Worked examples and kernel-checked certificates

Two layers. The **edge-level** examples are integer-signed graphs; their
certificates are checked with `by decide`, i.e. by kernel-produced proof terms
with no dependency beyond Lean core. The **GRN-level** examples build the same
circuits from Hill kinetics and recover the identical signed graph through
`signedInteractionGraph`; those are exercised with `#eval` (compiled), since the
sign extraction from `Float` bounds does not reduce in the kernel.
-/

namespace GRN.Examples

open GRN

/-! ## Edge-level certificates (kernel-checked) -/

/-- A two-stage inducible relay: an inducer activates TF1, which represses GFP.
A feedforward tree: monotone, no loops. -/
def sensorEdges : List SignedEdge := [("aTc", "TF1", 1), ("TF1", "GFP", -1)]

/-- Incoherent reconvergence: one species both activates and represses another.
Not sign-consistent, so not monotone. -/
def incoherentEdges : List SignedEdge := [("A", "C", 1), ("A", "C", -1)]

/-- A toggle switch: mutual repression. The double-negative loop is positive
(bistability capacity) and the graph is still sign-consistent (monotone). -/
def toggleEdges : List SignedEdge := [("TF2", "TF1", -1), ("TF1", "TF2", -1)]

/-- A repressilator: three repressions in a cycle. The loop is negative
(oscillation capacity); the odd repression cycle is not sign-consistent. -/
def repressilatorEdges : List SignedEdge :=
  [("TF1", "TF2", -1), ("TF2", "TF3", -1), ("TF3", "TF1", -1)]

-- Sensor: monotone, no loops.
example : isMonotoneEdges sensorEdges = true := by decide
example : hasPositiveLoopEdges sensorEdges = false := by decide
example : hasNegativeLoopEdges sensorEdges = false := by decide
example : certifiesEdges sensorEdges .sensor = true := by decide

-- Incoherent reconvergence: not monotone.
example : isMonotoneEdges incoherentEdges = false := by decide

-- Toggle: positive loop and monotone; not a negative loop.
example : hasPositiveLoopEdges toggleEdges = true := by decide
example : hasNegativeLoopEdges toggleEdges = false := by decide
example : isMonotoneEdges toggleEdges = true := by decide
example : certifiesEdges toggleEdges .switch = true := by decide

-- Repressilator: negative loop, not monotone.
example : hasNegativeLoopEdges repressilatorEdges = true := by decide
example : isMonotoneEdges repressilatorEdges = false := by decide
example : certifiesEdges repressilatorEdges .oscillator = true := by decide

/-! ## GRN-level circuits (compiled evaluation) -/

/-- A genetic species (no kinetics). -/
def species (id : String) (k : NodeKind) : Node := { id := id, kind := k }

/-- A receiver activated by an inducer (`alpha = [0, 100]`). -/
def receiver (id : String) : Node :=
  { id := id, kind := .receiver, params := [("alpha", .list [.num 0, .num 100])] }

/-- A repressing Hill promoter (`alpha = [1, 0]`, high basal driven down). -/
def hillRep (id : String) : Node :=
  { id := id, kind := .hill1, params := [("alpha", .list [.num 1, .num 0])] }

/-- The two-stage sensor as a Hill-kinetic circuit; its signed graph is exactly
`sensorEdges`. -/
def sensor : GRN :=
  { nodes := [ species "aTc" .supplement, receiver "Rc", species "TF1" .regulator,
               hillRep "P1", species "GFP" .reporter ],
    edges := [ ⟨"aTc", "Rc", 0⟩, ⟨"Rc", "TF1", 0⟩, ⟨"TF1", "P1", 0⟩, ⟨"P1", "GFP", 0⟩ ] }

/-- The toggle switch as two cross-repressing Hill promoters; signed graph is
`toggleEdges`. -/
def toggle : GRN :=
  { nodes := [ species "TF1" .regulator, species "TF2" .regulator,
               hillRep "P1", hillRep "P2" ],
    edges := [ ⟨"TF2", "P1", 0⟩, ⟨"P1", "TF1", 0⟩, ⟨"TF1", "P2", 0⟩, ⟨"P2", "TF2", 0⟩ ] }

#eval signedInteractionGraph sensor   -- [("aTc", "TF1", 1), ("TF1", "GFP", -1)]
#eval isMonotone sensor               -- true
#eval certifies sensor .sensor        -- true
#eval signedInteractionGraph toggle   -- [("TF2", "TF1", -1), ("TF1", "TF2", -1)]
#eval hasPositiveLoop toggle          -- true
#eval certifies toggle .switch        -- true

/-- A `hill2` gate `alpha = [0, 100, 0, 100]`: a pass-through of its port-0 input (`X`), inert in
port-1 (`Y`). Locks the LOICA port convention: the edge lands on `X`, not `Y`. -/
def hill2Pass : Node :=
  { id := "G", kind := .hill2, nInputs := 2,
    params := [("alpha", .list [.num 0, .num 100, .num 0, .num 100])] }

def logicGate : GRN :=
  { nodes := [ species "X" .regulator, species "Y" .regulator, hill2Pass, species "Z" .reporter ],
    edges := [ ⟨"X", "G", 0⟩, ⟨"Y", "G", 1⟩, ⟨"G", "Z", 0⟩ ] }

#eval signedInteractionGraph logicGate  -- [("X", "Z", 1)]: port-0 (X) drives, port-1 (Y) inert

/-! ### GRN-level certificates, kernel-checked

With rational kinetics the sign extraction reduces in the kernel, so a certificate holds by `decide`
directly on the `GRN`, not merely on its precomputed signed graph. -/

example : signedInteractionGraph logicGate = [("X", "Z", 1)] := by decide
example : isMonotone sensor = true := by decide
example : certifies sensor .sensor = true := by decide
example : hasPositiveLoop toggle = true := by decide
example : certifies toggle .switch = true := by decide

end GRN.Examples
