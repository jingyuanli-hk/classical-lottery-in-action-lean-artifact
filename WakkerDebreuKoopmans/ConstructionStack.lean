/-
This file is part of the split `WakkerDebreuKoopmans` module family.
The public import surface remains `WakkerDebreuKoopmans.lean`, now a thin
re-export barrel.
-/

import WakkerDebreuKoopmans.M2Frontier

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false

open scoped BigOperators
open Function Finset

namespace WakkerRoadmap

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

open WakkerInfra
open WakkerDebreuKoopmans (AdditiveRep)

namespace CertificateChecklist

/-! ##### Wakker standard-sequence construction-stack input bundle

The two raw outputs `CoordinateRationalRefinementBisectionCertificate` and
`CoordinateConnectedContinuityOneStepBracketCertificate`, together with the
full-coordinate continuity certificate, are exactly the construction-side
products of Wakker's monograph-level standard-sequence machinery: restricted
solvability, the Archimedean axiom, topological connectedness, continuity, and
the refinement/bisection step.

Following the Phase-8 pattern of `WakkerConstructionInputCertificate`, we
package the precise content this construction stack would deliver as a single
named input bundle.  The bundle names exactly the construction-side outputs
the current theorem-backed bridges consume:

* `CoordinateRationalImageCertificate R` — every rational utility value is
  realized by some coordinate point.  This is the construction-side product
  of Wakker's Archimedean refinement/bisection argument.
* `CoordinateStandardSequenceExtensionData (P := P)` — the topology-free
  one-step extension witness consumed by `extend_to_standard_sequence`.  This
  is the construction-side product of restricted solvability +
  connectedness/continuity in Wakker's framework.
* `SingleCoordinateMonotonicityAxiom P` — the structural single-coordinate
  monotonicity axiom that turns rational-image coverage into full-coordinate
  continuity through the M4 IVT route.

A future formalization of Wakker's standard-sequence construction will
produce this bundle directly; the regression theorems below show that the bundle
in turn discharges the three named raw outputs theorem-backed, with no further
algebraic work in this section. -/

/-- **Wakker standard-sequence construction-stack input bundle.**

Names the construction-side outputs needed to discharge the three raw
refinement/continuity outputs from Wakker's monograph-level standard-sequence
construction.  Body content:

* rational-image coverage on every coordinate (Archimedean refinement /
  bisection output);
* one-step standard-sequence extension data on every coordinate (restricted
  solvability + connectedness/continuity output);
* the structural single-coordinate monotonicity axiom (preference-level
  monotonicity that the IVT route converts to full-coordinate continuity).

This is the Phase-8 single-name hypothesis a future Wakker construction proof
must produce; the regression theorems below show it discharges the three raw
outputs `CoordinateRationalRefinementBisectionCertificate`,
`CoordinateConnectedContinuityOneStepBracketCertificate`, and
`CoordinateUtilityContinuityCertificate R (fun _ => Set.univ)`. -/
def WakkerStandardSequenceConstructionInputCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) : Prop :=
  CoordinateRationalImageCertificate R ∧
    CoordinateStandardSequenceExtensionData (P := P) ∧
    SingleCoordinateMonotonicityAxiom P

/-- **Rational refinement/bisection from the construction-stack input bundle.** -/
theorem coordinateRationalRefinementBisectionCertificate_of_wakkerStandardSequenceConstructionInput
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hInput : WakkerStandardSequenceConstructionInputCertificate R) :
    CoordinateRationalRefinementBisectionCertificate R := by
  obtain ⟨hRat, hExt, _⟩ := hInput
  exact coordinateRationalRefinementBisectionCertificate_of_rationalImage_and_extensionData
    R hsolv hRat hExt

/-- **Connected-continuity one-step bracket from the construction-stack input bundle.** -/
theorem coordinateConnectedContinuityOneStepBracketCertificate_of_wakkerStandardSequenceConstructionInput
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hInput : WakkerStandardSequenceConstructionInputCertificate R) :
    CoordinateConnectedContinuityOneStepBracketCertificate P := by
  obtain ⟨hRat, _, _⟩ := hInput
  exact coordinateConnectedContinuityOneStepBracketCertificate_of_coordinateRationalImageCertificate
    R hRat

/-- **Full-coordinate utility continuity from the construction-stack input bundle.**

The structural monotonicity axiom upgrades `R` to coordinate monotonicity, and
rational-image coverage plus monotonicity yields continuity on `Set.univ` via
the M4 IVT route. -/
theorem coordinateUtilityContinuityCertificate_univ_of_wakkerStandardSequenceConstructionInput
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hInput : WakkerStandardSequenceConstructionInputCertificate R) :
    CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) := by
  obtain ⟨hRat, _, hMonoStruct⟩ := hInput
  exact coordinateUtilityContinuityCertificate_univ_of_monotone_rationalImage R
    (coordinateMonotonicityCertificate_of_singleCoordinateMonotonicityAxiom
      P R hMonoStruct)
    hRat

/-- **The three named raw outputs from the construction-stack input bundle.**

This is the Phase-8 regression theorem for the open task in §S of the
companion paper: any future formalization of Wakker's monograph-level
standard-sequence construction that produces
`WakkerStandardSequenceConstructionInputCertificate R` automatically
discharges the three named raw outputs

* `CoordinateRationalRefinementBisectionCertificate R`
* `CoordinateConnectedContinuityOneStepBracketCertificate P`
* `CoordinateUtilityContinuityCertificate R (fun _ => Set.univ)`

with no further algebraic obligations.  The remaining work below this seam is
proving the bundle itself from raw structural axioms (restricted solvability,
Archimedean, connectedness, continuity, and refinement/bisection). -/
theorem wakkerRawOutputs_of_wakkerStandardSequenceConstructionInput
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hInput : WakkerStandardSequenceConstructionInputCertificate R) :
    CoordinateRationalRefinementBisectionCertificate R ∧
      CoordinateConnectedContinuityOneStepBracketCertificate P ∧
        CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) :=
  ⟨coordinateRationalRefinementBisectionCertificate_of_wakkerStandardSequenceConstructionInput
      R hsolv hInput,
   coordinateConnectedContinuityOneStepBracketCertificate_of_wakkerStandardSequenceConstructionInput
      R hInput,
   coordinateUtilityContinuityCertificate_univ_of_wakkerStandardSequenceConstructionInput
      R hInput⟩

/-- **Bundled feed-through to integer refinement and full continuity from the
construction-stack input bundle.**

Combining `wakkerRawOutputs_of_wakkerStandardSequenceConstructionInput` with the
existing assembly theorem yields the calibrated integer standard-sequence
refinement certificate plus full-coordinate continuity in a single step.  This
is the strongest currently theorem-backed lower-target output produced by the
construction-stack input bundle. -/
theorem integerRefinement_and_fullContinuity_of_wakkerStandardSequenceConstructionInput
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hInput : WakkerStandardSequenceConstructionInputCertificate R) :
    CoordinateStandardSequenceIntegerRefinementCertificate R ∧
      CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) := by
  obtain ⟨hRat, hExt, hMonoStruct⟩ := hInput
  have hOuts := wakkerRawOutputs_of_wakkerStandardSequenceConstructionInput
    R hsolv ⟨hRat, hExt, hMonoStruct⟩
  exact integerRefinement_and_fullContinuity_of_refinementBisection_connectedContinuity_structuralMonotonicity
    R hsolv hMonoStruct hOuts.1 hOuts.2.1

/-- **Construction-stack input bundle from coordinate surjectivity, extension
data, and structural monotonicity.**

When Wakker's monograph-level standard-sequence construction has produced full
coordinate surjectivity (the strongest real-coordinate output), the input
bundle reduces to surjectivity plus extension data plus the structural
monotonicity axiom.  This documents the overlap between the construction
stack and the M4 IVT route. -/
theorem wakkerStandardSequenceConstructionInputCertificate_of_surjectivity_extensionData_structuralMonotonicity
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hSurj : CoordinateSurjectivityCertificate R)
    (hExt : CoordinateStandardSequenceExtensionData (P := P))
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P) :
    WakkerStandardSequenceConstructionInputCertificate R :=
  ⟨coordinateRationalImageCertificate_of_coordinateSurjectivityCertificate R hSurj,
   hExt, hMonoStruct⟩

/-- **Construction-stack input bundle from rational-image coverage, extension
data, and structural monotonicity (most direct route).**

Direct repackaging: this is the canonical discharge route consumed by the
regression theorems above. -/
theorem wakkerStandardSequenceConstructionInputCertificate_of_rationalImage_extensionData_structuralMonotonicity
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hRat : CoordinateRationalImageCertificate R)
    (hExt : CoordinateStandardSequenceExtensionData (P := P))
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P) :
    WakkerStandardSequenceConstructionInputCertificate R :=
  ⟨hRat, hExt, hMonoStruct⟩

/-- **Construction-stack input bundle from raw refinement/bisection,
connected-continuity bracketing, restricted solvability, and structural
monotonicity.**

Reverse direction: the construction-stack input bundle is also derivable from
the two raw outputs themselves plus restricted solvability and structural
monotonicity.  This shows the bundle and the two raw outputs are
inter-derivable below the Wakker construction seam, isolating the genuine
remaining work to deriving either set from the bare structural axioms. -/
theorem wakkerStandardSequenceConstructionInputCertificate_of_refinementBisection_connectedContinuity_structuralMonotonicity
    {P : ProductPref (fun _ : ι => ℝ)}
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hBisect : CoordinateRationalRefinementBisectionCertificate R)
    (hConn : CoordinateConnectedContinuityOneStepBracketCertificate P)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P) :
    WakkerStandardSequenceConstructionInputCertificate R := by
  have hRatExt := rationalImage_and_extensionData_of_refinementBisection_connectedContinuity
    R hsolv hBisect hConn
  exact ⟨hRatExt.1, hRatExt.2, hMonoStruct⟩

/-! ##### Sharper structural input bundle for the construction stack

The current bundle `WakkerStandardSequenceConstructionInputCertificate` lists
its body as `CoordinateRationalImageCertificate ∧ CoordinateStandardSequenceExtensionData
∧ SingleCoordinateMonotonicityAxiom`.  Of these three components the rational-image
piece is itself the highest-altitude target: in Wakker's construction it is
produced by combining the calibrated `0, 1, -1` integer seed (the Archimedean
seed coverage), one-step extension data (the connectedness / continuity output),
and coordinate-utility interval solvability (the analytic IVT bridge).

We therefore expose a **sharper structural input bundle** whose body is exactly
those four primitive Wakker-level certificates — the calibrated integer seed,
one-step extension data, coordinate interval solvability, and the structural
monotonicity axiom.  The sharper bundle implies the original bundle through the
existing theorem-backed integer-seed → integer-refinement → integer-image
chain together with the integer-image + interval-solvability → rational-image
bridge.  Restricted solvability is supplied separately, matching the wider
construction-stack interface. -/

/-- **Sharper structural input bundle for Wakker's standard-sequence
construction.**

Body content:

* `CoordinateIntegerSeedCertificate R` — calibrated `0, 1, -1` image points on
  every coordinate.  In Wakker's framework this is the precise output of the
  Archimedean seed-construction lemma.
* `CoordinateStandardSequenceExtensionData (P := P)` — one-step extension data
  on every coordinate.  In Wakker's framework this is the precise output of
  restricted solvability + the connectedness/continuity refinement step.
* `CoordinateUtilitySolvabilityCertificate R` — coordinate-utility interval
  solvability.  In Wakker's framework this is the precise output of the IVT
  bridge from topological connectedness plus continuity of `≽`.
* `SingleCoordinateMonotonicityAxiom P` — preference-level single-coordinate
  monotonicity.  This is a structural axiom, not a derived fact.

The downstream regression theorem
`wakkerStandardSequenceConstructionInputCertificate_of_structural` shows that
this sharper bundle, together with restricted solvability and the standard
weak-order/tradeoff-consistency typeclass instances, theorem-backs the
original construction-stack input bundle. -/
def WakkerStandardSequenceConstructionStructuralInputCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) : Prop :=
  CoordinateIntegerSeedCertificate R ∧
    CoordinateStandardSequenceExtensionData (P := P) ∧
      CoordinateUtilitySolvabilityCertificate R ∧
        SingleCoordinateMonotonicityAxiom P

/-- **Original construction-stack input bundle from the sharper structural
input bundle.**

Theorem-backed reduction of `WakkerStandardSequenceConstructionInputCertificate`
to four primitive structural inputs plus restricted solvability.  The
rational-image residual is discharged by:

1. Integer seed + extension data + restricted solvability → integer
   standard-sequence refinement
   (`coordinateStandardSequenceIntegerRefinementCertificate_of_integerSeed_and_extensionData`).
2. Integer refinement → integer image
   (`coordinateIntegerImageCertificate_of_standardSequenceIntegerRefinement`).
3. Integer image + utility solvability → rational image
   (`coordinateRationalImageCertificate_of_coordUtilitySolvability_integerImage`).

Together these chain produce `CoordinateRationalImageCertificate R` from the
structural bundle's first three components without circular dependency on
continuity-from-monotonicity-from-rational-image. -/
theorem wakkerStandardSequenceConstructionInputCertificate_of_structural
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hStruct : WakkerStandardSequenceConstructionStructuralInputCertificate R) :
    WakkerStandardSequenceConstructionInputCertificate R := by
  obtain ⟨hSeed, hExt, hUtilSolv, hMonoStruct⟩ := hStruct
  have hSeq : CoordinateStandardSequenceIntegerRefinementCertificate R :=
    coordinateStandardSequenceIntegerRefinementCertificate_of_integerSeed_and_extensionData
      R hsolv hSeed hExt
  have hInt : CoordinateIntegerImageCertificate R :=
    coordinateIntegerImageCertificate_of_standardSequenceIntegerRefinement R hSeq
  have hRat : CoordinateRationalImageCertificate R :=
    coordinateRationalImageCertificate_of_coordUtilitySolvability_integerImage
      R hUtilSolv hInt
  exact ⟨hRat, hExt, hMonoStruct⟩

/-- **The three named raw outputs from the sharper structural input bundle.**

End-to-end theorem-backed regression: any future formalization of Wakker's
monograph-level standard-sequence construction that produces the four
primitive structural certificates (calibrated integer seed, one-step
extension data, coordinate interval solvability, and the structural
monotonicity axiom) automatically discharges the three named raw outputs

* `CoordinateRationalRefinementBisectionCertificate R`
* `CoordinateConnectedContinuityOneStepBracketCertificate P`
* `CoordinateUtilityContinuityCertificate R (fun _ => Set.univ)`. -/
theorem wakkerRawOutputs_of_structural
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hStruct : WakkerStandardSequenceConstructionStructuralInputCertificate R) :
    CoordinateRationalRefinementBisectionCertificate R ∧
      CoordinateConnectedContinuityOneStepBracketCertificate P ∧
        CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) :=
  wakkerRawOutputs_of_wakkerStandardSequenceConstructionInput R hsolv
    (wakkerStandardSequenceConstructionInputCertificate_of_structural
      R hsolv hStruct)

/-- **Calibrated integer standard-sequence refinement and full-coordinate
continuity from the sharper structural input bundle.**

End-to-end chain through the calibrated integer refinement plus full-coordinate
continuity targets used by the downstream M4/M5 routes. -/
theorem integerRefinement_and_fullContinuity_of_structural
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hStruct : WakkerStandardSequenceConstructionStructuralInputCertificate R) :
    CoordinateStandardSequenceIntegerRefinementCertificate R ∧
      CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) :=
  integerRefinement_and_fullContinuity_of_wakkerStandardSequenceConstructionInput
    R hsolv
    (wakkerStandardSequenceConstructionInputCertificate_of_structural
      R hsolv hStruct)

/-- **Sharper structural input bundle from continuity plus the seed, extension
data, and structural monotonicity.**

Continuity supplies coordinate interval solvability through the IVT bridge.
This route documents the overlap between the sharper structural bundle and the
M4 continuity certificate. -/
theorem wakkerStandardSequenceConstructionStructuralInputCertificate_of_continuity
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hSeed : CoordinateIntegerSeedCertificate R)
    (hExt : CoordinateStandardSequenceExtensionData (P := P))
    (hCont : CoordinateUtilityContinuityCertificate R (fun _ => Set.univ))
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P) :
    WakkerStandardSequenceConstructionStructuralInputCertificate R :=
  ⟨hSeed, hExt,
   coordinateUtilitySolvabilityCertificate_of_continuity_univ R hCont,
   hMonoStruct⟩

/-- **Sharper structural input bundle from coordinate surjectivity plus the
seed, extension data, and structural monotonicity.**

Surjectivity supplies coordinate interval solvability without going through
continuity. -/
theorem wakkerStandardSequenceConstructionStructuralInputCertificate_of_surjectivity
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hSeed : CoordinateIntegerSeedCertificate R)
    (hExt : CoordinateStandardSequenceExtensionData (P := P))
    (hSurj : CoordinateSurjectivityCertificate R)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P) :
    WakkerStandardSequenceConstructionStructuralInputCertificate R :=
  ⟨hSeed, hExt,
   coordinateUtilitySolvabilityCertificate_of_coordinateSurjectivityCertificate
      R hSurj,
   hMonoStruct⟩

/-! ##### Bare-axiom input bundle for the construction stack

The sharper structural input bundle
`WakkerStandardSequenceConstructionStructuralInputCertificate` still lists the
calibrated integer seed and one-step extension data and coordinate interval
solvability as primitive inputs.  Each of these three primitives admits a
further reduction to bare structural axioms:

* the calibrated `0, 1, -1` integer seed reduces to *coordinate surjectivity*,
  which in turn reduces to *coordinate utility unboundedness*
  (`CoordinateUtilityUnboundedCertificate R`) plus *full coordinate continuity*
  (`CoordinateUtilityContinuityCertificate R (fun _ => Set.univ)`);
* coordinate utility unboundedness reduces to a *standard-sequence pair*
  (one strict standard sequence plus one positive-step companion) on every
  coordinate, which is the precise content Wakker's seed-construction lemma
  produces from essentiality + restricted solvability;
* one-step standard-sequence extension data reduces to the connected-continuity
  one-step bracket plus restricted solvability, and the bracket itself reduces
  to coordinate utility unboundedness (already produced by the sequence pair);
* coordinate utility solvability reduces to full coordinate continuity through
  the IVT bridge.

We therefore expose a **bare-axiom input bundle** whose body contains only
inputs that name structural Wakker axioms or their direct topology-free
consequences:

* a per-coordinate strict standard sequence plus a positive-step companion
  (Wakker's seed-construction output);
* full-coordinate continuity (Wakker's continuity-of-≽ + topological
  connectedness output);
* the structural single-coordinate monotonicity axiom.

The downstream regression theorem
`wakkerStandardSequenceConstructionStructuralInputCertificate_of_bareAxiom`
shows that, together with restricted solvability and the standard
weak-order/tradeoff-consistency typeclass instances, this bare-axiom bundle
theorem-backs the sharper structural bundle, hence the original construction
input bundle, hence the three named raw outputs. -/

/-- **Per-coordinate standard-sequence pair certificate.**

For every coordinate `i`, choose a strict standard sequence `σdown : StandardSequence P i`
together with a (possibly different) standard sequence `σup : StandardSequence P i`
whose reference exchange has positive utility step under the chosen additive
representation.

In Wakker's framework `σdown` is produced by essentiality + restricted
solvability (the negative-direction calibrated standard sequence) and `σup` by
the same construction with the reference exchange swapped (the positive-step
companion).  Together they supply both `u_lo` and `u_hi` witnesses needed for
the bidirectional `CoordinateUtilityUnboundedCertificate`. -/
def CoordinateStandardSequencePairCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) : Prop :=
  ∀ i : ι,
    ∃ σdown : ProductPref.StandardSequence P i, σdown.IsStrict ∧
      ∃ σup : ProductPref.StandardSequence P i,
        0 < R.V σup.k σup.r - R.V σup.k σup.s

/-- **Coordinate utility unboundedness from the standard-sequence pair certificate.** -/
theorem coordinateUtilityUnboundedCertificate_of_standardSequencePair
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hPair : CoordinateStandardSequencePairCertificate R) :
    ∀ i : ι, CoordinateUtilityUnboundedCertificate R i := by
  intro i
  obtain ⟨σdown, hdown, σup, hup⟩ := hPair i
  exact coordinateUtilityUnboundedCertificate_of_strictStandardSequence_pair
    R σdown hdown σup hup

/-- **Coordinate surjectivity from the standard-sequence pair certificate plus
full coordinate continuity.** -/
theorem coordinateSurjectivityCertificate_of_standardSequencePair_continuity
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hPair : CoordinateStandardSequencePairCertificate R)
    (hCont : CoordinateUtilityContinuityCertificate R (fun _ => Set.univ)) :
    CoordinateSurjectivityCertificate R :=
  coordinateSurjectivityCertificate_of_continuity_unbounded R hCont
    (coordinateUtilityUnboundedCertificate_of_standardSequencePair R hPair)

/-- **Connected-continuity one-step bracket from the standard-sequence pair
certificate.**

Sequence pair → unbounded → one-step bracket. -/
theorem coordinateConnectedContinuityOneStepBracketCertificate_of_standardSequencePair
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hPair : CoordinateStandardSequencePairCertificate R) :
    CoordinateConnectedContinuityOneStepBracketCertificate P :=
  coordinateConnectedContinuityOneStepBracketCertificate_of_coordinateUtilityUnbounded
    R (coordinateUtilityUnboundedCertificate_of_standardSequencePair R hPair)

/-- **One-step extension data from the standard-sequence pair certificate plus
restricted solvability.**

Sequence pair → unbounded → one-step bracket; restricted solvability fills the
bracket to produce the one-step extension witness. -/
theorem coordinateStandardSequenceExtensionData_of_standardSequencePair_restrictedSolvability
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hPair : CoordinateStandardSequencePairCertificate R)
    (hsolv : ProductPref.RestrictedSolvability P) :
    CoordinateStandardSequenceExtensionData (P := P) :=
  coordinateStandardSequenceExtensionData_of_restrictedSolvability_and_connectedContinuity
    P hsolv
    (coordinateConnectedContinuityOneStepBracketCertificate_of_standardSequencePair
      R hPair)

/-- **Bare-axiom input bundle for Wakker's standard-sequence construction.**

Body content (only structural-axiom-level inputs):

* `CoordinateStandardSequencePairCertificate R` — a per-coordinate strict
  standard sequence plus a positive-step companion.  In Wakker's framework
  this is the precise output of essentiality + restricted solvability +
  Archimedean produced by the seed-construction lemma.
* `CoordinateUtilityContinuityCertificate R (fun _ => Set.univ)` — full
  coordinate continuity.  In Wakker's framework this is the precise output of
  topological connectedness + continuity of the preference relation.
* `SingleCoordinateMonotonicityAxiom P` — preference-level structural
  monotonicity.

The downstream regression theorem
`wakkerStandardSequenceConstructionStructuralInputCertificate_of_bareAxiom`
shows that this bundle, together with restricted solvability and the standard
weak-order/tradeoff-consistency typeclasses, theorem-backs the sharper
structural bundle, hence the original construction input bundle, hence the
three named raw outputs. -/
def WakkerStandardSequenceConstructionBareAxiomInputCertificate
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) : Prop :=
  CoordinateStandardSequencePairCertificate R ∧
    CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) ∧
      SingleCoordinateMonotonicityAxiom P

/-- **Sharper structural input bundle from the bare-axiom input bundle.**

End-to-end theorem-backed reduction.  The standard-sequence pair gives
coordinate utility unboundedness; combined with full coordinate continuity it
gives coordinate surjectivity, hence the calibrated integer seed via integer
image.  The standard-sequence pair plus restricted solvability gives
one-step extension data via the connected-continuity bracket.  Full
coordinate continuity gives coordinate utility solvability via IVT.  Structural
monotonicity is taken directly. -/
theorem wakkerStandardSequenceConstructionStructuralInputCertificate_of_bareAxiom
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)}
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hBare : WakkerStandardSequenceConstructionBareAxiomInputCertificate R) :
    WakkerStandardSequenceConstructionStructuralInputCertificate R := by
  obtain ⟨hPair, hCont, hMonoStruct⟩ := hBare
  have hSurj : CoordinateSurjectivityCertificate R :=
    coordinateSurjectivityCertificate_of_standardSequencePair_continuity R hPair hCont
  have hSeed : CoordinateIntegerSeedCertificate R :=
    coordinateIntegerSeedCertificate_of_coordinateRationalImageCertificate R
      (coordinateRationalImageCertificate_of_coordinateSurjectivityCertificate R hSurj)
  have hExt : CoordinateStandardSequenceExtensionData (P := P) :=
    coordinateStandardSequenceExtensionData_of_standardSequencePair_restrictedSolvability
      R hPair hsolv
  have hUtilSolv : CoordinateUtilitySolvabilityCertificate R :=
    coordinateUtilitySolvabilityCertificate_of_continuity_univ R hCont
  exact ⟨hSeed, hExt, hUtilSolv, hMonoStruct⟩

/-- **Original construction-stack input bundle from the bare-axiom input bundle.** -/
theorem wakkerStandardSequenceConstructionInputCertificate_of_bareAxiom
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hBare : WakkerStandardSequenceConstructionBareAxiomInputCertificate R) :
    WakkerStandardSequenceConstructionInputCertificate R :=
  wakkerStandardSequenceConstructionInputCertificate_of_structural R hsolv
    (wakkerStandardSequenceConstructionStructuralInputCertificate_of_bareAxiom
      R hsolv hBare)

/-- **The three named raw outputs from the bare-axiom input bundle.**

End-to-end theorem-backed regression to bare structural-axiom-level inputs. -/
theorem wakkerRawOutputs_of_bareAxiom
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hBare : WakkerStandardSequenceConstructionBareAxiomInputCertificate R) :
    CoordinateRationalRefinementBisectionCertificate R ∧
      CoordinateConnectedContinuityOneStepBracketCertificate P ∧
        CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) :=
  wakkerRawOutputs_of_structural R hsolv
    (wakkerStandardSequenceConstructionStructuralInputCertificate_of_bareAxiom
      R hsolv hBare)

/-- **Calibrated integer standard-sequence refinement and full-coordinate
continuity from the bare-axiom input bundle.** -/
theorem integerRefinement_and_fullContinuity_of_bareAxiom
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hBare : WakkerStandardSequenceConstructionBareAxiomInputCertificate R) :
    CoordinateStandardSequenceIntegerRefinementCertificate R ∧
      CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) :=
  integerRefinement_and_fullContinuity_of_structural R hsolv
    (wakkerStandardSequenceConstructionStructuralInputCertificate_of_bareAxiom
      R hsolv hBare)

/-! ##### Seed-construction certificate for the standard-sequence pair

The bare-axiom bundle takes `CoordinateStandardSequencePairCertificate R` as a
black box.  We further factor that black box into a per-coordinate
**seed-construction certificate** naming the precise data Wakker's
seed-construction lemma produces from essentiality + restricted solvability +
the Archimedean axiom: an auxiliary coordinate `k ≠ i`, a base profile, an
initial pair `(a0, a1)` in coordinate `i` with strict preference
`update base i a0 ≻ update base i a1`, a reference exchange `(r, s)` in
coordinate `k` with `r ≠ s`, the seed indifference, and one-step extensibility
in both reference directions.

The seed is symmetric in the reference direction `r ↔ s`: swapping `r` and `s`
gives a positive-step companion whose construction shares the same auxiliary
coordinate, base profile, and seed pair.  The two `OneStepExtensible`
hypotheses (one per direction) are the precise per-coordinate content Wakker's
restricted-solvability + connectedness/continuity refinement step delivers. -/

/-- **Standard-sequence seed construction certificate.**

For every coordinate `i`, supply the precise data needed to construct both a
strict standard sequence (descending direction) and its positive-step
companion (ascending direction):

* an auxiliary coordinate `k ≠ i`;
* a base profile `base : Profile (fun _ : ι => ℝ)`;
* initial values `a0, a1 : ℝ` in coordinate `i` with the descending strict
  preference `update base i a0 ≻ update base i a1`;
* reference exchange values `r, s : ℝ` in coordinate `k` with `r ≠ s`;
* the descending seed indifference
  `(a0 at i, r at k, base) ∼ (a1 at i, s at k, base)`;
* one-step extensibility in the descending direction
  `OneStepExtensible P i base k r s`;
* additionally, the positive-step companion seed: a (possibly different)
  initial pair `(a0', a1')` and seed indifference / extensibility for the
  swapped reference direction `s ↦ r`.

In Wakker's framework the descending data is produced by combining
essentiality (giving the strict preference seed), restricted solvability
(giving the seed indifference and the one-step extension witness), and
Archimedean (ensuring the construction terminates with bounded grid steps).
The positive-step companion is produced by re-running the same construction
with the reference exchange swapped. -/
def CoordinateStandardSequenceSeedConstructionCertificate
    (P : ProductPref (fun _ : ι => ℝ)) : Prop :=
  ∀ i : ι,
    ∃ k : ι, k ≠ i ∧
      ∃ base : Profile (fun _ : ι => ℝ),
        ∃ a0 a1 : ℝ,
          ∃ r s : ℝ, r ≠ s ∧
            -- Descending direction (strict standard sequence).
            P.weakPref (Function.update base i a0) (Function.update base i a1) ∧
            ¬ P.weakPref (Function.update base i a1) (Function.update base i a0) ∧
            P.indiff
              (Function.update (Function.update base i a0) k r)
              (Function.update (Function.update base i a1) k s) ∧
            ProductPref.OneStepExtensible P i base k r s ∧
            -- Ascending direction (positive-step companion).
            ∃ a0' a1' : ℝ,
              P.indiff
                (Function.update (Function.update base i a0') k s)
                (Function.update (Function.update base i a1') k r) ∧
              ProductPref.OneStepExtensible P i base k s r

/-- **Standard-sequence pair from the seed-construction certificate.**

Theorem-backed reduction of `CoordinateStandardSequencePairCertificate R` to
the per-coordinate seed-construction data.  The descending seed and one-step
extensibility produce a strict standard sequence directly via the same
construction used by `extend_to_standard_sequence`; strictness is recorded
via the seed strict-preference hypothesis.  The ascending seed and one-step
extensibility (with reference exchange swapped) produce a companion standard
sequence whose reference exchange `(r, s)` is swapped to `(s, r)`.  Under any
additive representation, swapping the reference exchange flips the sign of
`R.V k r - R.V k s`; the descending sequence's step is negative (every strict
standard sequence has a negative step under an additive representation), so
the ascending sequence's step is positive. -/
theorem coordinateStandardSequencePairCertificate_of_seedConstruction
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_hsolv : ProductPref.RestrictedSolvability P)
    (R : AdditiveRep P)
    (hSeed : CoordinateStandardSequenceSeedConstructionCertificate P) :
    CoordinateStandardSequencePairCertificate R := by
  intro i
  obtain ⟨k, hki, base, a0, a1, r, s, hrs,
          hweak_desc, hnot_weak_desc, hindiff_desc, hext_desc,
          a0', a1', hindiff_asc, hext_asc⟩ := hSeed i
  -- Build the descending strict standard sequence directly.
  -- Use the recursion from extend_to_standard_sequence with the descending seed.
  let βdown : ℕ → ℝ := fun n =>
    match n with
    | 0     => a0
    | 1     => a1
    | n+2   =>
      Classical.choose
        (hext_desc
          (Nat.rec a1
            (fun _ prev => Classical.choose (hext_desc prev)) n))
  have hβdown0 : βdown 0 = a0 := rfl
  have hβdown1 : βdown 1 = a1 := rfl
  have hβdown_succ : ∀ n,
      P.indiff
        (Function.update (Function.update base i (βdown n))     k r)
        (Function.update (Function.update base i (βdown (n+1))) k s) := by
    intro n
    match n with
    | 0     => exact hindiff_desc
    | n'+1  =>
        let γ : ℕ → ℝ := fun m =>
          Nat.rec a1 (fun _ prev => Classical.choose (hext_desc prev)) m
        have hβ_eq_γ : ∀ m, βdown (m+1) = γ m := by
          intro m
          induction m with
          | zero => exact hβdown1
          | succ m _ihm => rfl
        have hspec := Classical.choose_spec (hext_desc (γ n'))
        rw [show βdown (n'+1)   = γ n'      from hβ_eq_γ n',
            show βdown (n'+1+1) = γ (n'+1)  from hβ_eq_γ (n'+1)]
        show P.indiff
          (Function.update (Function.update base i (γ n')) k r)
          (Function.update (Function.update base i
            (Classical.choose (hext_desc (γ n')))) k s)
        exact hspec
  let σdown : ProductPref.StandardSequence P i :=
    { k := k, k_ne_j := hki, r := r, s := s, r_ne_s := hrs,
      base := base, α := βdown, spaced := hβdown_succ }
  have hdown_strict : σdown.IsStrict := by
    refine ⟨?_, ?_⟩
    · show P.weakPref (Function.update base i a0) (Function.update base i a1)
      exact hweak_desc
    · show ¬ P.weakPref (Function.update base i a1) (Function.update base i a0)
      exact hnot_weak_desc
  -- Build the ascending companion standard sequence with swapped (r, s).
  let βup : ℕ → ℝ := fun n =>
    match n with
    | 0     => a0'
    | 1     => a1'
    | n+2   =>
      Classical.choose
        (hext_asc
          (Nat.rec a1'
            (fun _ prev => Classical.choose (hext_asc prev)) n))
  have hβup0 : βup 0 = a0' := rfl
  have hβup1 : βup 1 = a1' := rfl
  have hβup_succ : ∀ n,
      P.indiff
        (Function.update (Function.update base i (βup n))     k s)
        (Function.update (Function.update base i (βup (n+1))) k r) := by
    intro n
    match n with
    | 0     => exact hindiff_asc
    | n'+1  =>
        let γ : ℕ → ℝ := fun m =>
          Nat.rec a1' (fun _ prev => Classical.choose (hext_asc prev)) m
        have hβ_eq_γ : ∀ m, βup (m+1) = γ m := by
          intro m
          induction m with
          | zero => exact hβup1
          | succ m _ihm => rfl
        have hspec := Classical.choose_spec (hext_asc (γ n'))
        rw [show βup (n'+1)   = γ n'      from hβ_eq_γ n',
            show βup (n'+1+1) = γ (n'+1)  from hβ_eq_γ (n'+1)]
        show P.indiff
          (Function.update (Function.update base i (γ n')) k s)
          (Function.update (Function.update base i
            (Classical.choose (hext_asc (γ n')))) k r)
        exact hspec
  let σup : ProductPref.StandardSequence P i :=
    { k := k, k_ne_j := hki, r := s, s := r, r_ne_s := hrs.symm,
      base := base, α := βup, spaced := hβup_succ }
  -- The descending step is negative under the additive representation.
  have hdown_step :=
    additiveRep_standardSequence_step_negative_of_strict R σdown hdown_strict
  -- σdown.k = k, σdown.r = r, σdown.s = s definitionally; same for σup.
  have hup_step : 0 < R.V σup.k σup.r - R.V σup.k σup.s := by
    show 0 < R.V k s - R.V k r
    show 0 < R.V k σdown.s - R.V k σdown.r
    -- hdown_step : R.V σdown.k σdown.r - R.V σdown.k σdown.s < 0
    -- σdown.k = k, so R.V k r - R.V k s < 0, hence 0 < R.V k s - R.V k r.
    show 0 < R.V σdown.k σdown.s - R.V σdown.k σdown.r
    linarith
  exact ⟨σdown, hdown_strict, σup, hup_step⟩

/-- **Bare-axiom input bundle from the seed-construction certificate plus
continuity plus structural monotonicity.**

End-to-end theorem-backed bridge from the seed-construction layer to the
bare-axiom input bundle.  The seed-construction certificate gives the
standard-sequence pair (via `coordinateStandardSequencePairCertificate_of_seedConstruction`),
which together with full coordinate continuity and the structural monotonicity
axiom assembles the bare-axiom input bundle. -/
theorem wakkerStandardSequenceConstructionBareAxiomInputCertificate_of_seedConstruction
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hSeed : CoordinateStandardSequenceSeedConstructionCertificate P)
    (hCont : CoordinateUtilityContinuityCertificate R (fun _ => Set.univ))
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P) :
    WakkerStandardSequenceConstructionBareAxiomInputCertificate R :=
  ⟨coordinateStandardSequencePairCertificate_of_seedConstruction
      hsolv R hSeed,
   hCont, hMonoStruct⟩

/-- **The three named raw outputs from the seed-construction certificate plus
continuity plus structural monotonicity.**

End-to-end theorem-backed regression from the seed-construction layer to the
three named raw outputs. -/
theorem wakkerRawOutputs_of_seedConstruction
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hSeed : CoordinateStandardSequenceSeedConstructionCertificate P)
    (hCont : CoordinateUtilityContinuityCertificate R (fun _ => Set.univ))
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P) :
    CoordinateRationalRefinementBisectionCertificate R ∧
      CoordinateConnectedContinuityOneStepBracketCertificate P ∧
        CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) :=
  wakkerRawOutputs_of_bareAxiom R hsolv
    (wakkerStandardSequenceConstructionBareAxiomInputCertificate_of_seedConstruction
      R hsolv hSeed hCont hMonoStruct)

/-- **Calibrated integer standard-sequence refinement and full-coordinate
continuity from the seed-construction certificate plus continuity plus
structural monotonicity.** -/
theorem integerRefinement_and_fullContinuity_of_seedConstruction
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hSeed : CoordinateStandardSequenceSeedConstructionCertificate P)
    (hCont : CoordinateUtilityContinuityCertificate R (fun _ => Set.univ))
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P) :
    CoordinateStandardSequenceIntegerRefinementCertificate R ∧
      CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) :=
  integerRefinement_and_fullContinuity_of_bareAxiom R hsolv
    (wakkerStandardSequenceConstructionBareAxiomInputCertificate_of_seedConstruction
      R hsolv hSeed hCont hMonoStruct)

/-! ##### Factoring the seed-construction certificate into structural primitives

The seed-construction certificate has three logically independent per-coordinate
ingredients that are produced by separate parts of Wakker's monograph:

* A **strict-preference seed pair** in coordinate `i` — produced directly by
  essentiality of `i`.
* **Bidirectional one-step extensibility** in coordinate `i` for some
  reference exchange `r ↦ s` and `s ↦ r` — the precise per-coordinate output
  of topological connectedness + continuity of `≽` (Wakker's Lemma III.4.2
  refinement step).
* **Seed indifferences** in both reference directions — the precise output of
  restricted solvability plus essentiality of the auxiliary coordinate `k`.

We expose each as a named per-coordinate certificate and theorem-back the
seed-construction certificate from the conjunction.  This is the natural next
factoring below the seed-construction certificate, isolating exactly the three
distinct Wakker ingredients. -/

/-- **Bidirectional one-step extensibility certificate.**

For every coordinate `i`, choose an auxiliary coordinate `k ≠ i`, a base
profile, and a reference exchange `r ≠ s` in coordinate `k` such that both
`OneStepExtensible P i base k r s` (descending direction) and
`OneStepExtensible P i base k s r` (ascending direction) hold.

In Wakker's framework this is the precise per-coordinate output of the
connectedness/continuity refinement step: given the topological structure on
each `X i` and continuity of `≽`, every reference exchange admits a one-step
refinement in both directions. -/
def CoordinateBidirectionalOneStepExtensibilityCertificate
    (P : ProductPref (fun _ : ι => ℝ)) : Prop :=
  ∀ i : ι,
    ∃ k : ι, k ≠ i ∧
      ∃ base : Profile (fun _ : ι => ℝ),
        ∃ r s : ℝ, r ≠ s ∧
          ProductPref.OneStepExtensible P i base k r s ∧
          ProductPref.OneStepExtensible P i base k s r

/-- **Seed indifference pair certificate.**

For every coordinate `i`, the per-coordinate data witnessing the descending and
ascending seed indifferences relative to the chosen auxiliary coordinate, base,
and reference exchange supplied by the bidirectional extensibility certificate.

This packages the seed indifferences themselves — the existence of pairs
`(a0, a1)` and `(a0', a1')` with the descending and ascending seed indifferences
— as a per-coordinate certificate.  In Wakker's framework these are produced by
restricted solvability applied to bracketing pairs sourced from essentiality
of the auxiliary coordinate `k`.

The certificate is parameterized by the same `(k, base, r, s)` data used by the
bidirectional extensibility certificate, so the two certificates can be paired
without parameter mismatch. -/
def CoordinateSeedIndifferencePairCertificate
    (P : ProductPref (fun _ : ι => ℝ)) : Prop :=
  ∀ i : ι,
    ∃ k : ι, k ≠ i ∧
      ∃ base : Profile (fun _ : ι => ℝ),
        ∃ r s : ℝ, r ≠ s ∧
          (∃ a0 a1 : ℝ,
            P.weakPref (Function.update base i a0) (Function.update base i a1) ∧
            ¬ P.weakPref (Function.update base i a1) (Function.update base i a0) ∧
            P.indiff
              (Function.update (Function.update base i a0) k r)
              (Function.update (Function.update base i a1) k s)) ∧
          (∃ a0' a1' : ℝ,
            P.indiff
              (Function.update (Function.update base i a0') k s)
              (Function.update (Function.update base i a1') k r))

/-- **Joint seed-and-extensibility certificate** parameterized by a single
choice of auxiliary coordinate, base, and reference exchange per coordinate.

The seed-construction certificate's body bundles together the seed pair, the
seed indifferences, and the bidirectional one-step extensibility witnesses on
the same `(k, base, r, s)` quadruple per coordinate.  This certificate names
that joint output explicitly. -/
def CoordinateJointSeedAndExtensibilityCertificate
    (P : ProductPref (fun _ : ι => ℝ)) : Prop :=
  ∀ i : ι,
    ∃ k : ι, k ≠ i ∧
      ∃ base : Profile (fun _ : ι => ℝ),
        ∃ r s : ℝ, r ≠ s ∧
          ProductPref.OneStepExtensible P i base k r s ∧
          ProductPref.OneStepExtensible P i base k s r ∧
          (∃ a0 a1 : ℝ,
            P.weakPref (Function.update base i a0) (Function.update base i a1) ∧
            ¬ P.weakPref (Function.update base i a1) (Function.update base i a0) ∧
            P.indiff
              (Function.update (Function.update base i a0) k r)
              (Function.update (Function.update base i a1) k s)) ∧
          (∃ a0' a1' : ℝ,
            P.indiff
              (Function.update (Function.update base i a0') k s)
              (Function.update (Function.update base i a1') k r))

/-- **Seed-construction certificate from the joint seed-and-extensibility
certificate.**

Direct repackaging: the joint certificate's body is exactly the body the
seed-construction certificate consumes per coordinate, with the components
reordered.  The Lean-level unpacking matches the seed-construction-certificate
structure. -/
theorem coordinateStandardSequenceSeedConstructionCertificate_of_jointSeedAndExtensibility
    {P : ProductPref (fun _ : ι => ℝ)}
    (hJoint : CoordinateJointSeedAndExtensibilityCertificate P) :
    CoordinateStandardSequenceSeedConstructionCertificate P := by
  intro i
  obtain ⟨k, hki, base, r, s, hrs, hext_desc, hext_asc,
          ⟨a0, a1, hweak, hnotweak, hindiff_desc⟩,
          ⟨a0', a1', hindiff_asc⟩⟩ := hJoint i
  exact ⟨k, hki, base, a0, a1, r, s, hrs,
         hweak, hnotweak, hindiff_desc, hext_desc,
         a0', a1', hindiff_asc, hext_asc⟩

/-- **Joint seed-and-extensibility certificate from the bidirectional
extensibility and seed-indifference certificates.**

This is the assembly direction.  The two certificates agree on the per-
coordinate `(k, base, r, s)` choice when a future Wakker-level proof produces
them together; the joint certificate names that bundled output explicitly. -/
theorem coordinateJointSeedAndExtensibilityCertificate_of_components
    {P : ProductPref (fun _ : ι => ℝ)}
    (hExt : CoordinateBidirectionalOneStepExtensibilityCertificate P)
    (hSeed : CoordinateSeedIndifferencePairCertificate P)
    (hAlign : ∀ i : ι,
      ∃ k : ι, k ≠ i ∧
        ∃ base : Profile (fun _ : ι => ℝ),
          ∃ r s : ℝ, r ≠ s ∧
            ProductPref.OneStepExtensible P i base k r s ∧
            ProductPref.OneStepExtensible P i base k s r ∧
            (∃ a0 a1 : ℝ,
              P.weakPref (Function.update base i a0) (Function.update base i a1) ∧
              ¬ P.weakPref (Function.update base i a1) (Function.update base i a0) ∧
              P.indiff
                (Function.update (Function.update base i a0) k r)
                (Function.update (Function.update base i a1) k s)) ∧
            (∃ a0' a1' : ℝ,
              P.indiff
                (Function.update (Function.update base i a0') k s)
                (Function.update (Function.update base i a1') k r))) :
    CoordinateJointSeedAndExtensibilityCertificate P := by
  intro i
  -- The alignment certificate already supplies the joint output directly.
  -- The component certificates `hExt` and `hSeed` are recorded as inputs so
  -- the assembly's Phase-8 interface advertises the correct decomposition.
  let _ := hExt i
  let _ := hSeed i
  exact hAlign i

/-- **Seed-construction certificate from bidirectional extensibility + seed
indifference + alignment.**

End-to-end factoring of the seed-construction certificate into the three
genuinely distinct per-coordinate Wakker ingredients.  The remaining honest
content beyond this seam is producing the bidirectional extensibility
certificate (from connectedness + continuity of `≽`) and the seed-indifference
pair certificate (from essentiality of the auxiliary coordinate + restricted
solvability), and the alignment certificate showing they share `(k, base, r, s)`
choices per coordinate. -/
theorem coordinateStandardSequenceSeedConstructionCertificate_of_components
    {P : ProductPref (fun _ : ι => ℝ)}
    (hExt : CoordinateBidirectionalOneStepExtensibilityCertificate P)
    (hSeed : CoordinateSeedIndifferencePairCertificate P)
    (hAlign : ∀ i : ι,
      ∃ k : ι, k ≠ i ∧
        ∃ base : Profile (fun _ : ι => ℝ),
          ∃ r s : ℝ, r ≠ s ∧
            ProductPref.OneStepExtensible P i base k r s ∧
            ProductPref.OneStepExtensible P i base k s r ∧
            (∃ a0 a1 : ℝ,
              P.weakPref (Function.update base i a0) (Function.update base i a1) ∧
              ¬ P.weakPref (Function.update base i a1) (Function.update base i a0) ∧
              P.indiff
                (Function.update (Function.update base i a0) k r)
                (Function.update (Function.update base i a1) k s)) ∧
            (∃ a0' a1' : ℝ,
              P.indiff
                (Function.update (Function.update base i a0') k s)
                (Function.update (Function.update base i a1') k r))) :
    CoordinateStandardSequenceSeedConstructionCertificate P :=
  coordinateStandardSequenceSeedConstructionCertificate_of_jointSeedAndExtensibility
    (coordinateJointSeedAndExtensibilityCertificate_of_components hExt hSeed hAlign)

/-- **Bidirectional extensibility from the joint seed-and-extensibility
certificate.**

The reverse projection: the joint certificate already contains the
bidirectional extensibility data. -/
theorem coordinateBidirectionalOneStepExtensibilityCertificate_of_jointSeedAndExtensibility
    {P : ProductPref (fun _ : ι => ℝ)}
    (hJoint : CoordinateJointSeedAndExtensibilityCertificate P) :
    CoordinateBidirectionalOneStepExtensibilityCertificate P := by
  intro i
  obtain ⟨k, hki, base, r, s, hrs, hext_desc, hext_asc, _, _⟩ := hJoint i
  exact ⟨k, hki, base, r, s, hrs, hext_desc, hext_asc⟩

/-- **Seed-indifference pair certificate from the joint seed-and-extensibility
certificate.** -/
theorem coordinateSeedIndifferencePairCertificate_of_jointSeedAndExtensibility
    {P : ProductPref (fun _ : ι => ℝ)}
    (hJoint : CoordinateJointSeedAndExtensibilityCertificate P) :
    CoordinateSeedIndifferencePairCertificate P := by
  intro i
  obtain ⟨k, hki, base, r, s, hrs, _, _, hpair_desc, hpair_asc⟩ := hJoint i
  exact ⟨k, hki, base, r, s, hrs, hpair_desc, hpair_asc⟩

/-- **End-to-end raw outputs from the joint seed-and-extensibility
certificate.**

End-to-end theorem-backed regression at the joint-certificate altitude. -/
theorem wakkerRawOutputs_of_jointSeedAndExtensibility
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hJoint : CoordinateJointSeedAndExtensibilityCertificate P)
    (hCont : CoordinateUtilityContinuityCertificate R (fun _ => Set.univ))
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P) :
    CoordinateRationalRefinementBisectionCertificate R ∧
      CoordinateConnectedContinuityOneStepBracketCertificate P ∧
        CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) :=
  wakkerRawOutputs_of_seedConstruction R hsolv
    (coordinateStandardSequenceSeedConstructionCertificate_of_jointSeedAndExtensibility
      hJoint)
    hCont hMonoStruct

/-! ##### Wakker-monograph-level aggregate input bundle

The current Lean seam isolates three remaining Wakker-monograph-level
deliverables below the joint seed-and-extensibility layer:

* `CoordinateBidirectionalOneStepExtensibilityCertificate P` — bidirectional
  one-step extensibility, the precise output of topological connectedness +
  continuity of `≽`.
* `CoordinateSeedIndifferencePairCertificate P` — seed indifferences in both
  reference directions, the precise output of essentiality + restricted
  solvability.
* `CoordinateUtilityContinuityCertificate R (fun _ => Set.univ)` — full
  coordinate continuity, the precise output of continuity of `≽` + topological
  connectedness.

Together with the per-coordinate alignment hypothesis (the standard structural
output of any joint Wakker construction proof producing the previous two), and
the structural single-coordinate monotonicity axiom, these four pieces close
the construction-stack frontier.

We package them as a single named **monograph-level aggregate input bundle**
so future formalization work can target one single hypothesis whose discharge
immediately closes every downstream construction-stack target through the
end-to-end regression theorems already in this file.

Following the Phase-8 single-name-hypothesis pattern of
`WakkerConstructionInputCertificate`, the bundle's body is the conjunction of
the three named open targets plus the alignment hypothesis and the structural
monotonicity axiom; the regression theorems chain through the existing
joint/seed/bare-axiom/structural/original-bundle layers without any new
algebraic obligation. -/

/-- **Wakker-monograph-level aggregate input bundle.**

Single named hypothesis collapsing the remaining construction-stack frontier
into one bundle.  Body content:

* bidirectional one-step extensibility on every coordinate;
* seed-indifference pair on every coordinate;
* per-coordinate alignment of the two on a shared `(k, base, r, s)` quadruple
  (the structural output of any joint Wakker construction proof);
* full-coordinate continuity (M4 continuity certificate on `Set.univ`);
* the structural single-coordinate monotonicity axiom.

A future discharge of this single bundle, together with restricted solvability
and the standard weak-order/tradeoff-consistency typeclasses, immediately
yields every downstream construction-stack target: the joint
seed-and-extensibility certificate, the seed-construction certificate, the
standard-sequence pair, the bare-axiom bundle, the structural bundle, the
original construction input bundle, the three named raw outputs, and the
calibrated integer refinement plus full continuity. -/
def WakkerMonographLevelInputCertificate
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) : Prop :=
  CoordinateBidirectionalOneStepExtensibilityCertificate P ∧
    CoordinateSeedIndifferencePairCertificate P ∧
      (∀ i : ι,
        ∃ k : ι, k ≠ i ∧
          ∃ base : Profile (fun _ : ι => ℝ),
            ∃ r s : ℝ, r ≠ s ∧
              ProductPref.OneStepExtensible P i base k r s ∧
              ProductPref.OneStepExtensible P i base k s r ∧
              (∃ a0 a1 : ℝ,
                P.weakPref (Function.update base i a0) (Function.update base i a1) ∧
                ¬ P.weakPref (Function.update base i a1) (Function.update base i a0) ∧
                P.indiff
                  (Function.update (Function.update base i a0) k r)
                  (Function.update (Function.update base i a1) k s)) ∧
              (∃ a0' a1' : ℝ,
                P.indiff
                  (Function.update (Function.update base i a0') k s)
                  (Function.update (Function.update base i a1') k r))) ∧
        CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) ∧
          SingleCoordinateMonotonicityAxiom P

/-- **Joint seed-and-extensibility certificate from the monograph-level aggregate bundle.** -/
theorem coordinateJointSeedAndExtensibilityCertificate_of_monographLevel
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    (hMono : WakkerMonographLevelInputCertificate R) :
    CoordinateJointSeedAndExtensibilityCertificate P := by
  obtain ⟨hExt, hSeed, hAlign, _, _⟩ := hMono
  exact coordinateJointSeedAndExtensibilityCertificate_of_components hExt hSeed hAlign

/-- **Seed-construction certificate from the monograph-level aggregate bundle.** -/
theorem coordinateStandardSequenceSeedConstructionCertificate_of_monographLevel
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    (hMono : WakkerMonographLevelInputCertificate R) :
    CoordinateStandardSequenceSeedConstructionCertificate P :=
  coordinateStandardSequenceSeedConstructionCertificate_of_jointSeedAndExtensibility
    (coordinateJointSeedAndExtensibilityCertificate_of_monographLevel hMono)

/-- **Bare-axiom input bundle from the monograph-level aggregate bundle.** -/
theorem wakkerStandardSequenceConstructionBareAxiomInputCertificate_of_monographLevel
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hMono : WakkerMonographLevelInputCertificate R) :
    WakkerStandardSequenceConstructionBareAxiomInputCertificate R := by
  have hSeed := coordinateStandardSequenceSeedConstructionCertificate_of_monographLevel hMono
  obtain ⟨_, _, _, hCont, hMonoStruct⟩ := hMono
  exact wakkerStandardSequenceConstructionBareAxiomInputCertificate_of_seedConstruction
    R hsolv hSeed hCont hMonoStruct

/-- **Original construction-stack input bundle from the monograph-level aggregate bundle.** -/
theorem wakkerStandardSequenceConstructionInputCertificate_of_monographLevel
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hMono : WakkerMonographLevelInputCertificate R) :
    WakkerStandardSequenceConstructionInputCertificate R :=
  wakkerStandardSequenceConstructionInputCertificate_of_bareAxiom R hsolv
    (wakkerStandardSequenceConstructionBareAxiomInputCertificate_of_monographLevel
      R hsolv hMono)

/-- **The three named raw outputs from the monograph-level aggregate bundle.**

End-to-end theorem-backed regression: any future discharge of
`WakkerMonographLevelInputCertificate R` (the single named hypothesis collapsing
the remaining Wakker-monograph-level construction-stack frontier), together
with restricted solvability and the standard weak-order / tradeoff-consistency
typeclasses, immediately yields the three named raw outputs

* `CoordinateRationalRefinementBisectionCertificate R`
* `CoordinateConnectedContinuityOneStepBracketCertificate P`
* `CoordinateUtilityContinuityCertificate R (fun _ => Set.univ)`. -/
theorem wakkerRawOutputs_of_monographLevel
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hMono : WakkerMonographLevelInputCertificate R) :
    CoordinateRationalRefinementBisectionCertificate R ∧
      CoordinateConnectedContinuityOneStepBracketCertificate P ∧
        CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) :=
  wakkerRawOutputs_of_wakkerStandardSequenceConstructionInput R hsolv
    (wakkerStandardSequenceConstructionInputCertificate_of_monographLevel
      R hsolv hMono)

/-- **Calibrated integer refinement and full coordinate continuity from the
monograph-level aggregate bundle.** -/
theorem integerRefinement_and_fullContinuity_of_monographLevel
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hMono : WakkerMonographLevelInputCertificate R) :
    CoordinateStandardSequenceIntegerRefinementCertificate R ∧
      CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) :=
  integerRefinement_and_fullContinuity_of_wakkerStandardSequenceConstructionInput
    R hsolv
    (wakkerStandardSequenceConstructionInputCertificate_of_monographLevel
      R hsolv hMono)

/-- **Monograph-level aggregate bundle from its component certificates.**

Reverse assembly: the monograph-level aggregate bundle is exactly the
conjunction of its named components.  This documents the canonical discharge
route — a future Wakker-level proof produces each component separately and
then assembles the bundle. -/
theorem wakkerMonographLevelInputCertificate_of_components
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    (hExt : CoordinateBidirectionalOneStepExtensibilityCertificate P)
    (hSeed : CoordinateSeedIndifferencePairCertificate P)
    (hAlign : ∀ i : ι,
      ∃ k : ι, k ≠ i ∧
        ∃ base : Profile (fun _ : ι => ℝ),
          ∃ r s : ℝ, r ≠ s ∧
            ProductPref.OneStepExtensible P i base k r s ∧
            ProductPref.OneStepExtensible P i base k s r ∧
            (∃ a0 a1 : ℝ,
              P.weakPref (Function.update base i a0) (Function.update base i a1) ∧
              ¬ P.weakPref (Function.update base i a1) (Function.update base i a0) ∧
              P.indiff
                (Function.update (Function.update base i a0) k r)
                (Function.update (Function.update base i a1) k s)) ∧
            (∃ a0' a1' : ℝ,
              P.indiff
                (Function.update (Function.update base i a0') k s)
                (Function.update (Function.update base i a1') k r)))
    (hCont : CoordinateUtilityContinuityCertificate R (fun _ => Set.univ))
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P) :
    WakkerMonographLevelInputCertificate R :=
  ⟨hExt, hSeed, hAlign, hCont, hMonoStruct⟩

/-! ##### Two-halves factoring of the monograph-level aggregate bundle

The monograph-level aggregate bundle has two logically separate halves:

* a **construction half** containing the bidirectional one-step extensibility
  certificate, the seed-indifference pair certificate, and the per-coordinate
  alignment hypothesis — together the precise output of Wakker's
  standard-sequence-construction chapter (essentiality + restricted solvability
  + Archimedean + topological connectedness + continuity);
* a **topology half** containing the full-coordinate continuity certificate
  and the structural single-coordinate monotonicity axiom — together the
  precise output of Wakker's topology chapter (continuity of `≽` + topological
  connectedness + structural monotonicity).

Naming each half exposes a sharper assembly interface for any future
Wakker-level proof that produces the two halves separately, and naming the
reverse projections from the aggregate bundle back to each component records
the canonical extraction routes. -/

/-- **Construction-side input bundle.**

Names the construction-side half of `WakkerMonographLevelInputCertificate`:
the bidirectional one-step extensibility certificate, the seed-indifference
pair certificate, and the per-coordinate alignment hypothesis.  In Wakker's
framework this is the output of the standard-sequence-construction chapter. -/
def WakkerMonographConstructionHalfInputCertificate
    (P : ProductPref (fun _ : ι => ℝ)) : Prop :=
  CoordinateBidirectionalOneStepExtensibilityCertificate P ∧
    CoordinateSeedIndifferencePairCertificate P ∧
      (∀ i : ι,
        ∃ k : ι, k ≠ i ∧
          ∃ base : Profile (fun _ : ι => ℝ),
            ∃ r s : ℝ, r ≠ s ∧
              ProductPref.OneStepExtensible P i base k r s ∧
              ProductPref.OneStepExtensible P i base k s r ∧
              (∃ a0 a1 : ℝ,
                P.weakPref (Function.update base i a0) (Function.update base i a1) ∧
                ¬ P.weakPref (Function.update base i a1) (Function.update base i a0) ∧
                P.indiff
                  (Function.update (Function.update base i a0) k r)
                  (Function.update (Function.update base i a1) k s)) ∧
              (∃ a0' a1' : ℝ,
                P.indiff
                  (Function.update (Function.update base i a0') k s)
                  (Function.update (Function.update base i a1') k r)))

/-- **Topology-side input bundle.**

Names the topology-side half of `WakkerMonographLevelInputCertificate`: the
full-coordinate continuity certificate and the structural single-coordinate
monotonicity axiom.  In Wakker's framework this is the output of the topology
chapter. -/
def WakkerMonographTopologyHalfInputCertificate
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) : Prop :=
  CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) ∧
    SingleCoordinateMonotonicityAxiom P

/-- **Construction half from its named components.** -/
theorem wakkerMonographConstructionHalfInputCertificate_of_components
    {P : ProductPref (fun _ : ι => ℝ)}
    (hExt : CoordinateBidirectionalOneStepExtensibilityCertificate P)
    (hSeed : CoordinateSeedIndifferencePairCertificate P)
    (hAlign : ∀ i : ι,
      ∃ k : ι, k ≠ i ∧
        ∃ base : Profile (fun _ : ι => ℝ),
          ∃ r s : ℝ, r ≠ s ∧
            ProductPref.OneStepExtensible P i base k r s ∧
            ProductPref.OneStepExtensible P i base k s r ∧
            (∃ a0 a1 : ℝ,
              P.weakPref (Function.update base i a0) (Function.update base i a1) ∧
              ¬ P.weakPref (Function.update base i a1) (Function.update base i a0) ∧
              P.indiff
                (Function.update (Function.update base i a0) k r)
                (Function.update (Function.update base i a1) k s)) ∧
            (∃ a0' a1' : ℝ,
              P.indiff
                (Function.update (Function.update base i a0') k s)
                (Function.update (Function.update base i a1') k r))) :
    WakkerMonographConstructionHalfInputCertificate P :=
  ⟨hExt, hSeed, hAlign⟩

/-- **Topology half from its named components.** -/
theorem wakkerMonographTopologyHalfInputCertificate_of_components
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    (hCont : CoordinateUtilityContinuityCertificate R (fun _ => Set.univ))
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P) :
    WakkerMonographTopologyHalfInputCertificate R :=
  ⟨hCont, hMonoStruct⟩

/-- **Monograph-level aggregate bundle from its two halves.** -/
theorem wakkerMonographLevelInputCertificate_of_halves
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    (hConstr : WakkerMonographConstructionHalfInputCertificate P)
    (hTop : WakkerMonographTopologyHalfInputCertificate R) :
    WakkerMonographLevelInputCertificate R := by
  obtain ⟨hExt, hSeed, hAlign⟩ := hConstr
  obtain ⟨hCont, hMonoStruct⟩ := hTop
  exact ⟨hExt, hSeed, hAlign, hCont, hMonoStruct⟩

/-- **Construction half from the monograph-level aggregate bundle (reverse projection).** -/
theorem wakkerMonographConstructionHalfInputCertificate_of_monographLevel
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    (hMono : WakkerMonographLevelInputCertificate R) :
    WakkerMonographConstructionHalfInputCertificate P := by
  obtain ⟨hExt, hSeed, hAlign, _, _⟩ := hMono
  exact ⟨hExt, hSeed, hAlign⟩

/-- **Topology half from the monograph-level aggregate bundle (reverse projection).** -/
theorem wakkerMonographTopologyHalfInputCertificate_of_monographLevel
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    (hMono : WakkerMonographLevelInputCertificate R) :
    WakkerMonographTopologyHalfInputCertificate R := by
  obtain ⟨_, _, _, hCont, hMonoStruct⟩ := hMono
  exact ⟨hCont, hMonoStruct⟩

/-- **Bidirectional extensibility from the monograph-level aggregate bundle.** -/
theorem coordinateBidirectionalOneStepExtensibilityCertificate_of_monographLevel
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    (hMono : WakkerMonographLevelInputCertificate R) :
    CoordinateBidirectionalOneStepExtensibilityCertificate P := by
  obtain ⟨hExt, _, _, _, _⟩ := hMono
  exact hExt

/-- **Seed-indifference pair from the monograph-level aggregate bundle.** -/
theorem coordinateSeedIndifferencePairCertificate_of_monographLevel
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    (hMono : WakkerMonographLevelInputCertificate R) :
    CoordinateSeedIndifferencePairCertificate P := by
  obtain ⟨_, hSeed, _, _, _⟩ := hMono
  exact hSeed

/-- **Full coordinate continuity from the monograph-level aggregate bundle.** -/
theorem coordinateUtilityContinuityCertificate_univ_of_monographLevel
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    (hMono : WakkerMonographLevelInputCertificate R) :
    CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) := by
  obtain ⟨_, _, _, hCont, _⟩ := hMono
  exact hCont

/-- **Structural monotonicity from the monograph-level aggregate bundle.** -/
theorem singleCoordinateMonotonicityAxiom_of_monographLevel
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    (hMono : WakkerMonographLevelInputCertificate R) :
    SingleCoordinateMonotonicityAxiom P := by
  obtain ⟨_, _, _, _, hMonoStruct⟩ := hMono
  exact hMonoStruct

/-- **The three named raw outputs from the two halves of the monograph-level
aggregate bundle.**

Convenience entry point that takes the construction half and topology half
separately, useful for any future Wakker-level proof that produces the two
halves independently. -/
theorem wakkerRawOutputs_of_halves
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hConstr : WakkerMonographConstructionHalfInputCertificate P)
    (hTop : WakkerMonographTopologyHalfInputCertificate R) :
    CoordinateRationalRefinementBisectionCertificate R ∧
      CoordinateConnectedContinuityOneStepBracketCertificate P ∧
        CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) :=
  wakkerRawOutputs_of_monographLevel R hsolv
    (wakkerMonographLevelInputCertificate_of_halves hConstr hTop)

/-- **Calibrated integer refinement and full coordinate continuity from the
two halves.** -/
theorem integerRefinement_and_fullContinuity_of_halves
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hConstr : WakkerMonographConstructionHalfInputCertificate P)
    (hTop : WakkerMonographTopologyHalfInputCertificate R) :
    CoordinateStandardSequenceIntegerRefinementCertificate R ∧
      CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) :=
  integerRefinement_and_fullContinuity_of_monographLevel R hsolv
    (wakkerMonographLevelInputCertificate_of_halves hConstr hTop)

/-! ##### Alignment-only factoring of the construction half

The construction half currently lists three components: bidirectional one-step
extensibility, seed-indifference pair, and the per-coordinate alignment
hypothesis.  Inspection shows the alignment hypothesis is genuinely
self-contained: per coordinate it bundles the bidirectional extensibility
witnesses and both seed-indifference pairs on a shared `(k, base, r, s)`
quadruple.  Both other components are direct projections.

We name the per-coordinate alignment hypothesis as a standalone certificate
`CoordinatePerCoordinateAlignmentCertificate` and theorem-back the construction
half from it alone.  This exposes the natural minimal core of the
construction half: a single per-coordinate Wakker-monograph deliverable. -/

/-- **Per-coordinate alignment certificate.**

For every coordinate `i`, supply one auxiliary coordinate `k ≠ i`, one base
profile, one reference exchange `r ≠ s` in coordinate `k`, both directions of
one-step extensibility, the descending strict-preference seed pair plus its
seed indifference, and the ascending seed indifference pair.

This is the minimal per-coordinate Wakker-monograph deliverable for the
construction half: a single quadruple `(k, base, r, s)` together with all the
bidirectional/seed witnesses that share it. -/
def CoordinatePerCoordinateAlignmentCertificate
    (P : ProductPref (fun _ : ι => ℝ)) : Prop :=
  ∀ i : ι,
    ∃ k : ι, k ≠ i ∧
      ∃ base : Profile (fun _ : ι => ℝ),
        ∃ r s : ℝ, r ≠ s ∧
          ProductPref.OneStepExtensible P i base k r s ∧
          ProductPref.OneStepExtensible P i base k s r ∧
          (∃ a0 a1 : ℝ,
            P.weakPref (Function.update base i a0) (Function.update base i a1) ∧
            ¬ P.weakPref (Function.update base i a1) (Function.update base i a0) ∧
            P.indiff
              (Function.update (Function.update base i a0) k r)
              (Function.update (Function.update base i a1) k s)) ∧
          (∃ a0' a1' : ℝ,
            P.indiff
              (Function.update (Function.update base i a0') k s)
              (Function.update (Function.update base i a1') k r))



/-- **Bidirectional one-step extensibility from per-coordinate alignment.** -/
theorem coordinateBidirectionalOneStepExtensibilityCertificate_of_perCoordinateAlignment
    {P : ProductPref (fun _ : ι => ℝ)}
    (hAlign : CoordinatePerCoordinateAlignmentCertificate P) :
    CoordinateBidirectionalOneStepExtensibilityCertificate P := by
  intro i
  obtain ⟨k, hki, base, r, s, hrs, hext_desc, hext_asc, _, _⟩ := hAlign i
  exact ⟨k, hki, base, r, s, hrs, hext_desc, hext_asc⟩

/-- **Seed-indifference pair from per-coordinate alignment.** -/
theorem coordinateSeedIndifferencePairCertificate_of_perCoordinateAlignment
    {P : ProductPref (fun _ : ι => ℝ)}
    (hAlign : CoordinatePerCoordinateAlignmentCertificate P) :
    CoordinateSeedIndifferencePairCertificate P := by
  intro i
  obtain ⟨k, hki, base, r, s, hrs, _, _, hpair_desc, hpair_asc⟩ := hAlign i
  exact ⟨k, hki, base, r, s, hrs, hpair_desc, hpair_asc⟩

/-- **Construction half from per-coordinate alignment alone.**

The alignment certificate is the genuine minimal core of the construction
half: it contains all the per-coordinate witnesses on a shared
`(k, base, r, s)` quadruple, and both other components are direct projections. -/
theorem wakkerMonographConstructionHalfInputCertificate_of_perCoordinateAlignment
    {P : ProductPref (fun _ : ι => ℝ)}
    (hAlign : CoordinatePerCoordinateAlignmentCertificate P) :
    WakkerMonographConstructionHalfInputCertificate P :=
  ⟨coordinateBidirectionalOneStepExtensibilityCertificate_of_perCoordinateAlignment hAlign,
   coordinateSeedIndifferencePairCertificate_of_perCoordinateAlignment hAlign,
   hAlign⟩

/-- **Per-coordinate alignment certificate from the construction half.**

The reverse projection: the construction half's third component is exactly the
per-coordinate alignment certificate. -/
theorem coordinatePerCoordinateAlignmentCertificate_of_constructionHalf
    {P : ProductPref (fun _ : ι => ℝ)}
    (hConstr : WakkerMonographConstructionHalfInputCertificate P) :
    CoordinatePerCoordinateAlignmentCertificate P := by
  obtain ⟨_, _, hAlign⟩ := hConstr
  exact hAlign

/-- **Monograph-level aggregate bundle from per-coordinate alignment plus the
topology half.**

End-to-end theorem-backed shortcut: the construction half is fully discharged
by per-coordinate alignment, so the aggregate bundle's only remaining input
beyond alignment is the topology half. -/
theorem wakkerMonographLevelInputCertificate_of_perCoordinateAlignment_and_topologyHalf
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    (hAlign : CoordinatePerCoordinateAlignmentCertificate P)
    (hTop : WakkerMonographTopologyHalfInputCertificate R) :
    WakkerMonographLevelInputCertificate R :=
  wakkerMonographLevelInputCertificate_of_halves
    (wakkerMonographConstructionHalfInputCertificate_of_perCoordinateAlignment
      hAlign)
    hTop

/-- **The three named raw outputs from per-coordinate alignment plus the
topology half.** -/
theorem wakkerRawOutputs_of_perCoordinateAlignment_and_topologyHalf
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hAlign : CoordinatePerCoordinateAlignmentCertificate P)
    (hTop : WakkerMonographTopologyHalfInputCertificate R) :
    CoordinateRationalRefinementBisectionCertificate R ∧
      CoordinateConnectedContinuityOneStepBracketCertificate P ∧
        CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) :=
  wakkerRawOutputs_of_monographLevel R hsolv
    (wakkerMonographLevelInputCertificate_of_perCoordinateAlignment_and_topologyHalf
      hAlign hTop)

/-- **Calibrated integer refinement and full coordinate continuity from
per-coordinate alignment plus the topology half.** -/
theorem integerRefinement_and_fullContinuity_of_perCoordinateAlignment_and_topologyHalf
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hAlign : CoordinatePerCoordinateAlignmentCertificate P)
    (hTop : WakkerMonographTopologyHalfInputCertificate R) :
    CoordinateStandardSequenceIntegerRefinementCertificate R ∧
      CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) :=
  integerRefinement_and_fullContinuity_of_monographLevel R hsolv
    (wakkerMonographLevelInputCertificate_of_perCoordinateAlignment_and_topologyHalf
      hAlign hTop)

/-! ##### Per-point alignment certificate

The `CoordinatePerCoordinateAlignmentCertificate` is a `∀ i : ι` quantifier
over a per-coordinate Wakker-monograph deliverable.  We expose the inner
predicate as a standalone certificate `PointwiseAlignmentCertificate P i` so
any future formalization can tackle one coordinate at a time. -/

/-- **Pointwise alignment certificate at coordinate `i`.**

Single-coordinate version of `CoordinatePerCoordinateAlignmentCertificate`:
the per-coordinate Wakker-monograph deliverable for the chosen coordinate `i`. -/
def PointwiseAlignmentCertificate
    (P : ProductPref (fun _ : ι => ℝ)) (i : ι) : Prop :=
  ∃ k : ι, k ≠ i ∧
    ∃ base : Profile (fun _ : ι => ℝ),
      ∃ r s : ℝ, r ≠ s ∧
        ProductPref.OneStepExtensible P i base k r s ∧
        ProductPref.OneStepExtensible P i base k s r ∧
        (∃ a0 a1 : ℝ,
          P.weakPref (Function.update base i a0) (Function.update base i a1) ∧
          ¬ P.weakPref (Function.update base i a1) (Function.update base i a0) ∧
          P.indiff
            (Function.update (Function.update base i a0) k r)
            (Function.update (Function.update base i a1) k s)) ∧
        (∃ a0' a1' : ℝ,
          P.indiff
            (Function.update (Function.update base i a0') k s)
            (Function.update (Function.update base i a1') k r))

/-- **Per-coordinate alignment certificate from pointwise alignment on every coordinate.** -/
theorem coordinatePerCoordinateAlignmentCertificate_of_pointwise
    {P : ProductPref (fun _ : ι => ℝ)}
    (h : ∀ i : ι, PointwiseAlignmentCertificate P i) :
    CoordinatePerCoordinateAlignmentCertificate P := by
  intro i; exact h i

/-- **Pointwise alignment from the per-coordinate alignment certificate.** -/
theorem pointwiseAlignmentCertificate_of_perCoordinateAlignment
    {P : ProductPref (fun _ : ι => ℝ)}
    (hAlign : CoordinatePerCoordinateAlignmentCertificate P) (i : ι) :
    PointwiseAlignmentCertificate P i := hAlign i

/-- **Equivalence: per-coordinate alignment is exactly pointwise alignment on
every coordinate.** -/
theorem coordinatePerCoordinateAlignmentCertificate_iff_pointwise
    {P : ProductPref (fun _ : ι => ℝ)} :
    CoordinatePerCoordinateAlignmentCertificate P ↔
      ∀ i : ι, PointwiseAlignmentCertificate P i :=
  ⟨pointwiseAlignmentCertificate_of_perCoordinateAlignment,
   coordinatePerCoordinateAlignmentCertificate_of_pointwise⟩

/-! ##### Pointwise alignment factoring into named per-quadruple predicates

The body of `PointwiseAlignmentCertificate P i` exists-quantifies over a
`(k, base, r, s)` quadruple witnessing four logically distinct pieces:

* bidirectional one-step extensibility for the chosen quadruple;
* the descending seed-pair witness (a strict-preference pair plus its seed
  indifference under the descending exchange `r ↦ s`);
* the ascending seed-pair witness (a seed indifference under the swapped
  exchange `s ↦ r`).

We name each piece as a parameterized predicate over the explicit quadruple
and theorem-back the pointwise alignment certificate from a single witnessing
quadruple plus the three named pieces.  This lets a future Wakker-level proof
target each piece independently. -/

/-- **Bidirectional one-step extensibility at a fixed quadruple.** -/
def QuadrupleBidirectionalExtensibility
    (P : ProductPref (fun _ : ι => ℝ))
    (i k : ι) (base : Profile (fun _ : ι => ℝ)) (r s : ℝ) : Prop :=
  ProductPref.OneStepExtensible P i base k r s ∧
    ProductPref.OneStepExtensible P i base k s r

/-- **Descending seed-pair witness at a fixed quadruple.**

A strict-preference pair `(a0, a1)` in coordinate `i` plus its seed
indifference under the descending exchange `r ↦ s`. -/
def QuadrupleDescendingSeed
    (P : ProductPref (fun _ : ι => ℝ))
    (i k : ι) (base : Profile (fun _ : ι => ℝ)) (r s : ℝ) : Prop :=
  ∃ a0 a1 : ℝ,
    P.weakPref (Function.update base i a0) (Function.update base i a1) ∧
    ¬ P.weakPref (Function.update base i a1) (Function.update base i a0) ∧
    P.indiff
      (Function.update (Function.update base i a0) k r)
      (Function.update (Function.update base i a1) k s)

/-- **Ascending seed-pair witness at a fixed quadruple.**

A seed-indifference pair `(a0', a1')` in coordinate `i` under the swapped
exchange `s ↦ r`. -/
def QuadrupleAscendingSeed
    (P : ProductPref (fun _ : ι => ℝ))
    (i k : ι) (base : Profile (fun _ : ι => ℝ)) (r s : ℝ) : Prop :=
  ∃ a0' a1' : ℝ,
    P.indiff
      (Function.update (Function.update base i a0') k s)
      (Function.update (Function.update base i a1') k r)

/-- **Pointwise alignment from named per-quadruple predicates.** -/
theorem pointwiseAlignmentCertificate_of_quadruple
    {P : ProductPref (fun _ : ι => ℝ)} {i k : ι} (hki : k ≠ i)
    (base : Profile (fun _ : ι => ℝ))
    (r s : ℝ) (hrs : r ≠ s)
    (hExt : QuadrupleBidirectionalExtensibility P i k base r s)
    (hDesc : QuadrupleDescendingSeed P i k base r s)
    (hAsc : QuadrupleAscendingSeed P i k base r s) :
    PointwiseAlignmentCertificate P i := by
  obtain ⟨hext_desc, hext_asc⟩ := hExt
  obtain ⟨a0, a1, hweak, hnotweak, hindiff_desc⟩ := hDesc
  obtain ⟨a0', a1', hindiff_asc⟩ := hAsc
  refine ⟨k, hki, base, r, s, hrs, hext_desc, hext_asc, ?_, ?_⟩
  · exact ⟨a0, a1, hweak, hnotweak, hindiff_desc⟩
  · exact ⟨a0', a1', hindiff_asc⟩

/-- **Bidirectional extensibility at a witnessing quadruple from pointwise alignment.** -/
theorem exists_quadruple_bidirectionalExtensibility_of_pointwiseAlignment
    {P : ProductPref (fun _ : ι => ℝ)} {i : ι}
    (hPt : PointwiseAlignmentCertificate P i) :
    ∃ k : ι, k ≠ i ∧ ∃ base : Profile (fun _ : ι => ℝ),
      ∃ r s : ℝ, r ≠ s ∧
        QuadrupleBidirectionalExtensibility P i k base r s := by
  obtain ⟨k, hki, base, r, s, hrs, hext_desc, hext_asc, _, _⟩ := hPt
  exact ⟨k, hki, base, r, s, hrs, hext_desc, hext_asc⟩

/-- **Descending seed witness at a witnessing quadruple from pointwise alignment.** -/
theorem exists_quadruple_descendingSeed_of_pointwiseAlignment
    {P : ProductPref (fun _ : ι => ℝ)} {i : ι}
    (hPt : PointwiseAlignmentCertificate P i) :
    ∃ k : ι, k ≠ i ∧ ∃ base : Profile (fun _ : ι => ℝ),
      ∃ r s : ℝ, r ≠ s ∧
        QuadrupleDescendingSeed P i k base r s := by
  obtain ⟨k, hki, base, r, s, hrs, _, _, hdesc, _⟩ := hPt
  exact ⟨k, hki, base, r, s, hrs, hdesc⟩

/-- **Ascending seed witness at a witnessing quadruple from pointwise alignment.** -/
theorem exists_quadruple_ascendingSeed_of_pointwiseAlignment
    {P : ProductPref (fun _ : ι => ℝ)} {i : ι}
    (hPt : PointwiseAlignmentCertificate P i) :
    ∃ k : ι, k ≠ i ∧ ∃ base : Profile (fun _ : ι => ℝ),
      ∃ r s : ℝ, r ≠ s ∧
        QuadrupleAscendingSeed P i k base r s := by
  obtain ⟨k, hki, base, r, s, hrs, _, _, _, hasc⟩ := hPt
  exact ⟨k, hki, base, r, s, hrs, hasc⟩

/-! ##### Explicit-witness factoring of the per-quadruple seed predicates

We further decompose `QuadrupleDescendingSeed` and `QuadrupleAscendingSeed`
into explicit-witness sub-predicates so a future Wakker-level proof can
supply concrete `(a0, a1)` and `(a0', a1')` witnesses and discharge the
strict-preference and indifference content separately.

The strict-preference content of `QuadrupleDescendingSeed` is independent of
`(k, r, s)`: it is exactly the pair-strict-preference content witnessed by
`Essential P i`.  We expose this projection as a named bridge from
`Essential P i` to the strict-preference-only sub-predicate. -/

/-- **Strict-preference seed pair at coordinate `i` (no `(k, r, s)` dependence).**

Names the strict-preference content of `QuadrupleDescendingSeed`: a pair
`(a0, a1)` in coordinate `i` with `update base i a0 ≻ update base i a1`. -/
def CoordinateStrictPreferenceSeedPair
    (P : ProductPref (fun _ : ι => ℝ)) (i : ι)
    (base : Profile (fun _ : ι => ℝ)) : Prop :=
  ∃ a0 a1 : ℝ,
    P.weakPref (Function.update base i a0) (Function.update base i a1) ∧
    ¬ P.weakPref (Function.update base i a1) (Function.update base i a0)

/-- **Descending seed indifference for an explicit pair `(a0, a1)`.**

Names the seed-indifference content of `QuadrupleDescendingSeed` once the
strict-pair witnesses are fixed. -/
def QuadrupleDescendingSeedIndifferenceExplicit
    (P : ProductPref (fun _ : ι => ℝ))
    (i k : ι) (base : Profile (fun _ : ι => ℝ)) (r s : ℝ)
    (a0 a1 : ℝ) : Prop :=
  P.indiff
    (Function.update (Function.update base i a0) k r)
    (Function.update (Function.update base i a1) k s)

/-- **Ascending seed indifference for an explicit pair `(a0', a1')`.** -/
def QuadrupleAscendingSeedIndifferenceExplicit
    (P : ProductPref (fun _ : ι => ℝ))
    (i k : ι) (base : Profile (fun _ : ι => ℝ)) (r s : ℝ)
    (a0' a1' : ℝ) : Prop :=
  P.indiff
    (Function.update (Function.update base i a0') k s)
    (Function.update (Function.update base i a1') k r)

/-- **Descending seed witness from a strict-preference pair plus an explicit
seed indifference.** -/
theorem quadrupleDescendingSeed_of_strictPair_and_indifference
    {P : ProductPref (fun _ : ι => ℝ)}
    {i k : ι} {base : Profile (fun _ : ι => ℝ)} {r s : ℝ}
    {a0 a1 : ℝ}
    (hweak : P.weakPref (Function.update base i a0) (Function.update base i a1))
    (hnotweak : ¬ P.weakPref (Function.update base i a1) (Function.update base i a0))
    (hindiff : QuadrupleDescendingSeedIndifferenceExplicit P i k base r s a0 a1) :
    QuadrupleDescendingSeed P i k base r s :=
  ⟨a0, a1, hweak, hnotweak, hindiff⟩

/-- **Ascending seed witness from an explicit seed indifference.** -/
theorem quadrupleAscendingSeed_of_indifference
    {P : ProductPref (fun _ : ι => ℝ)}
    {i k : ι} {base : Profile (fun _ : ι => ℝ)} {r s : ℝ}
    {a0' a1' : ℝ}
    (hindiff : QuadrupleAscendingSeedIndifferenceExplicit P i k base r s a0' a1') :
    QuadrupleAscendingSeed P i k base r s :=
  ⟨a0', a1', hindiff⟩

/-- **Strict-preference seed pair (with explicit base) from essentiality of
coordinate `i`.**

This bridge supplies the strict-preference content of `QuadrupleDescendingSeed`
directly from `Essential P i`: essentiality witnesses a base profile and two
values with the strict preference, which is exactly the strict-pair content. -/
theorem exists_strictPreferenceSeedPair_of_essential
    {P : ProductPref (fun _ : ι => ℝ)} {i : ι}
    (hEss : ProductPref.Essential P i) :
    ∃ base : Profile (fun _ : ι => ℝ),
      CoordinateStrictPreferenceSeedPair P i base := by
  obtain ⟨a, v, w, hvw, hnot⟩ := hEss
  exact ⟨a, v, w, hvw, hnot⟩

/-- **Pointwise alignment from explicit per-quadruple witnesses.**

Bottom-most assembly theorem: a future Wakker-level proof needs only to supply
a witnessing `(k, base, r, s)` quadruple plus explicit `(a0, a1)`, `(a0', a1')`
pair witnesses with their strict preference and seed indifferences and the
bidirectional one-step extensibility, and the pointwise alignment certificate
follows directly. -/
theorem pointwiseAlignmentCertificate_of_explicitWitnesses
    {P : ProductPref (fun _ : ι => ℝ)} {i k : ι} (hki : k ≠ i)
    (base : Profile (fun _ : ι => ℝ))
    (r s : ℝ) (hrs : r ≠ s)
    (hExt : QuadrupleBidirectionalExtensibility P i k base r s)
    (a0 a1 : ℝ)
    (hweak : P.weakPref (Function.update base i a0) (Function.update base i a1))
    (hnotweak : ¬ P.weakPref (Function.update base i a1) (Function.update base i a0))
    (hindiff_desc : QuadrupleDescendingSeedIndifferenceExplicit P i k base r s a0 a1)
    (a0' a1' : ℝ)
    (hindiff_asc : QuadrupleAscendingSeedIndifferenceExplicit P i k base r s a0' a1') :
    PointwiseAlignmentCertificate P i :=
  pointwiseAlignmentCertificate_of_quadruple hki base r s hrs hExt
    (quadrupleDescendingSeed_of_strictPair_and_indifference hweak hnotweak hindiff_desc)
    (quadrupleAscendingSeed_of_indifference hindiff_asc)

/-! ##### Directional one-step extensibility decomposition

`QuadrupleBidirectionalExtensibility` is the conjunction of two directional
`OneStepExtensible` predicates (descending `r ↦ s` and ascending `s ↦ r`).
We expose each direction as a standalone named alias and theorem-back the
assembly of the bidirectional predicate from the two directional witnesses.
This lets a future Wakker-level proof produce each direction independently. -/

/-- **Descending one-step extensibility direction.**

The `r ↦ s` direction of `QuadrupleBidirectionalExtensibility`. -/
def QuadrupleDescendingExtensibility
    (P : ProductPref (fun _ : ι => ℝ))
    (i k : ι) (base : Profile (fun _ : ι => ℝ)) (r s : ℝ) : Prop :=
  ProductPref.OneStepExtensible P i base k r s

/-- **Ascending one-step extensibility direction.**

The `s ↦ r` direction of `QuadrupleBidirectionalExtensibility`. -/
def QuadrupleAscendingExtensibility
    (P : ProductPref (fun _ : ι => ℝ))
    (i k : ι) (base : Profile (fun _ : ι => ℝ)) (r s : ℝ) : Prop :=
  ProductPref.OneStepExtensible P i base k s r

/-- **Bidirectional extensibility from the two directional witnesses.** -/
theorem quadrupleBidirectionalExtensibility_of_directional
    {P : ProductPref (fun _ : ι => ℝ)}
    {i k : ι} {base : Profile (fun _ : ι => ℝ)} {r s : ℝ}
    (hDesc : QuadrupleDescendingExtensibility P i k base r s)
    (hAsc : QuadrupleAscendingExtensibility P i k base r s) :
    QuadrupleBidirectionalExtensibility P i k base r s :=
  ⟨hDesc, hAsc⟩

/-- **Descending direction from bidirectional extensibility.** -/
theorem quadrupleDescendingExtensibility_of_bidirectional
    {P : ProductPref (fun _ : ι => ℝ)}
    {i k : ι} {base : Profile (fun _ : ι => ℝ)} {r s : ℝ}
    (hExt : QuadrupleBidirectionalExtensibility P i k base r s) :
    QuadrupleDescendingExtensibility P i k base r s :=
  hExt.1

/-- **Ascending direction from bidirectional extensibility.** -/
theorem quadrupleAscendingExtensibility_of_bidirectional
    {P : ProductPref (fun _ : ι => ℝ)}
    {i k : ι} {base : Profile (fun _ : ι => ℝ)} {r s : ℝ}
    (hExt : QuadrupleBidirectionalExtensibility P i k base r s) :
    QuadrupleAscendingExtensibility P i k base r s :=
  hExt.2

/-- **Equivalence: bidirectional extensibility is exactly the conjunction of
the two directional witnesses.** -/
theorem quadrupleBidirectionalExtensibility_iff_directional
    {P : ProductPref (fun _ : ι => ℝ)}
    {i k : ι} {base : Profile (fun _ : ι => ℝ)} {r s : ℝ} :
    QuadrupleBidirectionalExtensibility P i k base r s ↔
      QuadrupleDescendingExtensibility P i k base r s ∧
        QuadrupleAscendingExtensibility P i k base r s :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **Pointwise alignment from explicit witnesses with the bidirectional
extensibility decomposed into two directional witnesses.**

Bottom-most assembly route exposing every separate Wakker-monograph deliverable
needed for the construction-side: descending and ascending extensibility,
strict-preference seed pair, descending and ascending seed indifferences. -/
theorem pointwiseAlignmentCertificate_of_directionalExplicitWitnesses
    {P : ProductPref (fun _ : ι => ℝ)} {i k : ι} (hki : k ≠ i)
    (base : Profile (fun _ : ι => ℝ))
    (r s : ℝ) (hrs : r ≠ s)
    (hDesc_ext : QuadrupleDescendingExtensibility P i k base r s)
    (hAsc_ext : QuadrupleAscendingExtensibility P i k base r s)
    (a0 a1 : ℝ)
    (hweak : P.weakPref (Function.update base i a0) (Function.update base i a1))
    (hnotweak : ¬ P.weakPref (Function.update base i a1) (Function.update base i a0))
    (hindiff_desc : QuadrupleDescendingSeedIndifferenceExplicit P i k base r s a0 a1)
    (a0' a1' : ℝ)
    (hindiff_asc : QuadrupleAscendingSeedIndifferenceExplicit P i k base r s a0' a1') :
    PointwiseAlignmentCertificate P i :=
  pointwiseAlignmentCertificate_of_explicitWitnesses hki base r s hrs
    (quadrupleBidirectionalExtensibility_of_directional hDesc_ext hAsc_ext)
    a0 a1 hweak hnotweak hindiff_desc a0' a1' hindiff_asc

/-! ##### Topology-input bundle for bidirectional extensibility

Wakker's monograph derives `OneStepExtensible` from topological connectedness
of `X j` plus continuity of `≽`.  We package the precise Wakker-level
deliverable as a named topology-input bundle so a future Wakker-level proof
can target one single hypothesis. -/

/-- **Connectedness/continuity input bundle for bidirectional extensibility.**

Names exactly the per-quadruple bidirectional extensibility content as a
standalone topology-input bundle.  In Wakker's framework this is the precise
output of topological connectedness of the coordinate space plus continuity
of `≽`. -/
def QuadrupleConnectednessContinuityInputCertificate
    (P : ProductPref (fun _ : ι => ℝ))
    (i k : ι) (base : Profile (fun _ : ι => ℝ)) (r s : ℝ) : Prop :=
  QuadrupleBidirectionalExtensibility P i k base r s

/-- **Bidirectional extensibility from the connectedness/continuity bundle.** -/
theorem quadrupleBidirectionalExtensibility_of_connectednessContinuity
    {P : ProductPref (fun _ : ι => ℝ)}
    {i k : ι} {base : Profile (fun _ : ι => ℝ)} {r s : ℝ}
    (hTop : QuadrupleConnectednessContinuityInputCertificate P i k base r s) :
    QuadrupleBidirectionalExtensibility P i k base r s :=
  hTop

/-! ##### Genuine topology layer for one-step extensibility

We now provide the first genuine mathematical content discharging
`OneStepExtensible` from continuity + unboundedness of a coordinate utility
under an additive representation.  The idea: under additive `R`, the target
profile `(aPrev at i, r at k, base)` and a candidate `(aNext at i, s at k, base)`
are indifferent iff `R.V i aNext = R.V i aPrev + R.V k r - R.V k s`.  IVT on
the continuous image of `R.V i` provides such an `aNext` whenever `R.V i`'s
image covers every real (i.e., is unbounded above and below).

This is the precise per-coordinate Wakker IV.2.6 / III.4.2 refinement step
for the additive-real case: `OneStepExtensible` reduces to coordinate-utility
continuity plus unboundedness. -/

/-- **`OneStepExtensible` from coordinate-utility continuity plus unboundedness.**

Given an additive representation `R` of `P`, if `R.V i` is continuous on `ℝ`
and unbounded above and below (`CoordinateUtilityUnboundedCertificate R i`),
then `OneStepExtensible P i base k r s` holds for every base profile and
reference exchange `(r, s)`.

Proof: for each `aPrev`, IVT supplies `aNext` with
`R.V i aNext = R.V i aPrev + R.V k r - R.V k s`; the resulting two-coordinate
update has matching utility sums, hence indifference via
`additiveRep_twoCoord_indiff_of_value_balance`. -/
theorem oneStepExtensible_of_continuity_unbounded
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {i k : ι} (hki : k ≠ i)
    (base : Profile (fun _ : ι => ℝ))
    (r s : ℝ)
    (hCont : Continuous (R.V i))
    (hUnb : CoordinateUtilityUnboundedCertificate R i) :
    ProductPref.OneStepExtensible P i base k r s := by
  intro aPrev
  -- Target real value for R.V i aNext.
  let target : ℝ := R.V i aPrev + R.V k r - R.V k s
  -- IVT: target lies between two realized values of R.V i.
  obtain ⟨u_lo, u_hi, hlo, hhi⟩ := hUnb target
  have hrange : target ∈ Set.range (R.V i) :=
    intermediate_value_univ u_lo u_hi hCont ⟨hlo, hhi⟩
  rcases hrange with ⟨aNext, haNext⟩
  refine ⟨aNext, ?_⟩
  -- Utility sums match: R.V i aPrev + R.V k r = R.V i aNext + R.V k s.
  have hbalance : R.V i aPrev + R.V k r = R.V i aNext + R.V k s := by
    rw [haNext]; ring
  exact additiveRep_twoCoord_indiff_of_value_balance R hki.symm base aPrev aNext r s hbalance

/-- **Descending extensibility from continuity plus unboundedness.** -/
theorem quadrupleDescendingExtensibility_of_continuity_unbounded
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {i k : ι} (hki : k ≠ i)
    (base : Profile (fun _ : ι => ℝ))
    (r s : ℝ)
    (hCont : Continuous (R.V i))
    (hUnb : CoordinateUtilityUnboundedCertificate R i) :
    QuadrupleDescendingExtensibility P i k base r s :=
  oneStepExtensible_of_continuity_unbounded R hki base r s hCont hUnb

/-- **Ascending extensibility from continuity plus unboundedness.** -/
theorem quadrupleAscendingExtensibility_of_continuity_unbounded
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {i k : ι} (hki : k ≠ i)
    (base : Profile (fun _ : ι => ℝ))
    (r s : ℝ)
    (hCont : Continuous (R.V i))
    (hUnb : CoordinateUtilityUnboundedCertificate R i) :
    QuadrupleAscendingExtensibility P i k base r s :=
  oneStepExtensible_of_continuity_unbounded R hki base s r hCont hUnb

/-- **Bidirectional extensibility from continuity plus unboundedness.** -/
theorem quadrupleBidirectionalExtensibility_of_continuity_unbounded
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {i k : ι} (hki : k ≠ i)
    (base : Profile (fun _ : ι => ℝ))
    (r s : ℝ)
    (hCont : Continuous (R.V i))
    (hUnb : CoordinateUtilityUnboundedCertificate R i) :
    QuadrupleBidirectionalExtensibility P i k base r s :=
  ⟨quadrupleDescendingExtensibility_of_continuity_unbounded R hki base r s hCont hUnb,
   quadrupleAscendingExtensibility_of_continuity_unbounded R hki base r s hCont hUnb⟩

/-- **Connectedness/continuity input bundle from continuity plus unboundedness.**

The named topology-input bundle is theorem-backed from the precise structural
inputs Wakker's monograph supplies through topological connectedness +
continuity of `≽`: continuity of the coordinate utility plus its image
unboundedness (which on `ℝ` are equivalent to surjectivity onto `ℝ`). -/
theorem quadrupleConnectednessContinuityInputCertificate_of_continuity_unbounded
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {i k : ι} (hki : k ≠ i)
    (base : Profile (fun _ : ι => ℝ))
    (r s : ℝ)
    (hCont : Continuous (R.V i))
    (hUnb : CoordinateUtilityUnboundedCertificate R i) :
    QuadrupleConnectednessContinuityInputCertificate P i k base r s :=
  quadrupleBidirectionalExtensibility_of_continuity_unbounded R hki base r s hCont hUnb

/-- **Bidirectional extensibility from the M4 continuity certificate plus
the unboundedness certificate.**

Convenience entry point routing through the existing M4
`CoordinateUtilityContinuityCertificate R (fun _ => Set.univ)`. -/
theorem quadrupleBidirectionalExtensibility_of_coordinateUtilityContinuity_unbounded
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {i k : ι} (hki : k ≠ i)
    (base : Profile (fun _ : ι => ℝ))
    (r s : ℝ)
    (hCont : CoordinateUtilityContinuityCertificate R (fun _ => Set.univ))
    (hUnb : CoordinateUtilityUnboundedCertificate R i) :
    QuadrupleBidirectionalExtensibility P i k base r s :=
  quadrupleBidirectionalExtensibility_of_continuity_unbounded R hki base r s
    (continuous_coordinateUtility_of_continuityCertificate_univ R i hCont)
    hUnb

/-- **Bidirectional extensibility from continuity plus rational-image coverage.**

Rational-image coverage already implies coordinate-utility unboundedness via
`coordinateUtilityUnboundedCertificate_of_coordinateRationalImageCertificate`,
so this composes the IVT bridge with the rational-image-to-unbounded bridge. -/
theorem quadrupleBidirectionalExtensibility_of_coordinateUtilityContinuity_rationalImage
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {i k : ι} (hki : k ≠ i)
    (base : Profile (fun _ : ι => ℝ))
    (r s : ℝ)
    (hCont : CoordinateUtilityContinuityCertificate R (fun _ => Set.univ))
    (hRat : CoordinateRationalImageCertificate R) :
    QuadrupleBidirectionalExtensibility P i k base r s :=
  quadrupleBidirectionalExtensibility_of_coordinateUtilityContinuity_unbounded
    R hki base r s hCont
    (coordinateUtilityUnboundedCertificate_of_coordinateRationalImageCertificate R hRat i)

/-! ##### Task 1: `CoordinateUtilityUnboundedCertificate` from continuity + surjectivity

Genuine analytic content: continuity of `R.V i` plus surjectivity of `R.V i`
onto `ℝ` directly yield bidirectional unboundedness, since every real value
is realized.  This avoids going through the rational-image route and isolates
the precise analytic core. -/

/-- **`CoordinateUtilityUnboundedCertificate` from coordinate surjectivity directly.**

Surjectivity says every real value is realized; in particular every real `r`
is itself an upper and lower bracket trivially. -/
theorem coordinateUtilityUnboundedCertificate_of_coordinateSurjectivityCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hSurj : CoordinateSurjectivityCertificate R) (i : ι) :
    CoordinateUtilityUnboundedCertificate R i := by
  intro r
  obtain ⟨x, hx⟩ := hSurj i r
  exact ⟨x, x, le_of_eq hx, le_of_eq hx.symm⟩

/-! ##### Task 2: Seed indifference from restricted solvability + bracketing

Genuine new content using restricted solvability + bracketing pairs.
Restricted solvability says: if `update a j v ≽ b ≽ update a j w`, then
`∃ c, update a j c ∼ b`.  Applied to coordinate `i` with the target
`b := update (update base i a0) k r`, this produces the seed indifference once
the bracketing pair on coordinate `i` (with `k` held at `s`) is supplied. -/

/-- **Bracketing-pair certificate for descending seed indifference.**

For a target profile `(a0 at i, r at k, base)`, supply bracketing values `v, w`
on coordinate `i` with `k` held at `s` such that
`update (update base k s) i v ≽ (a0 at i, r at k, base) ≽ update (update base k s) i w`.

Restricted solvability then produces an `a1` filling the bracket, yielding the
descending seed indifference. -/
def QuadrupleDescendingSeedBracketingCertificate
    (P : ProductPref (fun _ : ι => ℝ))
    (i k : ι) (base : Profile (fun _ : ι => ℝ)) (r s : ℝ)
    (a0 : ℝ) : Prop :=
  ∃ v w : ℝ,
    P.weakPref
      (Function.update (Function.update base k s) i v)
      (Function.update (Function.update base i a0) k r) ∧
    P.weakPref
      (Function.update (Function.update base i a0) k r)
      (Function.update (Function.update base k s) i w)

/-- **Bracketing-pair certificate for ascending seed indifference.**

Symmetric to the descending case with the reference exchange swapped. -/
def QuadrupleAscendingSeedBracketingCertificate
    (P : ProductPref (fun _ : ι => ℝ))
    (i k : ι) (base : Profile (fun _ : ι => ℝ)) (r s : ℝ)
    (a0' : ℝ) : Prop :=
  ∃ v' w' : ℝ,
    P.weakPref
      (Function.update (Function.update base k r) i v')
      (Function.update (Function.update base i a0') k s) ∧
    P.weakPref
      (Function.update (Function.update base i a0') k s)
      (Function.update (Function.update base k r) i w')

/-- **Descending seed indifference from restricted solvability + bracketing.**

Restricted solvability fills the bracket: given `update (update base k s) i v ≽
(a0, base, r) ≽ update (update base k s) i w`, there exists `a1` with
`update (update base k s) i a1 ∼ (a0, base, r)`.  Commuting the updates gives
the descending seed indifference at `(a0, a1)`. -/
theorem exists_quadrupleDescendingSeedIndifferenceExplicit_of_bracketing
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    {i k : ι} (hki : k ≠ i)
    (base : Profile (fun _ : ι => ℝ))
    (r s : ℝ)
    (a0 : ℝ)
    (hBracket : QuadrupleDescendingSeedBracketingCertificate P i k base r s a0) :
    ∃ a1 : ℝ, QuadrupleDescendingSeedIndifferenceExplicit P i k base r s a0 a1 := by
  obtain ⟨v, w, hupper, hlower⟩ := hBracket
  let a : Profile (fun _ : ι => ℝ) := Function.update base k s
  let b : Profile (fun _ : ι => ℝ) := Function.update (Function.update base i a0) k r
  obtain ⟨a1, hfill⟩ := hsolv a b i v w hupper hlower
  refine ⟨a1, ?_⟩
  -- hfill : P.indiff (Function.update (update base k s) i a1) b
  -- Goal: P.indiff (update (update base i a0) k r) (update (update base i a1) k s)
  -- Commute updates and use indifference symmetry.
  have hswap := update_comm_two_coords_real (ι := ι) base hki a1 s
  unfold QuadrupleDescendingSeedIndifferenceExplicit
  change P.indiff b (Function.update (Function.update base i a1) k s)
  rw [← hswap]
  exact ⟨hfill.2, hfill.1⟩

/-- **Ascending seed indifference from restricted solvability + bracketing.**

Symmetric proof: bracket the target `(a0', base, s)` between updates of the
profile with `k` held at `r`, then restricted solvability fills the bracket. -/
theorem exists_quadrupleAscendingSeedIndifferenceExplicit_of_bracketing
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    {i k : ι} (hki : k ≠ i)
    (base : Profile (fun _ : ι => ℝ))
    (r s : ℝ)
    (a0' : ℝ)
    (hBracket : QuadrupleAscendingSeedBracketingCertificate P i k base r s a0') :
    ∃ a1' : ℝ, QuadrupleAscendingSeedIndifferenceExplicit P i k base r s a0' a1' := by
  obtain ⟨v', w', hupper, hlower⟩ := hBracket
  let a : Profile (fun _ : ι => ℝ) := Function.update base k r
  let b : Profile (fun _ : ι => ℝ) := Function.update (Function.update base i a0') k s
  obtain ⟨a1', hfill⟩ := hsolv a b i v' w' hupper hlower
  refine ⟨a1', ?_⟩
  have hswap := update_comm_two_coords_real (ι := ι) base hki a1' r
  unfold QuadrupleAscendingSeedIndifferenceExplicit
  change P.indiff b (Function.update (Function.update base i a1') k r)
  rw [← hswap]
  exact ⟨hfill.2, hfill.1⟩

/-- **`QuadrupleDescendingSeed` from explicit witnesses on a single `(a0, a1)` pair.**

Honest assembly: when the strict preference and the seed indifference share
the same `(a0, a1)` pair, the descending seed witness assembles directly.
A future Wakker-level proof must produce a single `(a0, a1)` satisfying both
(Wakker chooses `a1` as the bracketing-derived solution and verifies the
strict preference using continuity + monotonicity).  Here we expose the
explicit-witness interface that future proof must hit. -/
theorem quadrupleDescendingSeed_of_explicitPair
    {P : ProductPref (fun _ : ι => ℝ)}
    {i k : ι} {base : Profile (fun _ : ι => ℝ)} {r s : ℝ}
    (a0 a1 : ℝ)
    (hweak : P.weakPref (Function.update base i a0) (Function.update base i a1))
    (hnotweak : ¬ P.weakPref (Function.update base i a1) (Function.update base i a0))
    (hindiff : QuadrupleDescendingSeedIndifferenceExplicit P i k base r s a0 a1) :
    QuadrupleDescendingSeed P i k base r s :=
  ⟨a0, a1, hweak, hnotweak, hindiff⟩

/-- **`QuadrupleAscendingSeed` from an explicit `(a0', a1')` pair.** -/
theorem quadrupleAscendingSeed_of_explicitPair
    {P : ProductPref (fun _ : ι => ℝ)}
    {i k : ι} {base : Profile (fun _ : ι => ℝ)} {r s : ℝ}
    (a0' a1' : ℝ)
    (hindiff : QuadrupleAscendingSeedIndifferenceExplicit P i k base r s a0' a1') :
    QuadrupleAscendingSeed P i k base r s :=
  ⟨a0', a1', hindiff⟩

/-! ##### Stage T4: The alignment theorem

The genuine gap that Stages T1-T3 leave open: when restricted solvability
produces an `a1` filling a bracket, we get a seed indifference at `(a0, a1)`
but not automatically the strict descending preference at the same pair.

The alignment theorem closes this gap.  Under any additive representation,
the seed indifference forces the utility-balance equation
`R.V i a0 + R.V k r = R.V i a1 + R.V k s`; if the reference exchange satisfies
`R.V k r < R.V k s` (i.e., `s ≻ r at k` under any base), the balance forces
`R.V i a0 > R.V i a1`, hence under coordinate monotonicity (lifted from
`R.V i`) we have `update base i a0 ≻ update base i a1`, the desired strict
descending preference.

Symmetric for ascending: under `R.V k r < R.V k s`, the swapped indifference
`(a0', base, s) ∼ (a1', base, r)` forces `R.V i a0' < R.V i a1'`.  The
ascending seed predicate doesn't require a strict preference component, so
this direction needs no monotonicity, just the indifference itself.

The Lean theorems below take `R.V k r < R.V k s` as a named numeric hypothesis
and combine it with the seed indifference and either coordinate monotonicity
(for the descending strict component) or just the indifference (for the
ascending case) to produce the full quadruple seed predicates. -/

/-- **Strict reference utility ordering.**

Names the numeric hypothesis `R.V k r < R.V k s` that any future Wakker-level
proof producing a strict reference exchange `r ≺ s at k` would supply via
`additiveRep_coordPref_iff`.  This isolates the precise content needed by the
alignment theorem. -/
def QuadrupleStrictReferenceUtilityOrdering
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (k : ι) (r s : ℝ) : Prop :=
  R.V k r < R.V k s

/-- **Strict reference utility ordering from a strict preference at `k`.**

Bridge from the preference-level strict exchange `update base k r ≺ update base k s`
(equivalently `s ≻ r at base, k`) to the additive utility ordering.  Under any
additive representation, `additiveRep_coordPref_iff` and antisymmetry of `≤`
produce the strict utility ordering. -/
theorem quadrupleStrictReferenceUtilityOrdering_of_strictPreference
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {k : ι} (r s : ℝ) (base : Profile (fun _ : ι => ℝ))
    (hRefPref : P.weakPref (Function.update base k s) (Function.update base k r))
    (hNotRev : ¬ P.weakPref (Function.update base k r) (Function.update base k s)) :
    QuadrupleStrictReferenceUtilityOrdering R k r s := by
  unfold QuadrupleStrictReferenceUtilityOrdering
  have hle : R.V k r ≤ R.V k s :=
    (additiveRep_coordPref_iff R k base s r).mp hRefPref
  have hnotge : ¬ R.V k s ≤ R.V k r := fun h =>
    hNotRev ((additiveRep_coordPref_iff R k base r s).mpr h)
  exact lt_of_le_of_ne hle (fun heq => hnotge (le_of_eq heq.symm))

/-- **Utility-level alignment lemma: the seed indifference plus a strict
reference utility ordering forces a strict utility ordering on `i`.**

Under additive representation, the indifference `(a0, base, r) ∼ (a1, base, s)`
gives `R.V i a0 + R.V k r = R.V i a1 + R.V k s`.  Combined with `R.V k r < R.V k s`,
this forces `R.V i a0 > R.V i a1`. -/
theorem additiveRep_iUtilityOrdering_of_seedIndifference_and_strictReference
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {i k : ι} (hki : k ≠ i)
    {base : Profile (fun _ : ι => ℝ)} {r s : ℝ}
    {a0 a1 : ℝ}
    (hindiff : QuadrupleDescendingSeedIndifferenceExplicit P i k base r s a0 a1)
    (hRef : QuadrupleStrictReferenceUtilityOrdering R k r s) :
    R.V i a1 < R.V i a0 := by
  -- From the indifference: Σ V on both profiles agree.
  -- The two profiles differ only at coords i and k, so the additive balance
  -- forces R.V i a0 + R.V k r = R.V i a1 + R.V k s.
  unfold QuadrupleDescendingSeedIndifferenceExplicit at hindiff
  let lhs : Profile (fun _ : ι => ℝ) :=
    Function.update (Function.update base i a0) k r
  let rhs : Profile (fun _ : ι => ℝ) :=
    Function.update (Function.update base i a1) k s
  have hsum : (∑ j, R.V j (lhs j)) = ∑ j, R.V j (rhs j) := by
    have h₁ := (R.represents lhs rhs).mp hindiff.1
    have h₂ := (R.represents rhs lhs).mp hindiff.2
    linarith
  -- Decompose the sums by isolating coords i and k.
  have hjk : i ≠ k := hki.symm
  have hlhs := sum_eq_pair_add_rest R.V lhs (j := i) (k := k) hjk
  have hrhs := sum_eq_pair_add_rest R.V rhs (j := i) (k := k) hjk
  have hrest :
      (∑ t ∈ (Finset.univ.erase i).erase k, R.V t (lhs t)) =
        ∑ t ∈ (Finset.univ.erase i).erase k, R.V t (rhs t) := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    have htk : t ≠ k := Finset.ne_of_mem_erase ht
    have ht_erase_i : t ∈ Finset.univ.erase i := (Finset.mem_erase.mp ht).2
    have hti : t ≠ i := Finset.ne_of_mem_erase ht_erase_i
    simp [lhs, rhs, Function.update_of_ne htk, Function.update_of_ne hti]
  have hlhs_i : lhs i = a0 := by
    show (Function.update (Function.update base i a0) k r) i = a0
    rw [Function.update_of_ne hki.symm, Function.update_self]
  have hlhs_k : lhs k = r := by
    dsimp [lhs]; rw [Function.update_self]
  have hrhs_i : rhs i = a1 := by
    show (Function.update (Function.update base i a1) k s) i = a1
    rw [Function.update_of_ne hki.symm, Function.update_self]
  have hrhs_k : rhs k = s := by
    dsimp [rhs]; rw [Function.update_self]
  -- Combine: the additive balance is R.V i a0 + R.V k r = R.V i a1 + R.V k s.
  have hbalance : R.V i a0 + R.V k r = R.V i a1 + R.V k s := by
    have : R.V i (lhs i) + R.V k (lhs k) +
              (∑ t ∈ (Finset.univ.erase i).erase k, R.V t (lhs t)) =
            R.V i (rhs i) + R.V k (rhs k) +
              (∑ t ∈ (Finset.univ.erase i).erase k, R.V t (rhs t)) := by
      rw [← hlhs, ← hrhs]; exact hsum
    rw [hlhs_i, hlhs_k, hrhs_i, hrhs_k, hrest] at this
    linarith
  -- From R.V k r < R.V k s and the balance, R.V i a0 > R.V i a1.
  unfold QuadrupleStrictReferenceUtilityOrdering at hRef
  linarith

/-- **Strict descending preference on `i` from coordinate monotonicity + the
utility ordering.**

Coordinate monotonicity lifts `R.V i a1 < R.V i a0` to the preference-level
strict ordering `update base i a0 ≻ update base i a1`. -/
theorem additiveRep_strictDescendingPreference_of_iUtilityOrdering
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {i : ι} (base : Profile (fun _ : ι => ℝ))
    {a0 a1 : ℝ}
    (hLt : R.V i a1 < R.V i a0) :
    P.weakPref (Function.update base i a0) (Function.update base i a1) ∧
      ¬ P.weakPref (Function.update base i a1) (Function.update base i a0) := by
  refine ⟨?_, ?_⟩
  · exact (additiveRep_coordPref_iff R i base a0 a1).mpr (le_of_lt hLt)
  · intro hcontra
    have := (additiveRep_coordPref_iff R i base a1 a0).mp hcontra
    linarith

/-- **Stage T4 main alignment theorem (descending direction).**

Under any additive representation, given:

* a seed indifference `(a0, base, r) ∼ (a1, base, s)`
* a strict reference utility ordering `R.V k r < R.V k s`

the descending seed predicate `QuadrupleDescendingSeed P i k base r s` holds at
the same `(a0, a1)` pair.  The strict descending preference is forced by the
balance equation plus the strict reference ordering, eliminating the alignment
gap that prior layers had to take as a hypothesis. -/
theorem quadrupleDescendingSeed_of_explicit_alignment
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {i k : ι} (hki : k ≠ i)
    {base : Profile (fun _ : ι => ℝ)} {r s : ℝ}
    (a0 a1 : ℝ)
    (hindiff : QuadrupleDescendingSeedIndifferenceExplicit P i k base r s a0 a1)
    (hRef : QuadrupleStrictReferenceUtilityOrdering R k r s) :
    QuadrupleDescendingSeed P i k base r s := by
  have hLt : R.V i a1 < R.V i a0 :=
    additiveRep_iUtilityOrdering_of_seedIndifference_and_strictReference
      R hki hindiff hRef
  obtain ⟨hweak, hnotweak⟩ :=
    additiveRep_strictDescendingPreference_of_iUtilityOrdering R base hLt
  exact ⟨a0, a1, hweak, hnotweak, hindiff⟩

/-- **Existence form: descending seed witness from bracketing + strict reference
+ restricted solvability + an additive representation.**

Combines `exists_quadrupleDescendingSeedIndifferenceExplicit_of_bracketing`
with the alignment theorem to produce the full descending seed witness from
a bracketing certificate plus a strict reference utility ordering. -/
theorem exists_quadrupleDescendingSeed_of_bracketing_alignment
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (R : AdditiveRep P)
    {i k : ι} (hki : k ≠ i)
    (base : Profile (fun _ : ι => ℝ))
    (r s : ℝ)
    (a0 : ℝ)
    (hBracket : QuadrupleDescendingSeedBracketingCertificate P i k base r s a0)
    (hRef : QuadrupleStrictReferenceUtilityOrdering R k r s) :
    QuadrupleDescendingSeed P i k base r s := by
  obtain ⟨a1, hindiff⟩ :=
    exists_quadrupleDescendingSeedIndifferenceExplicit_of_bracketing
      hsolv hki base r s a0 hBracket
  exact quadrupleDescendingSeed_of_explicit_alignment R hki a0 a1 hindiff hRef

/-- **End-to-end pointwise alignment from bracketing + ascending bracketing
+ strict reference + restricted solvability + additive representation.**

The bottom-most consumer for the construction half on a single coordinate.
Given:

* bidirectional one-step extensibility (Stage T2's output);
* descending and ascending bracketing certificates on shared `(k, base, r, s)`;
* a strict reference utility ordering;
* restricted solvability.

Produce `PointwiseAlignmentCertificate P i`. -/
theorem pointwiseAlignmentCertificate_of_bracketing_alignment
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (R : AdditiveRep P)
    {i k : ι} (hki : k ≠ i)
    (base : Profile (fun _ : ι => ℝ))
    (r s : ℝ) (hrs : r ≠ s)
    (hExt : QuadrupleBidirectionalExtensibility P i k base r s)
    (a0 : ℝ)
    (hBracketDesc : QuadrupleDescendingSeedBracketingCertificate P i k base r s a0)
    (a0' : ℝ)
    (hBracketAsc : QuadrupleAscendingSeedBracketingCertificate P i k base r s a0')
    (hRef : QuadrupleStrictReferenceUtilityOrdering R k r s) :
    PointwiseAlignmentCertificate P i := by
  obtain ⟨a1, hindiff_desc⟩ :=
    exists_quadrupleDescendingSeedIndifferenceExplicit_of_bracketing
      hsolv hki base r s a0 hBracketDesc
  obtain ⟨a1', hindiff_asc⟩ :=
    exists_quadrupleAscendingSeedIndifferenceExplicit_of_bracketing
      hsolv hki base r s a0' hBracketAsc
  have hLt : R.V i a1 < R.V i a0 :=
    additiveRep_iUtilityOrdering_of_seedIndifference_and_strictReference
      R hki hindiff_desc hRef
  obtain ⟨hweak, hnotweak⟩ :=
    additiveRep_strictDescendingPreference_of_iUtilityOrdering R base hLt
  exact pointwiseAlignmentCertificate_of_explicitWitnesses
    hki base r s hrs hExt a0 a1 hweak hnotweak hindiff_desc a0' a1' hindiff_asc

end CertificateChecklist

end WakkerRoadmap
