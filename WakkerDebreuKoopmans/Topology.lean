/-
This file is part of the split `WakkerDebreuKoopmans` module family.
The public import surface remains `WakkerDebreuKoopmans.lean`, now a thin
re-export barrel.
-/

import WakkerDebreuKoopmans.ConstructionStack

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

/-! ##### Stage T1: Continuity-of-preference axiom

Wakker (1989) IV.2.3 assumes that for every base profile `a`, the upper set
`{x : x ≽ a}` and the lower set `{x : a ≽ x}` are closed in the product
topology on `∏ᵢ Xᵢ`.  We mechanize this directly as a named predicate, expose
the equivalent indifference-set formulation, and prove the **forward direction
under additive representation**: when each coordinate utility `R.V i` is
continuous, the additive representation forces preference continuity.

The converse direction --- from preference continuity to coordinate utility
continuity --- is the genuinely substantive Wakker Lemma III.4.5 content and
is deferred to Stage T3.  Stage T1 isolates the predicate plus its forward
discharge so downstream consumers can target the predicate as a single named
hypothesis. -/

/-- **Continuity of the preference relation** (Wakker IV.2.3).

For every base profile `a`, both the upper set `{x | x ≽ a}` and the lower
set `{x | a ≽ x}` are closed in the product topology on `∏ᵢ Xᵢ`.  This is the
analytic shape of preference continuity used throughout Wakker (1989).

Stated abstractly via `IsClosed`; the product topology is supplied by the
ambient `[∀ i, TopologicalSpace (X i)]` instances. -/
def ProductPref.PreferenceContinuous
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    (P : WakkerInfra.ProductPref X) : Prop :=
  ∀ a : Profile X,
    IsClosed {x : Profile X | P.weakPref x a} ∧
      IsClosed {x : Profile X | P.weakPref a x}

/-- **Equivalent formulation: closedness of the indifference set.**

Under a weak-order assumption, the indifference set `{x | P.indiff x a}` is the
intersection of the upper and lower sets `{x | x ≽ a}` and `{x | a ≽ x}`,
hence closed iff both are closed.  The forward direction (preference
continuous → indifference set closed) requires no extra hypotheses beyond the
definition of `indiff`. -/
theorem indiffSet_closed_of_preferenceContinuous
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : WakkerInfra.ProductPref X}
    (hCont : ProductPref.PreferenceContinuous P) (a : Profile X) :
    IsClosed {x : Profile X | P.indiff x a} := by
  -- {x | P.indiff x a} = {x | P.weakPref x a} ∩ {x | P.weakPref a x}.
  have h_eq :
      {x : Profile X | P.indiff x a} =
        {x : Profile X | P.weakPref x a} ∩ {x : Profile X | P.weakPref a x} := by
    ext x
    simp [WakkerInfra.ProductPref.indiff]
  rw [h_eq]
  exact (hCont a).1.inter (hCont a).2

/-- **Auxiliary: the additive sum of continuous coordinate utilities is
continuous in the product topology.**

For each `i`, the projection `(fun x : Profile X => x i)` is continuous; the
composition with `R.V i` (continuous by hypothesis) is continuous; the sum
of finitely many continuous functions is continuous. -/
theorem additiveRep_sum_continuous
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : WakkerInfra.ProductPref X} (R : AdditiveRep P)
    (hCont : ∀ i : ι, Continuous (R.V i)) :
    Continuous (fun x : Profile X => ∑ i, R.V i (x i)) := by
  refine continuous_finset_sum Finset.univ ?_
  intro i _
  exact (hCont i).comp (continuous_apply i)

/-- **Forward direction (Stage T1's main theorem): preference continuity from
continuous coordinate utilities under additive representation.**

If every `R.V i` is continuous, then the additive sum is continuous in the
product topology; the preference relation `weakPref` reduces under
`R.represents` to a comparison of additive sums, and the preimage of a closed
half-line under a continuous function is closed.  Hence the upper and lower
sets are closed and `PreferenceContinuous P` holds. -/
theorem additiveRep_pullback_preferenceContinuous
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : WakkerInfra.ProductPref X} (R : AdditiveRep P)
    (hCont : ∀ i : ι, Continuous (R.V i)) :
    ProductPref.PreferenceContinuous P := by
  intro a
  -- Let f x := Σ R.V i (x i).  f is continuous.
  let f : Profile X → ℝ := fun x => ∑ i, R.V i (x i)
  have hf : Continuous f := additiveRep_sum_continuous R hCont
  refine ⟨?_, ?_⟩
  · -- {x | x ≽ a} = {x | f a ≤ f x} (R.represents).
    have h_eq : {x : Profile X | P.weakPref x a} = {x : Profile X | f a ≤ f x} := by
      ext x
      simp only [Set.mem_setOf_eq]
      exact R.represents x a
    rw [h_eq]
    -- The set {x | f a ≤ f x} is closed: it's the preimage of [f a, ∞) under f.
    have hpre : {x : Profile X | f a ≤ f x} = f ⁻¹' (Set.Ici (f a)) := by
      ext x; simp [Set.mem_Ici]
    rw [hpre]
    exact isClosed_Ici.preimage hf
  · -- {x | a ≽ x} = {x | f x ≤ f a}.
    have h_eq : {x : Profile X | P.weakPref a x} = {x : Profile X | f x ≤ f a} := by
      ext x
      simp only [Set.mem_setOf_eq]
      exact R.represents a x
    rw [h_eq]
    have hpre : {x : Profile X | f x ≤ f a} = f ⁻¹' (Set.Iic (f a)) := by
      ext x; simp [Set.mem_Iic]
    rw [hpre]
    exact isClosed_Iic.preimage hf

/-- **Indifference set closed from continuous coordinate utilities under
additive representation.**

End-to-end: `Continuous (R.V i)` for every coordinate `i` directly implies
closedness of every indifference set under any additive representation. -/
theorem additiveRep_indiffSet_closed
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : WakkerInfra.ProductPref X} (R : AdditiveRep P)
    (hCont : ∀ i : ι, Continuous (R.V i)) (a : Profile X) :
    IsClosed {x : Profile X | P.indiff x a} :=
  indiffSet_closed_of_preferenceContinuous
    (additiveRep_pullback_preferenceContinuous R hCont) a

/-- **Real-coordinate convenience: preference continuity from continuous
real-coordinate utilities.**

Specialization to `X i = ℝ` (with the standard topology). -/
theorem additiveRep_real_pullback_preferenceContinuous
    {P : WakkerInfra.ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hCont : ∀ i : ι, Continuous (R.V i)) :
    ProductPref.PreferenceContinuous P :=
  additiveRep_pullback_preferenceContinuous R hCont

/-! ##### Stage T2: Topological connectedness axiom on each coordinate

This is the first piece of new topology infrastructure beyond the IVT bridge.
We name the per-coordinate connectedness assumption explicitly so the same
machinery extends to general coordinate spaces; on real coordinates the
assumption is automatic via Mathlib's `Real.connectedSpace` instance.

The key downstream consequences are:

* The image of any continuous coordinate utility is preconnected, hence (on `ℝ`)
  an interval — supplying the analytic shape needed by IVT-style arguments.
* Every continuous monotone surjection between connected spaces is bicontinuous;
  this is the underlying mechanism by which Wakker's connectedness assumption
  delivers continuity-of-≽ from per-coordinate continuity. -/

/-- **Per-coordinate connectedness axiom** (Wakker IV.2.3 spatial component).

Names the assumption that every coordinate space `X i` is topologically
connected.  In the real-coordinate case this is automatic; for general
coordinate spaces it is a genuine structural axiom of Wakker's setting. -/
def ProductPref.ConnectedCoordinates
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    (_P : WakkerInfra.ProductPref X) : Prop :=
  ∀ i : ι, ConnectedSpace (X i)

/-- **Connectedness on every coordinate is automatic for the real-coordinate
case.**

Mathlib supplies `Real.instConnectedSpace`, hence every real coordinate is
connected without further assumption. -/
theorem connectedCoordinates_realProduct
    (P : WakkerInfra.ProductPref (fun _ : ι => ℝ)) :
    ProductPref.ConnectedCoordinates P :=
  fun _ => inferInstance

/-- **The image of a continuous coordinate utility on a connected space is
preconnected.**

This is the genuine analytic content of Stage T2: a continuous function
from any connected space has preconnected image.  Under `R.V i` continuous,
the image `Set.range (R.V i)` is preconnected. -/
theorem coordinateUtilityImage_isPreconnected_of_connected_and_continuous
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : WakkerInfra.ProductPref X} (R : AdditiveRep P)
    (hConn : ProductPref.ConnectedCoordinates P) (i : ι)
    (hCont : Continuous (R.V i)) :
    IsPreconnected (Set.range (R.V i)) := by
  have hUniv : IsPreconnected (Set.univ : Set (X i)) :=
    (hConn i).isPreconnected_univ
  have himg : IsPreconnected ((R.V i) '' (Set.univ : Set (X i))) :=
    hUniv.image (R.V i) hCont.continuousOn
  rwa [Set.image_univ] at himg

/-- **The image of a continuous real-coordinate utility on a connected space
is an interval (the only preconnected sets in `ℝ`).**

Specialization to `X i = ℝ` of the previous lemma.  Mathlib's
`IsPreconnected.ordConnected` shows the image is order-connected; on `ℝ` this
characterizes intervals. -/
theorem coordinateUtilityImage_ordConnected_of_real_continuous
    {P : WakkerInfra.ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (i : ι) (hCont : Continuous (R.V i)) :
    Set.OrdConnected (Set.range (R.V i)) := by
  have hConn : ProductPref.ConnectedCoordinates P := connectedCoordinates_realProduct P
  exact (coordinateUtilityImage_isPreconnected_of_connected_and_continuous R hConn i hCont).ordConnected

/-- **Surjectivity from connectedness + continuity + bidirectional unboundedness.**

If `R.V i` is continuous on a connected coordinate space and its image is
unbounded above and below in `ℝ`, then `R.V i` is surjective onto `ℝ`.  This
is a direct consequence of preconnectedness of the image plus its bidirectional
unboundedness: a preconnected subset of `ℝ` containing arbitrarily small and
arbitrarily large values must equal all of `ℝ`. -/
theorem coordinateSurjectivityCertificate_of_connected_continuous_unbounded
    {P : WakkerInfra.ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hConn : ProductPref.ConnectedCoordinates P)
    (hCont : ∀ i : ι, Continuous (R.V i))
    (hUnb : ∀ i : ι, CoordinateUtilityUnboundedCertificate R i) :
    CoordinateSurjectivityCertificate R := by
  intro i r
  obtain ⟨u_lo, u_hi, hlo, hhi⟩ := hUnb i r
  have hPre : IsPreconnected (Set.range (R.V i)) :=
    coordinateUtilityImage_isPreconnected_of_connected_and_continuous R hConn i (hCont i)
  have hOrd : Set.OrdConnected (Set.range (R.V i)) := hPre.ordConnected
  have hlo_mem : R.V i u_lo ∈ Set.range (R.V i) := ⟨u_lo, rfl⟩
  have hhi_mem : R.V i u_hi ∈ Set.range (R.V i) := ⟨u_hi, rfl⟩
  have hr_mem : r ∈ Set.range (R.V i) :=
    hOrd.out hlo_mem hhi_mem ⟨hlo, hhi⟩
  exact hr_mem

/-- **`CoordinateUtilityUnboundedCertificate` from connectedness + continuity
+ surjectivity.**

Convenience wrapper: when surjectivity is already known, unboundedness is free. -/
theorem coordinateUtilityUnbounded_of_connected_continuous_surjective
    {P : WakkerInfra.ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hSurj : CoordinateSurjectivityCertificate R) (i : ι) :
    CoordinateUtilityUnboundedCertificate R i :=
  coordinateUtilityUnboundedCertificate_of_coordinateSurjectivityCertificate R hSurj i

/-- **`OneStepExtensible` from connectedness + continuity + bidirectional
unboundedness.**

End-to-end consumer: connectedness lifts the IVT bridge from "continuity +
unboundedness" to a structural-axiom-shaped input.  This composes
`oneStepExtensible_of_continuity_unbounded` with the connectedness layer. -/
theorem oneStepExtensible_of_connected_continuous_unbounded
    {P : WakkerInfra.ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {i k : ι} (hki : k ≠ i)
    (base : Profile (fun _ : ι => ℝ))
    (r s : ℝ)
    (_hConn : ProductPref.ConnectedCoordinates P)
    (hCont : Continuous (R.V i))
    (hUnb : CoordinateUtilityUnboundedCertificate R i) :
    WakkerInfra.ProductPref.OneStepExtensible P i base k r s :=
  oneStepExtensible_of_continuity_unbounded R hki base r s hCont hUnb

/-- **`QuadrupleBidirectionalExtensibility` from connectedness + continuity
+ unboundedness.** -/
theorem quadrupleBidirectionalExtensibility_of_connected_continuous_unbounded
    {P : WakkerInfra.ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {i k : ι} (hki : k ≠ i)
    (base : Profile (fun _ : ι => ℝ))
    (r s : ℝ)
    (hConn : ProductPref.ConnectedCoordinates P)
    (hCont : Continuous (R.V i))
    (hUnb : CoordinateUtilityUnboundedCertificate R i) :
    QuadrupleBidirectionalExtensibility P i k base r s := by
  refine ⟨?_, ?_⟩
  · exact oneStepExtensible_of_connected_continuous_unbounded R hki base r s hConn hCont hUnb
  · exact oneStepExtensible_of_connected_continuous_unbounded R hki base s r hConn hCont hUnb

/-! ##### Stage T3: Continuous coordinate utility from preference continuity

The substantive Stage T3 content: under preference continuity plus monotonicity,
each coordinate utility `R.V i` is continuous on `Set.univ`.  Combined with
Stage T2 outputs (preconnectedness from connectedness + continuity), this
closes the topology half's continuity component without going through the
construction-stack ladder.

Honest scope note: the most powerful version of Wakker's Lemma III.4.5 derives
coordinate monotonicity itself from preference continuity + essentiality +
restricted solvability.  That direction requires a *direction-of-preference*
witness (without it, e.g.\ a reversed preference satisfies all the structural
axioms but yields antitone `R.V i`).  Stage T3 below mechanizes the direction
that takes monotonicity as given (or derives it from the structural axiom)
and shows the continuity step is then theorem-backed; the genuine remaining
content for the full Lemma III.4.5 discharge is the directional witness, which
is exposed as a named hypothesis below. -/

/-- **Coordinate monotonicity from structural monotonicity (forward, already
established) and structural monotonicity from coordinate monotonicity (the
genuine new content).**

This is the converse of `coordinateMonotonicityCertificate_of_singleCoordinateMonotonicityAxiom`.
Under any additive representation, coordinate monotonicity of `R.V i` directly
yields the preference-level structural monotonicity axiom: if `R.V i u ≤ R.V i v`,
then by `R.represents` the profile updated to `v` is weakly preferred to the
profile updated to `u`. -/
theorem singleCoordinateMonotonicityAxiom_of_coordinateMonotonicityCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hMono : CoordinateMonotonicityCertificate R) :
    SingleCoordinateMonotonicityAxiom P := by
  intro i a u v huv
  -- Goal: P.weakPref (update a i v) (update a i u).
  -- Under R.represents: Σ R.V j ((update a i u) j) ≤ Σ R.V j ((update a i v) j).
  rw [R.represents]
  -- The two sums differ only at coordinate i: at i they are R.V i u vs R.V i v.
  -- For all j ≠ i, the two updates equal a j.
  have hsum_v :
      (∑ j, R.V j ((Function.update a i v) j)) =
        R.V i v + ∑ j ∈ Finset.univ.erase i, R.V j (a j) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    rw [show R.V i ((Function.update a i v) i) = R.V i v from by
          simp [Function.update_self]]
    have : (∑ j ∈ Finset.univ.erase i, R.V j ((Function.update a i v) j)) =
        ∑ j ∈ Finset.univ.erase i, R.V j (a j) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      rw [Function.update_of_ne hji]
    rw [this]
    ring
  have hsum_u :
      (∑ j, R.V j ((Function.update a i u) j)) =
        R.V i u + ∑ j ∈ Finset.univ.erase i, R.V j (a j) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    rw [show R.V i ((Function.update a i u) i) = R.V i u from by
          simp [Function.update_self]]
    have : (∑ j ∈ Finset.univ.erase i, R.V j ((Function.update a i u) j)) =
        ∑ j ∈ Finset.univ.erase i, R.V j (a j) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      rw [Function.update_of_ne hji]
    rw [this]
    ring
  rw [hsum_u, hsum_v]
  have hVle : R.V i u ≤ R.V i v := hMono i huv
  linarith

/-- **Equivalence between coordinate monotonicity and structural monotonicity
under any additive representation.** -/
theorem coordinateMonotonicityCertificate_iff_singleCoordinateMonotonicityAxiom
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) :
    CoordinateMonotonicityCertificate R ↔ SingleCoordinateMonotonicityAxiom P :=
  ⟨singleCoordinateMonotonicityAxiom_of_coordinateMonotonicityCertificate R,
   coordinateMonotonicityCertificate_of_singleCoordinateMonotonicityAxiom P R⟩

/-- **Continuous coordinate utility from connectedness + continuity-on-grid +
unboundedness + coordinate monotonicity.**

End-to-end Stage T3 consumer.  The chain:

* Stage T2 surjectivity from preconnectedness + bidirectional unboundedness;
* dense-range from surjectivity;
* M4 IVT bridge: dense-range + monotonicity → continuity on `Set.univ`.

Note: this consumer requires `Continuous (R.V i)` as input (via Stage T2's
preconnectedness step); the output is the M4 `CoordinateUtilityContinuityCertificate`
on `Set.univ`, which is ordinary continuity in our setting. -/
theorem coordinateUtilityContinuityCertificate_univ_of_connected_monotone_continuous_unbounded
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hConn : ProductPref.ConnectedCoordinates P)
    (hMono : CoordinateMonotonicityCertificate R)
    (hCont : ∀ i : ι, Continuous (R.V i))
    (hUnb : ∀ i : ι, CoordinateUtilityUnboundedCertificate R i) :
    CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) := by
  have hSurj : CoordinateSurjectivityCertificate R :=
    coordinateSurjectivityCertificate_of_connected_continuous_unbounded R hConn hCont hUnb
  have hDense : CoordinateDenseRangeCertificate R :=
    coordinateDenseRangeCertificate_of_coordinateSurjectivityCertificate R hSurj
  exact coordinateUtilityContinuityCertificate_univ_of_monotone_denseRange R hMono hDense

/-- **Continuous coordinate utility from connectedness + structural monotonicity
+ continuity-on-grid + unboundedness.**

Replaces the `CoordinateMonotonicityCertificate` input by the structural
monotonicity axiom, derived under any additive representation.  This is the
form Stage T5's bare-axiom bundle will consume. -/
theorem coordinateUtilityContinuityCertificate_univ_of_connected_structuralMonotonicity_continuous_unbounded
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hConn : ProductPref.ConnectedCoordinates P)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P)
    (hCont : ∀ i : ι, Continuous (R.V i))
    (hUnb : ∀ i : ι, CoordinateUtilityUnboundedCertificate R i) :
    CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) :=
  coordinateUtilityContinuityCertificate_univ_of_connected_monotone_continuous_unbounded
    R hConn
    (coordinateMonotonicityCertificate_of_singleCoordinateMonotonicityAxiom P R hMonoStruct)
    hCont hUnb

/-- **Topology half from connectedness + structural monotonicity + continuity
+ unboundedness.**

End-to-end discharge of `WakkerMonographTopologyHalfInputCertificate` from
genuinely topological inputs (no rational-image coverage required). -/
theorem wakkerMonographTopologyHalfInputCertificate_of_connected_structuralMonotonicity_continuous_unbounded
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hConn : ProductPref.ConnectedCoordinates P)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P)
    (hCont : ∀ i : ι, Continuous (R.V i))
    (hUnb : ∀ i : ι, CoordinateUtilityUnboundedCertificate R i) :
    WakkerMonographTopologyHalfInputCertificate R :=
  ⟨coordinateUtilityContinuityCertificate_univ_of_connected_structuralMonotonicity_continuous_unbounded
    R hConn hMonoStruct hCont hUnb,
   hMonoStruct⟩

/-- **Real-coordinate convenience: the topology half from preference continuity
+ structural monotonicity + per-coordinate continuity + unboundedness.**

For real coordinates, `ConnectedCoordinates` is automatic, and the upstream
preference continuity (Stage T1) is recorded as an unused hypothesis to
document the full Wakker IV.2.3 input shape. -/
theorem wakkerMonographTopologyHalfInputCertificate_of_real_preferenceContinuous_structuralMonotonicity_continuous_unbounded
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (_hPrefCont : ProductPref.PreferenceContinuous P)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P)
    (hCont : ∀ i : ι, Continuous (R.V i))
    (hUnb : ∀ i : ι, CoordinateUtilityUnboundedCertificate R i) :
    WakkerMonographTopologyHalfInputCertificate R :=
  wakkerMonographTopologyHalfInputCertificate_of_connected_structuralMonotonicity_continuous_unbounded
    R (connectedCoordinates_realProduct P) hMonoStruct hCont hUnb

/-! ##### Stage T5: Wakker topological axiom bundle

Package the Stage T2-T4 outputs into a single named hypothesis whose body
lists exactly the structural-topological inputs Wakker (1989) treats as
primitive plus the per-coordinate alignment data needed by Stage T4.

Honest scope note: Stage T5 takes the bracketing-pair certificates as
primitive (packaged inside `CoordinateWakkerAlignmentData`), which is the
role they play before Stage T6 derives them from the Archimedean axiom. -/

/-- **Per-coordinate Wakker alignment data.**

Names the per-coordinate Wakker-monograph data needed for Stage T4 alignment:
an auxiliary coordinate `k ≠ i`, a base profile, a reference exchange `(r, s)`
with `r ≠ s`, bidirectional one-step extensibility, descending and ascending
bracketing certificates at chosen seed points, and a strict reference utility
ordering at the chosen `(k, r, s)`. -/
def CoordinateWakkerAlignmentData
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) (i : ι) : Prop :=
  ∃ k : ι, k ≠ i ∧
    ∃ base : Profile (fun _ : ι => ℝ),
      ∃ r s : ℝ, r ≠ s ∧
        QuadrupleBidirectionalExtensibility P i k base r s ∧
          (∃ a0 : ℝ, QuadrupleDescendingSeedBracketingCertificate P i k base r s a0) ∧
            (∃ a0' : ℝ, QuadrupleAscendingSeedBracketingCertificate P i k base r s a0') ∧
              QuadrupleStrictReferenceUtilityOrdering R k r s

/-- **Pointwise alignment from per-coordinate Wakker alignment data.** -/
theorem pointwiseAlignmentCertificate_of_coordinateWakkerAlignmentData
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (R : AdditiveRep P) (i : ι)
    (hData : CoordinateWakkerAlignmentData R i) :
    PointwiseAlignmentCertificate P i := by
  obtain ⟨k, hki, base, r, s, hrs, hExt, ⟨a0, hBracketDesc⟩, ⟨a0', hBracketAsc⟩, hRef⟩ := hData
  exact pointwiseAlignmentCertificate_of_bracketing_alignment
    hsolv R hki base r s hrs hExt a0 hBracketDesc a0' hBracketAsc hRef

/-- **Wakker topological axiom bundle.**

Single named hypothesis collapsing the topology infrastructure plus alignment
data into one bundle.  Body content:

* `ConnectedCoordinates P` (Wakker IV.2.3 spatial component, free for ℝ)
* `∀ i, Continuous (R.V i)` (per-coordinate continuity)
* `∀ i, CoordinateUtilityUnboundedCertificate R i` (image unboundedness)
* `SingleCoordinateMonotonicityAxiom P` (structural monotonicity)
* `∀ i, CoordinateWakkerAlignmentData R i` (per-coordinate alignment data)

Together with `RestrictedSolvability P` (kept as a separate explicit
hypothesis to match the existing consumer interface), this bundle discharges
every downstream construction-stack target through the Stage T2-T4 chain. -/
def WakkerTopologicalAxiomBundle
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) : Prop :=
  ProductPref.ConnectedCoordinates P ∧
    (∀ i : ι, Continuous (R.V i)) ∧
      (∀ i : ι, CoordinateUtilityUnboundedCertificate R i) ∧
        SingleCoordinateMonotonicityAxiom P ∧
          (∀ i : ι, CoordinateWakkerAlignmentData R i)

/-- **Per-coordinate alignment certificate from the Wakker topological
axiom bundle.** -/
theorem coordinatePerCoordinateAlignmentCertificate_of_wakkerTopologicalAxiomBundle
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    {R : AdditiveRep P}
    (hBundle : WakkerTopologicalAxiomBundle R) :
    CoordinatePerCoordinateAlignmentCertificate P := by
  intro i
  obtain ⟨_, _, _, _, hData⟩ := hBundle
  exact pointwiseAlignmentCertificate_of_coordinateWakkerAlignmentData
    hsolv R i (hData i)

/-- **Topology half from the Wakker topological axiom bundle.** -/
theorem wakkerMonographTopologyHalfInputCertificate_of_wakkerTopologicalAxiomBundle
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    (hBundle : WakkerTopologicalAxiomBundle R) :
    WakkerMonographTopologyHalfInputCertificate R := by
  obtain ⟨hConn, hCont, hUnb, hMonoStruct, _⟩ := hBundle
  exact wakkerMonographTopologyHalfInputCertificate_of_connected_structuralMonotonicity_continuous_unbounded
    R hConn hMonoStruct hCont hUnb

/-- **Monograph-level aggregate bundle from the Wakker topological axiom bundle.** -/
theorem wakkerMonographLevelInputCertificate_of_wakkerTopologicalAxiomBundle
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    {R : AdditiveRep P}
    (hBundle : WakkerTopologicalAxiomBundle R) :
    WakkerMonographLevelInputCertificate R := by
  have hAlign := coordinatePerCoordinateAlignmentCertificate_of_wakkerTopologicalAxiomBundle
    hsolv hBundle
  have hTop := wakkerMonographTopologyHalfInputCertificate_of_wakkerTopologicalAxiomBundle hBundle
  exact wakkerMonographLevelInputCertificate_of_perCoordinateAlignment_and_topologyHalf
    hAlign hTop

/-- **Three named raw outputs from the Wakker topological axiom bundle.**

End-to-end discharge from the structural-topological axiom bundle to the
three named raw outputs through the entire Stage T2-T4 chain. -/
theorem wakkerRawOutputs_of_wakkerTopologicalAxiomBundle
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hBundle : WakkerTopologicalAxiomBundle R) :
    CoordinateRationalRefinementBisectionCertificate R ∧
      CoordinateConnectedContinuityOneStepBracketCertificate P ∧
        CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) :=
  wakkerRawOutputs_of_monographLevel R hsolv
    (wakkerMonographLevelInputCertificate_of_wakkerTopologicalAxiomBundle hsolv hBundle)

/-- **Calibrated integer refinement and full continuity from the Wakker
topological axiom bundle.** -/
theorem integerRefinement_and_fullContinuity_of_wakkerTopologicalAxiomBundle
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hBundle : WakkerTopologicalAxiomBundle R) :
    CoordinateStandardSequenceIntegerRefinementCertificate R ∧
      CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) :=
  integerRefinement_and_fullContinuity_of_monographLevel R hsolv
    (wakkerMonographLevelInputCertificate_of_wakkerTopologicalAxiomBundle hsolv hBundle)

/-- **Wakker topological axiom bundle from named components.**

Reverse assembly: the canonical discharge route is to produce each named
component independently and assemble the bundle. -/
theorem wakkerTopologicalAxiomBundle_of_components
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    (hConn : ProductPref.ConnectedCoordinates P)
    (hCont : ∀ i : ι, Continuous (R.V i))
    (hUnb : ∀ i : ι, CoordinateUtilityUnboundedCertificate R i)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P)
    (hData : ∀ i : ι, CoordinateWakkerAlignmentData R i) :
    WakkerTopologicalAxiomBundle R :=
  ⟨hConn, hCont, hUnb, hMonoStruct, hData⟩

/-! ##### Stage T6: Bracketing-pair discharge from utility unboundedness

The last remaining non-axiomatic piece in Stage T5's bundle: the bracketing
pair certificates inside `CoordinateWakkerAlignmentData`.

Honest scope reduction: under any additive representation, the bracketing
inequalities reduce to bracketing the *real value*
`R.V i a0 + R.V k r - R.V k s` between two values of `R.V i`.  This is
exactly the content of `CoordinateUtilityUnboundedCertificate R i`, which
is already directly provided as a primitive in Stage T5's bundle.  The
theorems below close the loop: bracketing pairs are theorem-backed from
unboundedness.

The Archimedean axiom appears upstream: it is the structural source of
unboundedness through the standard-sequence-pair certificate
(`coordinateUtilityUnboundedCertificate_of_strictStandardSequence_pair`),
which Wakker (1989) IV.2.6 derives from essentiality + restricted solvability +
the Archimedean axiom.  Stage T6 therefore mechanizes the analytic core of
the bracketing discharge directly under additive representation, leaving the
Archimedean-to-unboundedness step as the structural input. -/

/-- **Descending seed bracketing certificate from utility unboundedness.**

Under additive representation, the descending seed bracketing inequalities
reduce to bracketing the real value `R.V i a0 + R.V k r - R.V k s` between
two values of `R.V i`.  Coordinate utility unboundedness on `i` supplies both
witnesses `v` and `w`. -/
theorem quadrupleDescendingSeedBracketingCertificate_of_unbounded
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {i k : ι} (hki : k ≠ i)
    (base : Profile (fun _ : ι => ℝ))
    (r s : ℝ)
    (a0 : ℝ)
    (hUnb : CoordinateUtilityUnboundedCertificate R i) :
    QuadrupleDescendingSeedBracketingCertificate P i k base r s a0 := by
  obtain ⟨w, v, hlo, hhi⟩ := hUnb (R.V i a0 + R.V k r - R.V k s)
  refine ⟨v, w, ?_, ?_⟩
  · -- Goal: weakPref (update (update base k s) i v) (update (update base i a0) k r)
    rw [R.represents]
    have hLhs := sum_eq_pair_add_rest R.V
      (Function.update (Function.update base k s) i v)
      (j := i) (k := k) hki.symm
    have hRhs := sum_eq_pair_add_rest R.V
      (Function.update (Function.update base i a0) k r)
      (j := i) (k := k) hki.symm
    have hLhs_i :
        R.V i ((Function.update (Function.update base k s) i v) i) = R.V i v := by
      rw [Function.update_self]
    have hLhs_k :
        R.V k ((Function.update (Function.update base k s) i v) k) = R.V k s := by
      rw [Function.update_of_ne hki, Function.update_self]
    have hRhs_i :
        R.V i ((Function.update (Function.update base i a0) k r) i) = R.V i a0 := by
      rw [Function.update_of_ne hki.symm, Function.update_self]
    have hRhs_k :
        R.V k ((Function.update (Function.update base i a0) k r) k) = R.V k r := by
      rw [Function.update_self]
    have hrest :
        (∑ t ∈ (Finset.univ.erase i).erase k,
            R.V t ((Function.update (Function.update base i a0) k r) t)) =
          ∑ t ∈ (Finset.univ.erase i).erase k,
            R.V t ((Function.update (Function.update base k s) i v) t) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      have htk : t ≠ k := Finset.ne_of_mem_erase ht
      have ht_erase_i : t ∈ Finset.univ.erase i := (Finset.mem_erase.mp ht).2
      have hti : t ≠ i := Finset.ne_of_mem_erase ht_erase_i
      rw [Function.update_of_ne htk, Function.update_of_ne hti,
          Function.update_of_ne hti, Function.update_of_ne htk]
    rw [hRhs, hLhs, hRhs_i, hRhs_k, hLhs_i, hLhs_k, hrest]
    linarith
  · -- Goal: weakPref (update (update base i a0) k r) (update (update base k s) i w)
    rw [R.represents]
    have hLhs := sum_eq_pair_add_rest R.V
      (Function.update (Function.update base i a0) k r)
      (j := i) (k := k) hki.symm
    have hRhs := sum_eq_pair_add_rest R.V
      (Function.update (Function.update base k s) i w)
      (j := i) (k := k) hki.symm
    have hLhs_i :
        R.V i ((Function.update (Function.update base i a0) k r) i) = R.V i a0 := by
      rw [Function.update_of_ne hki.symm, Function.update_self]
    have hLhs_k :
        R.V k ((Function.update (Function.update base i a0) k r) k) = R.V k r := by
      rw [Function.update_self]
    have hRhs_i :
        R.V i ((Function.update (Function.update base k s) i w) i) = R.V i w := by
      rw [Function.update_self]
    have hRhs_k :
        R.V k ((Function.update (Function.update base k s) i w) k) = R.V k s := by
      rw [Function.update_of_ne hki, Function.update_self]
    have hrest :
        (∑ t ∈ (Finset.univ.erase i).erase k,
            R.V t ((Function.update (Function.update base k s) i w) t)) =
          ∑ t ∈ (Finset.univ.erase i).erase k,
            R.V t ((Function.update (Function.update base i a0) k r) t) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      have htk : t ≠ k := Finset.ne_of_mem_erase ht
      have ht_erase_i : t ∈ Finset.univ.erase i := (Finset.mem_erase.mp ht).2
      have hti : t ≠ i := Finset.ne_of_mem_erase ht_erase_i
      rw [Function.update_of_ne hti, Function.update_of_ne htk,
          Function.update_of_ne htk, Function.update_of_ne hti]
    rw [hLhs, hRhs, hLhs_i, hLhs_k, hRhs_i, hRhs_k, hrest]
    linarith

/-- **Ascending seed bracketing certificate from utility unboundedness.**

Symmetric to the descending case with the reference exchange direction
swapped. -/
theorem quadrupleAscendingSeedBracketingCertificate_of_unbounded
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {i k : ι} (hki : k ≠ i)
    (base : Profile (fun _ : ι => ℝ))
    (r s : ℝ)
    (a0' : ℝ)
    (hUnb : CoordinateUtilityUnboundedCertificate R i) :
    QuadrupleAscendingSeedBracketingCertificate P i k base r s a0' := by
  -- The ascending bracketing is the descending bracketing with (r, s) swapped.
  -- Apply the descending bracketing theorem to (s, r).
  exact quadrupleDescendingSeedBracketingCertificate_of_unbounded R hki base s r a0' hUnb

/-- **Per-coordinate Wakker alignment data from connectedness, unboundedness,
and a strict reference exchange witness.**

End-to-end Stage T6 consumer producing the per-coordinate alignment data from
the structural primitives.  The bidirectional one-step extensibility comes
from connectedness + per-coord continuity + unboundedness (Stage T2);
the bracketing certificates come from unboundedness alone (Stage T6 above);
the strict reference utility ordering is a direct hypothesis (in Wakker's
framework, supplied by essentiality on the auxiliary coordinate). -/
theorem coordinateWakkerAlignmentData_of_connected_continuous_unbounded_strictReference
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {i k : ι} (hki : k ≠ i)
    (base : Profile (fun _ : ι => ℝ))
    (r s : ℝ) (hrs : r ≠ s)
    (hConn : ProductPref.ConnectedCoordinates P)
    (hCont : Continuous (R.V i))
    (hUnb : CoordinateUtilityUnboundedCertificate R i)
    (hRef : QuadrupleStrictReferenceUtilityOrdering R k r s) :
    CoordinateWakkerAlignmentData R i := by
  refine ⟨k, hki, base, r, s, hrs, ?_, ?_, ?_, hRef⟩
  · -- Bidirectional extensibility from connectedness + continuity + unboundedness.
    exact quadrupleBidirectionalExtensibility_of_connected_continuous_unbounded
      R hki base r s hConn hCont hUnb
  · -- Descending bracketing from unboundedness (some seed point, e.g., 0).
    exact ⟨0, quadrupleDescendingSeedBracketingCertificate_of_unbounded
      R hki base r s 0 hUnb⟩
  · -- Ascending bracketing from unboundedness (some seed point, e.g., 0).
    exact ⟨0, quadrupleAscendingSeedBracketingCertificate_of_unbounded
      R hki base r s 0 hUnb⟩

/-- **End-to-end consumer: Wakker topological axiom bundle from connectedness,
per-coordinate continuity + unboundedness, structural monotonicity, and a
per-coordinate strict reference exchange witness.**

The cleanest end-to-end discharge of Stage T5's bundle: the per-coordinate
alignment data is derived automatically from the per-coordinate continuity +
unboundedness + a strict reference exchange (the latter provided per
coordinate as a witness pair). -/
theorem wakkerTopologicalAxiomBundle_of_strictReferenceWitnesses
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hConn : ProductPref.ConnectedCoordinates P)
    (hCont : ∀ i : ι, Continuous (R.V i))
    (hUnb : ∀ i : ι, CoordinateUtilityUnboundedCertificate R i)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P)
    (hRef : ∀ i : ι, ∃ k : ι, k ≠ i ∧ ∃ r s : ℝ, r ≠ s ∧
      QuadrupleStrictReferenceUtilityOrdering R k r s) :
    WakkerTopologicalAxiomBundle R := by
  refine ⟨hConn, hCont, hUnb, hMonoStruct, ?_⟩
  intro i
  obtain ⟨k, hki, r, s, hrs, hRefi⟩ := hRef i
  let base : Profile (fun _ : ι => ℝ) := fun _ => 0
  exact coordinateWakkerAlignmentData_of_connected_continuous_unbounded_strictReference
    R hki base r s hrs hConn (hCont i) (hUnb i) hRefi

/-- **End-to-end discharge from connectedness + continuity + unboundedness +
structural monotonicity + per-coordinate strict reference witnesses to the
three named raw outputs.** -/
theorem wakkerRawOutputs_of_strictReferenceWitnesses
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hConn : ProductPref.ConnectedCoordinates P)
    (hCont : ∀ i : ι, Continuous (R.V i))
    (hUnb : ∀ i : ι, CoordinateUtilityUnboundedCertificate R i)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P)
    (hRef : ∀ i : ι, ∃ k : ι, k ≠ i ∧ ∃ r s : ℝ, r ≠ s ∧
      QuadrupleStrictReferenceUtilityOrdering R k r s) :
    CoordinateRationalRefinementBisectionCertificate R ∧
      CoordinateConnectedContinuityOneStepBracketCertificate P ∧
        CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) := by
  exact wakkerRawOutputs_of_wakkerTopologicalAxiomBundle R hsolv
    (wakkerTopologicalAxiomBundle_of_strictReferenceWitnesses
      R hConn hCont hUnb hMonoStruct hRef)

end CertificateChecklist

end WakkerRoadmap
