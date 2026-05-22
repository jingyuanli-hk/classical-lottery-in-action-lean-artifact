/-
Infrastructure for proving Wakker (1989) IV.2.7 and Debreu–Koopmans (1982).

This file builds the formal scaffolding that the deep theorems would
consume: precise statements of the structural axioms (essentiality,
solvability, Archimedean axiom, tradeoff consistency), key derived
notions (standard sequences, equally-spaced grids, comonotonic
modifications), and a number of fully-proven supporting lemmas.

The file is **complete in its own right**: every lemma stated here is
fully proved.  The deep results (`wakker_IV_2_7`, `debreu_koopmans_hard`)
that consume these lemmas are stated separately (in
`WakkerDebreuKoopmans.lean`) and remain wrappers around explicit
construction certificates.

Sections
========
  §1   Profile arithmetic and `Function.update` algebra
  §2   Coordinate-wise preference relations `≽_j`
  §3   Essentiality (proper definition + basic properties)
  §4   Restricted Solvability (proper definition + corollaries)
  §5   Tradeoff Consistency (proper definition)
  §6   Standard Sequences
  §7   The Archimedean Axiom (proper definition)
  §8   Comonotonic modifications and trade-off measurement
  §9   Convexity of upper-contour sets and concavity of additive utilities
  §10  Sums of concave functions on convex sets
  §11  Wakker Construction Certificate — first-layer consequences
       (seed for the spin-out mechanized-decision-theory paper)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Logic.Function.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open scoped BigOperators
open Function Finset

namespace WakkerInfra

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- A profile assigns to each coordinate `i : ι` a value in `Xᵢ`. -/
abbrev Profile (X : ι → Type v) := ∀ i, X i

/-- The product preference structure: a binary relation on profiles. -/
structure ProductPref (X : ι → Type v) where
  weakPref : Profile X → Profile X → Prop

namespace ProductPref

variable {X : ι → Type v}

/-- Strict preference. -/
def strict (P : ProductPref X) (x y : Profile X) : Prop :=
  P.weakPref x y ∧ ¬ P.weakPref y x

/-- Indifference. -/
def indiff (P : ProductPref X) (x y : Profile X) : Prop :=
  P.weakPref x y ∧ P.weakPref y x

/-- **Weak order** (Axiom 0): `≽` is complete and transitive. -/
class IsWeakOrder (P : ProductPref X) : Prop where
  complete   : ∀ x y, P.weakPref x y ∨ P.weakPref y x
  transitive : ∀ x y z, P.weakPref x y → P.weakPref y z → P.weakPref x z

end ProductPref

/-! ## §1.  Profile arithmetic -/

namespace Profile

variable {X : ι → Type v}

/-- Two profiles **agree off** a set `T` if `x i = y i` for every `i ∉ T`. -/
def agreeOff (T : Set ι) (x y : Profile X) : Prop :=
  ∀ i, i ∉ T → x i = y i

/-- `agreeOff` is reflexive. -/
@[simp] lemma agreeOff_refl (T : Set ι) (x : Profile X) : agreeOff T x x :=
  fun _ _ => rfl

/-- `agreeOff` is symmetric. -/
lemma agreeOff_symm {T : Set ι} {x y : Profile X}
    (h : agreeOff T x y) : agreeOff T y x :=
  fun i hi => (h i hi).symm

/-- `agreeOff` is transitive. -/
lemma agreeOff_trans {T : Set ι} {x y z : Profile X}
    (hxy : agreeOff T x y) (hyz : agreeOff T y z) : agreeOff T x z :=
  fun i hi => (hxy i hi).trans (hyz i hi)

/-- `agreeOff` is **anti-monotone** in the off-set: a *larger* "off" set
gives a *weaker* condition.  Equivalently, agreeing off a smaller set
implies agreeing off a larger set. -/
lemma agreeOff_mono {T T' : Set ι} (h : T ⊆ T') {x y : Profile X}
    (hxy : agreeOff T x y) : agreeOff T' x y :=
  fun i hi => hxy i (fun h' => hi (h h'))

/-- `Function.update x j v` agrees with `x` off `{j}`. -/
lemma agreeOff_update_singleton (x : Profile X) (j : ι) (v : X j) :
    agreeOff {j} x (Function.update x j v) := by
  intro i hi
  have : i ≠ j := by
    intro heq
    apply hi
    simp [heq]
  exact (Function.update_of_ne this v x).symm

end Profile

/-! ## §2.  Coordinate-wise restriction of `≽` -/

namespace ProductPref

variable {X : ι → Type v}

/-- The **coordinate `j` preference** `≽_j` derived from `P`:
`v ≽_j w ` iff for *some* (equivalently, *every*) profile `a` we have
`(v at j, a otherwise) ≽ (w at j, a otherwise)`.

We define the "for some" version here; the "for every" form is the
content of §3 and is the conclusion of `coordinate_separable`
(Theorem 1.4 in Wakker, derivable from tradeoff consistency). -/
def coordPref (P : ProductPref X) (j : ι) (a : Profile X) (v w : X j) : Prop :=
  P.weakPref (Function.update a j v) (Function.update a j w)

/-- **Coordinate-wise weak order** for a fixed profile `a`. -/
lemma coordPref_complete (P : ProductPref X) [IsWeakOrder P]
    (j : ι) (a : Profile X) (v w : X j) :
    P.coordPref j a v w ∨ P.coordPref j a w v := by
  exact IsWeakOrder.complete _ _

/-- Transitivity of `≽_j` for a fixed profile `a`. -/
lemma coordPref_trans (P : ProductPref X) [IsWeakOrder P]
    {j : ι} {a : Profile X} {u v w : X j}
    (h₁ : P.coordPref j a u v) (h₂ : P.coordPref j a v w) :
    P.coordPref j a u w :=
  IsWeakOrder.transitive _ _ _ h₁ h₂

end ProductPref

/-! ## §3.  Essentiality -/

namespace ProductPref

variable {X : ι → Type v}

/-- A coordinate `j` is **essential** (Wakker, Definition III.2.1) if
there exist a profile `a` and two values `v ≠ w` of `X j` for which
the coordinate `j` change is preference-relevant. -/
def Essential (P : ProductPref X) (j : ι) : Prop :=
  ∃ (a : Profile X) (v w : X j),
    P.weakPref (Function.update a j v) (Function.update a j w) ∧
    ¬ P.weakPref (Function.update a j w) (Function.update a j v)

/-- A coordinate `j` is **inessential** if it is *not* essential — i.e., the
profile preference is independent of the value at `j`. -/
def Inessential (P : ProductPref X) (j : ι) : Prop :=
  ∀ (a : Profile X) (v w : X j),
    P.weakPref (Function.update a j v) (Function.update a j w) ∧
    P.weakPref (Function.update a j w) (Function.update a j v)

lemma not_essential_iff_inessential (P : ProductPref X) [IsWeakOrder P]
    (j : ι) :
    ¬ Essential P j ↔ Inessential P j := by
  unfold Essential Inessential
  constructor
  · -- Suppose `j` is not essential.  We show inessentiality directly.
    intro h a v w
    -- Goal: `(v at j) ≽ (w at j)` AND `(w at j) ≽ (v at j)`.
    refine ⟨?_, ?_⟩
    · -- Show `v ≽_j w` at profile `a`.
      -- By completeness, either `v ≽_j w` or `w ≻_j v` (failing of the first).
      rcases IsWeakOrder.complete (P := P)
        (Function.update a j v) (Function.update a j w) with hvw | hwv
      · exact hvw
      · -- We have `w ≽_j v`.  If we *also* had `¬ v ≽_j w` we'd witness
        -- essentiality, contradicting `h`.  So `v ≽_j w` must hold.
        by_contra hnot
        exact h ⟨a, w, v, hwv, hnot⟩
    · -- Symmetric: show `w ≽_j v` at profile `a`.
      rcases IsWeakOrder.complete (P := P)
        (Function.update a j w) (Function.update a j v) with hwv | hvw
      · exact hwv
      · by_contra hnot
        exact h ⟨a, v, w, hvw, hnot⟩
  · -- Inessential ⇒ ¬ Essential.
    rintro hI ⟨a, v, w, _hvw, hnot⟩
    exact hnot (hI a v w).2

end ProductPref

/-! ## §4.  Restricted Solvability -/

namespace ProductPref

variable {X : ι → Type v}

/-- **Restricted Solvability** (Wakker IV.2.4):

For all profiles `a, b, c` and any coordinate `j`, if
`(a-with-j-set-to-v) ≽ b ≽ (a-with-j-set-to-w)`, then there exists a
value `c : X j` such that `(a-with-j-set-to-c) ∼ b`.

I.e., bracketing strict preferences in coordinate `j` yields an
indifference point. -/
def RestrictedSolvability (P : ProductPref X) : Prop :=
  ∀ (a b : Profile X) (j : ι) (v w : X j),
    P.weakPref (Function.update a j v) b →
    P.weakPref b (Function.update a j w) →
    ∃ c : X j, P.indiff (Function.update a j c) b

/-- Symmetric solvability: bracketing the *opposite* direction also yields
an indifference. -/
lemma restrictedSolvability_symm (P : ProductPref X)
    [IsWeakOrder P] (h : RestrictedSolvability P)
    (a b : Profile X) (j : ι) (v w : X j)
    (hvb : P.weakPref b (Function.update a j v))
    (hbw : P.weakPref (Function.update a j w) b) :
    ∃ c : X j, P.indiff (Function.update a j c) b := by
  -- Apply solvability to the swapped bracket.
  exact h a b j w v hbw hvb

end ProductPref

/-! ## §5.  Tradeoff Consistency -/

namespace ProductPref

variable {X : ι → Type v}

/-- **Tradeoff consistency** (Wakker IV.2.5; sometimes called "cardinal
coordinate independence" or, in two-coordinate settings, the "hexagon
condition").

Informally: the relative strength of an *exchange* `xⱼ ↦ xⱼ'` in
coordinate `j` is independent of what is happening on the other
coordinates, *and* it is comparable across coordinates in the sense that
the same exchange has the same "trade-off magnitude" no matter where the
ambient profile lies.

Formally (Wakker's Definition IV.2.5):
  Whenever profiles `a, b, c, d, e, f, g, h` differ from each other only
  on coordinate `j`, and the four indifferences
      a ∼ b,  c ∼ d,  e ∼ f
  hold, then `g ∼ h` follows from a fourth indifference.

This is the technical foundation of standard sequences and is what makes
the additive representation cardinally unique.  We state it as a class
parameterised on `P`. -/
class TradeoffConsistency (P : ProductPref X) : Prop where
  consistent :
    ∀ (j : ι) (a b c d e f g h : Profile X)
      (_ : Profile.agreeOff {j} a b)
      (_ : Profile.agreeOff {j} c d)
      (_ : Profile.agreeOff {j} e f)
      (_ : Profile.agreeOff {j} g h)
      -- Three indifferences known:
      (_ : P.indiff a b)
      (_ : P.indiff c d)
      (_ : P.indiff e f)
      -- Compatibility between the first three exchanges:
      (_ : a j = c j) (_ : b j = d j)
      (_ : c j = e j) (_ : d j = f j)
      (_ : a j = g j) (_ : b j = h j),
      -- Conclusion: the fourth exchange is also an indifference.
      P.indiff g h

end ProductPref

/-! ## §6.  Standard Sequences -/

namespace ProductPref

variable {X : ι → Type v}

/-- A **standard sequence** in coordinate `j` is a sequence `α₀, α₁, α₂, …`
in `X j` together with two reference values `r, s ∈ X k` (in some other
coordinate `k`) such that, when the profile is fixed everywhere else,
the exchange `αₙ ↦ αₙ₊₁` in coordinate `j` is indifferent to the
exchange `r ↦ s` in coordinate `k`.

This is Wakker's Definition III.4.1 — a "ruler" in coordinate `j` whose
unit length is calibrated by the reference exchange in coordinate `k`. -/
structure StandardSequence (P : ProductPref X) (j : ι) where
  /-- The other coordinate that supplies the reference unit. -/
  k          : ι
  k_ne_j     : k ≠ j
  /-- The reference values `r ≺ s` in coordinate `k`. -/
  r          : X k
  s          : X k
  r_ne_s     : r ≠ s
  /-- The base profile (fixed at every coordinate other than `j` and
  used as the ambient context). -/
  base       : Profile X
  /-- The standard sequence itself. -/
  α          : ℕ → X j
  /-- Equally-spaced indifference: the exchange `αₙ ↦ αₙ₊₁` in
  coordinate `j` is indifferent to the exchange `r ↦ s` in
  coordinate `k`. -/
  spaced     : ∀ n,
    P.indiff
      (Function.update (Function.update base j (α n))     k r)
      (Function.update (Function.update base j (α (n+1))) k s)

/-- A standard sequence is **strict** if any one of its exchanges is a
strict preference (this implies all of them are, by tradeoff
consistency). -/
def StandardSequence.IsStrict {P : ProductPref X} {j : ι}
    (σ : StandardSequence P j) : Prop :=
  P.strict (Function.update σ.base j (σ.α 0))
           (Function.update σ.base j (σ.α 1))

end ProductPref

/-! ## §7.  Archimedean Axiom -/

namespace ProductPref

variable {X : ι → Type v}

/-- **Archimedean axiom** (Wakker IV.2.6, restricted to coordinate `j`):
no infinite *bounded* strict standard sequence exists.  Equivalently,
every standard sequence that stays inside a preference-bounded region
must be finite.

The bounded-region clause is captured by the existence of profile
"bounds" `lo, hi` such that `lo ≼ ... ≼ hi` for every term of the
sequence.  The conclusion is that the sequence must be eventually
constant or empty. -/
def Archimedean (P : ProductPref X) (j : ι) : Prop :=
  ∀ (σ : StandardSequence P j),
    σ.IsStrict →
    -- there is no `lo, hi` profile bounding the entire sequence in `≽`.
    ¬ ∃ lo hi : Profile X,
      ∀ n,
        P.weakPref hi (Function.update σ.base j (σ.α n)) ∧
        P.weakPref (Function.update σ.base j (σ.α n)) lo

end ProductPref

/-! ## §8.  Comonotonic modifications and trade-off measurement -/

namespace ProductPref

variable {X : ι → Type v}

/-- Two profiles `x, y` agreeing off `{j, k}` are said to be a
**(j,k)-modification** of each other.  This is the smallest unit of
profile change involving more than one coordinate. -/
def IsTwoCoordModification (j k : ι) (x y : Profile X) : Prop :=
  Profile.agreeOff {j, k} x y

/-- A two-coordinate modification with `j ≠ k` corresponds exactly to
choosing values for the two coordinates `j` and `k` independently. -/
lemma isTwoCoordModification_iff (j k : ι) (_hjk : j ≠ k)
    (x y : Profile X) :
    IsTwoCoordModification j k x y ↔
    ∀ i, i ≠ j → i ≠ k → x i = y i := by
  unfold IsTwoCoordModification Profile.agreeOff
  refine ⟨fun h i hij hik => h i ?_, fun h i hi => h i ?_ ?_⟩
  · simp [hij, hik]
  · intro hij; apply hi; simp [hij]
  · intro hik; apply hi; simp [hik]

end ProductPref

/-! ## §9.  Convexity of upper-contour sets and concavity of additive
        utilities — partial results

This section contains structural lemmas on convex preferences that are
used by the *easy* and (eventually) *hard* directions of
Debreu–Koopmans.  These are fully proved here, not assumed.

We work with `X i = ℝ` for concreteness. -/

namespace ProductPref

variable {X : ι → Type v}

/-- A **rectangular convex domain** `D = ∏ᵢ Sᵢ` is convex.  Pure Mathlib
boilerplate, packaged here for use in Wakker / DK proofs. -/
lemma convex_product_of_convex (S : ι → Set ℝ) (hS : ∀ i, Convex ℝ (S i)) :
    Convex ℝ ({ x : ι → ℝ | ∀ i, x i ∈ S i }) := by
  intro x hx y hy a b ha hb hab i
  exact hS i (hx i) (hy i) ha hb hab

/-- **Convex preference** on a product: the upper-contour set of every
profile is convex inside the product domain. -/
def ConvexPref (P : ProductPref (fun _ : ι => ℝ)) (D : Set (ι → ℝ)) : Prop :=
  Convex ℝ D ∧
  ∀ y, Convex ℝ ({ x ∈ D | P.weakPref x y })

/-- For a *real-valued* representation `V`, the upper-contour set
`{x : V x ≥ V y}` of the induced preference is the super-level set
`{x : V y ≤ V x}` of `V` at `V y`. -/
lemma upperContour_eq_superLevel
    (P : ProductPref (fun _ : ι => ℝ))
    (V : (ι → ℝ) → ℝ)
    (h : ∀ x y : (ι → ℝ), P.weakPref x y ↔ V y ≤ V x)
    (y : ι → ℝ) :
    { x | P.weakPref x y } = { x | V y ≤ V x } := by
  ext x
  exact h x y

/-- The intersection of two convex sets is convex.  (Mathlib provides
this; we pin it down with the right type for use later.) -/
lemma convex_inter {D U : Set (ι → ℝ)} (hD : Convex ℝ D) (hU : Convex ℝ U) :
    Convex ℝ (D ∩ U) := hD.inter hU

/-- **The super-level set of a concave function on a convex set is convex.**
This is a key analytic fact used in the easy direction of Debreu–Koopmans
and in the convex-preference / concave-utility correspondence.

Note: `ConcaveOn ℝ D V` already encodes `D` as the underlying convex
domain, so the super-level set we form is `D ∩ {x : V y ≤ V x}`. -/
lemma convex_superLevel_of_concaveOn
    {D : Set (ι → ℝ)} (V : (ι → ℝ) → ℝ)
    (hVconc : ConcaveOn ℝ D V) (c : ℝ) :
    Convex ℝ ({ x ∈ D | c ≤ V x }) := by
  rintro x ⟨hxD, hxc⟩ y ⟨hyD, hyc⟩ a b ha hb hab
  refine ⟨hVconc.1 hxD hyD ha hb hab, ?_⟩
  -- concavity: V (a x + b y) ≥ a V x + b V y ≥ a c + b c = c
  have hconc : a • V x + b • V y ≤ V (a • x + b • y) :=
    hVconc.2 hxD hyD ha hb hab
  have h_ac : a * c ≤ a * V x := mul_le_mul_of_nonneg_left hxc ha
  have h_bc : b * c ≤ b * V y := mul_le_mul_of_nonneg_left hyc hb
  have h_combine : c ≤ a * V x + b * V y := by
    have hsum_c : a * c + b * c = c := by
      rw [← add_mul, hab, one_mul]
    calc c = a * c + b * c := hsum_c.symm
      _ ≤ a * V x + b * V y := by linarith
  -- combine concavity with the lower bound
  calc c ≤ a * V x + b * V y := h_combine
    _ = a • V x + b • V y := by simp [smul_eq_mul]
    _ ≤ V (a • x + b • y) := hconc

/-- **Convex preference from a concave numerical representation.**

If `P` is represented by `V`, i.e. `x ≽ y ⟺ V y ≤ V x`, and `V` is
concave on the domain `D`, then every upper-contour set is convex,
making `P` a convex preference. -/
lemma convexPref_of_concaveOn_repr
    (P : ProductPref (fun _ : ι => ℝ))
    {D : Set (ι → ℝ)} (hD : Convex ℝ D)
    (V : (ι → ℝ) → ℝ)
    (h : ∀ x y, P.weakPref x y ↔ V y ≤ V x)
    (hVconc : ConcaveOn ℝ D V) :
    ConvexPref P D := by
  refine ⟨hD, ?_⟩
  intro y
  -- The upper-contour set of `y` is `{x ∈ D | V y ≤ V x}`,
  -- which is the super-level set of `V` at `V y`.
  have h_eq :
      { x ∈ D | P.weakPref x y } = { x ∈ D | V y ≤ V x } := by
    ext x
    constructor
    · rintro ⟨hxD, hxy⟩; exact ⟨hxD, (h x y).mp hxy⟩
    · rintro ⟨hxD, hxy⟩; exact ⟨hxD, (h x y).mpr hxy⟩
  rw [h_eq]
  exact convex_superLevel_of_concaveOn V hVconc (V y)

end ProductPref

/-! ## §10.  Sums of concave functions -/

namespace ProductPref

/-- **Sum of concave functions on convex sets.**

If for each `i : ι` the function `Vᵢ : ℝ → ℝ` is concave on `Sᵢ` (which
is convex), then the sum `(x ↦ Σᵢ Vᵢ(xᵢ))` is concave on the product
domain `{x : ∀ i, x i ∈ Sᵢ}`.  This is the analytic core of the easy
direction of Debreu–Koopmans. -/
theorem concaveOn_sum_coords
    (V : ι → ℝ → ℝ) (S : ι → Set ℝ)
    (hS : ∀ i, Convex ℝ (S i))
    (hV : ∀ i, ConcaveOn ℝ (S i) (V i)) :
    ConcaveOn ℝ
      ({ x : ι → ℝ | ∀ i, x i ∈ S i })
      (fun x => ∑ i, V i (x i)) := by
  refine ⟨convex_product_of_convex S hS, ?_⟩
  intro x hx y hy a b ha hb hab
  have hpt : ∀ i,
      a * V i (x i) + b * V i (y i) ≤ V i (a * x i + b * y i) := by
    intro i
    have := (hV i).2 (hx i) (hy i) ha hb hab
    simpa [smul_eq_mul] using this
  calc a * (∑ i, V i (x i)) + b * (∑ i, V i (y i))
      = ∑ i, (a * V i (x i) + b * V i (y i)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ ∑ i, V i (a * x i + b * y i) := by
        exact Finset.sum_le_sum (fun i _ => hpt i)

end ProductPref

/-! ## §11.  Wakker Construction Certificate — first-layer consequences

This section seeds the mechanized-decision-theory spin-out paper.  The
goal of the spin-out is to prove the **Wakker construction certificate**
from the structural axioms.  Here we set up that certificate inside
the infrastructure namespace and prove its **forward (necessity) direction**:
every consequence that *any* prospective Wakker IV.2.7 proof must
reproduce — weak order, essentiality of any nontrivial coordinate,
restricted solvability, tradeoff consistency, the Archimedean axiom —
is shown here to follow from the existence of an additive representation,
without invoking any deep Wakker machinery.

The forward direction is exactly the content of Wakker (1989), §IV.6
(necessity of the seven axioms).  It is also the natural first
deliverable for the spin-out: a complete proof that the certificate's
output is internally consistent with the certificate's required inputs.

The hard direction — *constructing* the certificate from the seven
axioms — is the open multi-month theorem-proving task scoped in
`MechanizedDecisionTheoryWakkerDK.tex`.  The infrastructure here is
designed so that future construction work can be plugged in below this
section without touching the consumer files.
-/

namespace ProductPref

variable {X : ι → Type v}

/-- An assignment `V : (i : ι) → X i → ℝ` of coordinate utilities is an
**additive representation** of `P` if profile preference is decided by
the sum of coordinate utilities. -/
def AdditivelyRepresents (P : ProductPref X) (V : (i : ι) → X i → ℝ) : Prop :=
  ∀ x y : Profile X,
    P.weakPref x y ↔ (∑ i, V i (y i)) ≤ (∑ i, V i (x i))

/-- The **Wakker construction certificate** for a product preference: there
exist coordinate utilities `V` such that profile preference is exactly the
order on additive sums.  This is the local mirror of
`WakkerDebreuKoopmans.WakkerRoadmap.WakkerConstructionCertificate`,
phrased inside the infrastructure namespace so that this file is
self-contained for the spin-out development. -/
def WakkerConstructionCertificate (P : ProductPref X) : Prop :=
  ∃ V : (i : ι) → X i → ℝ, AdditivelyRepresents P V

/-! ### §11.1  Sum-update reduction

A single `Function.update` move on a profile shifts exactly one summand
in any additive representation. -/

/-- The additive sum of `V` on `Function.update a j v` differs from the
sum on `Function.update a j w` only in the `j`-th summand. -/
lemma sum_V_update_eq_update
    (V : (i : ι) → X i → ℝ) (a : Profile X) (j : ι) (v : X j) :
    (∑ i, V i (Function.update a j v i)) =
      V j v + ∑ i ∈ Finset.univ.erase j, V i (a i) := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
      Function.update_self, add_comm]
  refine congrArg (V j v + ·) ?_
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hij : i ≠ j := Finset.ne_of_mem_erase hi
  rw [Function.update_of_ne hij]

/-- Subtracting the two sums of `V` after replacing the `j`-th coordinate
collapses to the coordinate-utility difference. -/
lemma sum_V_update_diff
    (V : (i : ι) → X i → ℝ) (a : Profile X) (j : ι) (v w : X j) :
    (∑ i, V i (Function.update a j v i))
      - (∑ i, V i (Function.update a j w i)) = V j v - V j w := by
  rw [sum_V_update_eq_update V a j v, sum_V_update_eq_update V a j w]
  ring

/-! ### §11.2  Forward direction of the certificate

If `P` has an additive representation `V`, then `P` is a weak order, every
coordinate's essentiality is detected by `V j`, restricted solvability
follows from a real-analytic solvability statement on `V j`, and tradeoff
consistency holds automatically. -/

/-- **Necessity of weak order.**  Any additively-represented preference is
a weak order. -/
theorem isWeakOrder_of_additivelyRepresents
    {P : ProductPref X} {V : (i : ι) → X i → ℝ}
    (hV : AdditivelyRepresents P V) :
    IsWeakOrder P where
  complete := by
    intro x y
    rcases le_total (∑ i, V i (x i)) (∑ i, V i (y i)) with h | h
    · exact Or.inr ((hV y x).mpr h)
    · exact Or.inl ((hV x y).mpr h)
  transitive := by
    intro x y z hxy hyz
    have h₁ := (hV x y).mp hxy
    have h₂ := (hV y z).mp hyz
    exact (hV x z).mpr (h₂.trans h₁)

/-- **Coordinate-wise separability.**  If `P` is additively represented by
`V`, the coordinate-wise preference `≽_j` is determined by the
coordinate utility `V j` alone, independent of the ambient profile. -/
theorem coordPref_iff_of_additivelyRepresents
    {P : ProductPref X} {V : (i : ι) → X i → ℝ}
    (hV : AdditivelyRepresents P V)
    (j : ι) (a : Profile X) (v w : X j) :
    P.coordPref j a v w ↔ V j w ≤ V j v := by
  unfold coordPref
  rw [hV]
  rw [sum_V_update_eq_update V a j v, sum_V_update_eq_update V a j w]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **Coordinate preference is base-independent under additive representation.** -/
theorem coordPref_base_independent_of_additivelyRepresents
    {P : ProductPref X} {V : (i : ι) → X i → ℝ}
    (hV : AdditivelyRepresents P V)
    (j : ι) (a b : Profile X) (v w : X j) :
    P.coordPref j a v w ↔ P.coordPref j b v w := by
  rw [coordPref_iff_of_additivelyRepresents hV j a v w,
      coordPref_iff_of_additivelyRepresents hV j b v w]

/-- **Essentiality forces `V j` to be non-constant** (forward direction).
If `j` is essential in an additively-represented preference, the
coordinate utility `V j` takes at least two distinct values. -/
theorem Vj_nonconstant_of_essential_of_additivelyRepresents
    {P : ProductPref X} {V : (i : ι) → X i → ℝ}
    (hV : AdditivelyRepresents P V)
    {j : ι} (hj : Essential P j) :
    ∃ v w : X j, V j v ≠ V j w := by
  obtain ⟨a, v, w, hvw, hnotwv⟩ := hj
  refine ⟨v, w, ?_⟩
  -- `V j w ≤ V j v` from `hvw` and `¬ V j v ≤ V j w` from `hnotwv`,
  -- hence `V j v ≠ V j w`.
  have hle : V j w ≤ V j v :=
    (coordPref_iff_of_additivelyRepresents hV j a v w).mp hvw
  have hnot : ¬ V j v ≤ V j w := by
    intro hcontra
    apply hnotwv
    exact (coordPref_iff_of_additivelyRepresents hV j a w v).mpr hcontra
  intro h
  apply hnot
  rw [h]

/-- **`V j` non-constant produces essentiality of `j`** (reverse direction),
provided we have at least one base profile available.  The base-profile
hypothesis is automatic in the original Wakker setting because the
`Essential P j` predicate already quantifies over profiles, but is needed
in this purely-syntactic infrastructure layer. -/
theorem essential_of_Vj_nonconstant_of_additivelyRepresents
    {P : ProductPref X} {V : (i : ι) → X i → ℝ}
    (hV : AdditivelyRepresents P V)
    (j : ι) (a₀ : Profile X)
    (h : ∃ v w : X j, V j v ≠ V j w) :
    Essential P j := by
  obtain ⟨v, w, hne⟩ := h
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `V j v < V j w`: pick `(w, v)` so that `(w at j) ≻ (v at j)`.
    refine ⟨a₀, w, v, ?_, ?_⟩
    · exact (coordPref_iff_of_additivelyRepresents hV j a₀ w v).mpr hlt.le
    · intro hcontra
      have hle : V j w ≤ V j v :=
        (coordPref_iff_of_additivelyRepresents hV j a₀ v w).mp hcontra
      exact (not_le.mpr hlt) hle
  · -- `V j v > V j w`: pick `(v, w)` so that `(v at j) ≻ (w at j)`.
    refine ⟨a₀, v, w, ?_, ?_⟩
    · exact (coordPref_iff_of_additivelyRepresents hV j a₀ v w).mpr hgt.le
    · intro hcontra
      have hle : V j v ≤ V j w :=
        (coordPref_iff_of_additivelyRepresents hV j a₀ w v).mp hcontra
      exact (not_le.mpr hgt) hle

/-! ### §11.3  Tradeoff consistency under additive representation

The hexagon condition is the cardinality fingerprint of an additive
representation: it falls out of arithmetic on coordinate utilities.

The proof is purely algebraic: each indifference cancels everything
outside coordinate `j`, leaving the four coordinate-utility differences
`V j (a j) − V j (b j)`, etc., which compose to give the conclusion. -/

/-- **Necessity of tradeoff consistency** (Wakker's hexagon condition):
any additively-represented preference automatically satisfies tradeoff
consistency. -/
theorem tradeoffConsistency_of_additivelyRepresents
    {P : ProductPref X} {V : (i : ι) → X i → ℝ}
    (hV : AdditivelyRepresents P V) :
    TradeoffConsistency P where
  consistent := by
    intro j a b c d e f g h
      hab _hcd _hef _hgh
      hiab hicd hief
      hac hbd hce hdf hag hbh
    -- Translate every indifference into an equality of additive sums.
    -- `P.indiff x y ↔ ∑V x = ∑V y`.
    have indiff_iff : ∀ x y : Profile X,
        P.indiff x y ↔ (∑ i, V i (x i)) = (∑ i, V i (y i)) := by
      intro x y
      unfold ProductPref.indiff
      rw [hV x y, hV y x]
      constructor
      · rintro ⟨h1, h2⟩; linarith
      · intro heq; refine ⟨?_, ?_⟩ <;> linarith
    have eq_ab : (∑ i, V i (a i)) = (∑ i, V i (b i)) := (indiff_iff a b).mp hiab
    have eq_cd : (∑ i, V i (c i)) = (∑ i, V i (d i)) := (indiff_iff c d).mp hicd
    have eq_ef : (∑ i, V i (e i)) = (∑ i, V i (f i)) := (indiff_iff e f).mp hief
    -- For each pair `(x, y)` agreeing off `{j}`, `∑V x − ∑V y = V j (x j) − V j (y j)`.
    -- Express the `agreeOff {j}` rewrite as a sum-of-pairs cancellation.
    have agreeOff_diff : ∀ (x y : Profile X),
        Profile.agreeOff {j} x y →
        (∑ i, V i (x i)) - (∑ i, V i (y i)) = V j (x j) - V j (y j) := by
      intro x y hxy
      have h_off : ∀ i ∈ Finset.univ.erase j, V i (x i) = V i (y i) := by
        intro i hi
        have hij : i ≠ j := Finset.ne_of_mem_erase hi
        have : x i = y i := hxy i (by simp [hij])
        rw [this]
      have hxsum :
          (∑ i, V i (x i)) =
            V j (x j) + ∑ i ∈ Finset.univ.erase j, V i (x i) := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), add_comm]
      have hysum :
          (∑ i, V i (y i)) =
            V j (y j) + ∑ i ∈ Finset.univ.erase j, V i (y i) := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), add_comm]
      have hagree :
          (∑ i ∈ Finset.univ.erase j, V i (x i)) =
            (∑ i ∈ Finset.univ.erase j, V i (y i)) :=
        Finset.sum_congr rfl h_off
      rw [hxsum, hysum, hagree]
      ring
    -- Reduce each indifference equation to a coordinate-utility equation at `j`.
    have eq_ab_j : V j (a j) = V j (b j) := by
      have hd := agreeOff_diff a b hab
      have : V j (a j) - V j (b j) = 0 := by
        rw [← hd]; linarith
      linarith
    have eq_cd_j : V j (c j) = V j (d j) := by
      have hd := agreeOff_diff c d _hcd
      have : V j (c j) - V j (d j) = 0 := by
        rw [← hd]; linarith
      linarith
    have eq_ef_j : V j (e j) = V j (f j) := by
      have hd := agreeOff_diff e f _hef
      have : V j (e j) - V j (f j) = 0 := by
        rw [← hd]; linarith
      linarith
    -- Now propagate to `g, h`.  Compute the `g, h` difference using `_hgh`
    -- and the coordinate-utility chain.
    have hd_gh := agreeOff_diff g h _hgh
    -- Coordinate-value equalities from the matching hypotheses:
    -- `a j = c j = e j` and `b j = d j = f j` (via `hac, hce, hbd, hdf`).
    have hac' : V j (a j) = V j (c j) := by rw [hac]
    have hce' : V j (c j) = V j (e j) := by rw [hce]
    have hbd' : V j (b j) = V j (d j) := by rw [hbd]
    have hdf' : V j (d j) = V j (f j) := by rw [hdf]
    -- Combine with the indifference reductions to align `V j (a j) = V j (b j)`.
    have key : V j (a j) = V j (b j) := eq_ab_j
    have hag' : V j (g j) = V j (a j) := by rw [hag]
    have hbh' : V j (h j) = V j (b j) := by rw [hbh]
    have eq_gh_j : V j (g j) = V j (h j) := by
      rw [hag', hbh', key]
    have eq_gh_sum : (∑ i, V i (g i)) = (∑ i, V i (h i)) := by
      have : V j (g j) - V j (h j) = 0 := by rw [eq_gh_j]; ring
      have hgh_diff : (∑ i, V i (g i)) - (∑ i, V i (h i)) = 0 := by
        rw [hd_gh, eq_gh_j]; ring
      linarith
    exact (indiff_iff g h).mpr eq_gh_sum

/-! ### §11.4  Restricted solvability under additive representation

For an additively-represented preference, restricted solvability is
equivalent to a *real-analytic* solvability statement on the
coordinate utility `V j`.  We isolate the analytic statement and prove
that, conjoined with additive representation, it implies the structural
restricted-solvability axiom.  This is the recipe by which forward
proofs of the certificate eventually feed `RestrictedSolvability P`. -/

/-- **Coordinate-utility solvability** under additive representation:
the assertion that every value in the closed interval `[V j w, V j v]`
of `V j` is attained by some `c : X j`.

When `X j = ℝ` this is automatic; in the abstract setting it captures
the topological connectedness / continuity content of Wakker's
restricted-solvability axiom. -/
def CoordUtilitySolvability (V : (i : ι) → X i → ℝ) (j : ι) : Prop :=
  ∀ (lo hi : X j) (t : ℝ),
    V j lo ≤ t → t ≤ V j hi → ∃ c : X j, V j c = t

/-- **Necessity of restricted solvability** (analytic side).
If `P` is additively represented by `V` and every coordinate enjoys
the coordinate-utility solvability property, then `P` satisfies the
structural restricted-solvability axiom. -/
theorem restrictedSolvability_of_additivelyRepresents
    {P : ProductPref X} {V : (i : ι) → X i → ℝ}
    (hV : AdditivelyRepresents P V)
    (hsolv : ∀ j, CoordUtilitySolvability V j) :
    RestrictedSolvability P := by
  intro a b j v w hav hbw
  -- Sum of `V` on `Function.update a j x` equals `V j x + Sa`, where `Sa`
  -- is the sum over `Finset.univ.erase j` of `V i (a i)`.
  set Sa : ℝ := ∑ i ∈ Finset.univ.erase j, V i (a i) with hSa_def
  have hupd : ∀ x : X j,
      (∑ i, V i (Function.update a j x i)) = V j x + Sa := by
    intro x
    rw [sum_V_update_eq_update V a j x]
  -- Express the bracket inequalities in terms of `V j v, V j w` and `∑V b`.
  have hav' : (∑ i, V i (b i)) ≤ V j v + Sa := by
    have := (hV (Function.update a j v) b).mp hav
    rw [hupd v] at this
    exact this
  have hbw' : V j w + Sa ≤ (∑ i, V i (b i)) := by
    have := (hV b (Function.update a j w)).mp hbw
    rw [hupd w] at this
    exact this
  -- Target value `t := ∑V b - Sa` lies in `[V j w, V j v]`.
  set t : ℝ := (∑ i, V i (b i)) - Sa with ht_def
  have ht_lo : V j w ≤ t := by
    have h := hbw'; rw [ht_def]; linarith
  have ht_hi : t ≤ V j v := by
    have h := hav'; rw [ht_def]; linarith
  -- Coordinate solvability picks `c` with `V j c = t`.
  obtain ⟨c, hc⟩ := hsolv j w v t ht_lo ht_hi
  refine ⟨c, ?_, ?_⟩
  · -- `(c at j) ≽ b`: `(∑V (update a j c)) ≥ ∑V b`.
    refine (hV (Function.update a j c) b).mpr ?_
    rw [hupd c, hc, ht_def]
    linarith
  · -- `b ≽ (c at j)`: `∑V b ≥ ∑V (update a j c)`.
    refine (hV b (Function.update a j c)).mpr ?_
    rw [hupd c, hc, ht_def]
    linarith

/-! ### §11.5  Archimedean necessity

In an additively-represented preference, every strict standard sequence
in coordinate `j` increments `V j` by a fixed amount per step (the
two-coordinate `r ↦ s` step measured in `V σ.k`).  If that step is
nonzero, the sequence drifts to `±∞` in `V j`-value and cannot stay
inside any `≽`-bracket.  Hence the Archimedean axiom is necessary. -/

/-- **Two-coordinate `agreeOff` reduction** for sums of `V` along a
standard sequence.  Splitting the sum at `j` and `σ.k` reveals the
arithmetic of the standard-sequence step. -/
private lemma sum_V_two_coord_split
    {ι : Type u} [Fintype ι] [DecidableEq ι] {X : ι → Type v}
    (V : (i : ι) → X i → ℝ)
    (a : Profile X) (j k : ι) (hjk : k ≠ j) (vj : X j) (vk : X k) :
    (∑ i, V i (Function.update (Function.update a j vj) k vk i)) =
      V j vj + V k vk +
        ∑ i ∈ (Finset.univ.erase j).erase k, V i (a i) := by
  -- Pull out the `k` summand first using `Finset.sum_erase_add`.
  have hk_mem : k ∈ (Finset.univ : Finset ι) := Finset.mem_univ k
  rw [← Finset.sum_erase_add _ _ hk_mem]
  -- The `k`-summand simplifies via `Function.update_self`.
  have hk_eval :
      V k (Function.update (Function.update a j vj) k vk k) = V k vk := by
    simp [Function.update_self]
  rw [hk_eval]
  -- Now break `Finset.univ.erase k` at `j`.
  have hj_mem_erase : j ∈ Finset.univ.erase k := by
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro h; exact hjk h.symm
  rw [← Finset.sum_erase_add _ _ hj_mem_erase]
  -- The `j`-summand inside `Function.update_of_ne` evaluates correctly.
  have hj_eval :
      V j (Function.update (Function.update a j vj) k vk j) = V j vj := by
    have hjk' : j ≠ k := fun h => hjk h.symm
    rw [Function.update_of_ne hjk', Function.update_self]
  rw [hj_eval]
  -- The remaining sum has every index `i ≠ j, k`, where both updates are no-ops.
  have hcommute :
      (Finset.univ.erase k).erase j = (Finset.univ.erase j).erase k := by
    ext i; simp [Finset.mem_erase]; tauto
  rw [hcommute]
  have hrest_congr :
      (∑ i ∈ (Finset.univ.erase j).erase k,
          V i (Function.update (Function.update a j vj) k vk i)) =
        ∑ i ∈ (Finset.univ.erase j).erase k, V i (a i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_erase_j : i ∈ Finset.univ.erase j := Finset.mem_of_mem_erase hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi_erase_j).1
    have hik : i ≠ k := (Finset.mem_erase.mp hi).1
    rw [Function.update_of_ne hik, Function.update_of_ne hij]
  rw [hrest_congr]
  ring

/-- For an additively-represented preference, every standard sequence in
coordinate `j` shifts `V j` by the constant `V σ.k σ.s − V σ.k σ.r`. -/
lemma standardSequence_Vj_step
    {P : ProductPref X} {V : (i : ι) → X i → ℝ}
    (hV : AdditivelyRepresents P V)
    {j : ι} (σ : StandardSequence P j) (n : ℕ) :
    V j (σ.α (n + 1)) - V j (σ.α n) = V σ.k σ.r - V σ.k σ.s := by
  -- The indifference at step `n` becomes equality of additive sums.
  have hsp := σ.spaced n
  have heq :
      (∑ i, V i (Function.update (Function.update σ.base j (σ.α n)) σ.k σ.r i)) =
      (∑ i, V i (Function.update (Function.update σ.base j (σ.α (n+1))) σ.k σ.s i)) := by
    have hwk := (hV
        (Function.update (Function.update σ.base j (σ.α n)) σ.k σ.r)
        (Function.update (Function.update σ.base j (σ.α (n+1))) σ.k σ.s)).mp hsp.1
    have hwk' := (hV
        (Function.update (Function.update σ.base j (σ.α (n+1))) σ.k σ.s)
        (Function.update (Function.update σ.base j (σ.α n)) σ.k σ.r)).mp hsp.2
    linarith
  rw [sum_V_two_coord_split V σ.base j σ.k σ.k_ne_j (σ.α n) σ.r,
      sum_V_two_coord_split V σ.base j σ.k σ.k_ne_j (σ.α (n+1)) σ.s] at heq
  linarith

/-- **Necessity of the Archimedean axiom.**  If `P` is additively
represented by real-valued coordinate utilities, then every coordinate
satisfies the Wakker Archimedean axiom: no strict standard sequence
can be `≽`-bounded by a `lo, hi` pair of profiles. -/
theorem archimedean_of_additivelyRepresents
    {P : ProductPref X} {V : (i : ι) → X i → ℝ}
    (hV : AdditivelyRepresents P V)
    (j : ι) :
    Archimedean P j := by
  intro σ hσ
  rintro ⟨lo, hi, hbound⟩
  -- Per-step shift of `V j` along the standard sequence.
  set Δ : ℝ := V σ.k σ.r - V σ.k σ.s with hΔ_def
  have hstep : ∀ n, V j (σ.α (n + 1)) - V j (σ.α n) = Δ := by
    intro n
    have := standardSequence_Vj_step hV σ n
    simpa [hΔ_def] using this
  -- `V j (σ.α n) = V j (σ.α 0) + n * Δ`.
  have harith : ∀ n,
      V j (σ.α n) = V j (σ.α 0) + (n : ℝ) * Δ := by
    intro n; induction n with
    | zero => simp
    | succ k ih =>
        have h1 := hstep k
        have hk_eq : V j (σ.α (k+1)) = V j (σ.α k) + Δ := by linarith
        rw [hk_eq, ih]; push_cast; ring
  -- Strictness: `V j (σ.α 0) > V j (σ.α 1)`, i.e. `Δ < 0`.
  have hΔ_neg : Δ < 0 := by
    have hle : V j (σ.α 1) ≤ V j (σ.α 0) :=
      (coordPref_iff_of_additivelyRepresents hV j σ.base (σ.α 0) (σ.α 1)).mp hσ.1
    have hnot : ¬ V j (σ.α 0) ≤ V j (σ.α 1) := by
      intro hcontra
      apply hσ.2
      exact (coordPref_iff_of_additivelyRepresents hV j σ.base (σ.α 1) (σ.α 0)).mpr hcontra
    have hlt : V j (σ.α 1) < V j (σ.α 0) := lt_of_le_of_ne hle (fun heq => hnot heq.ge)
    have h0 := hstep 0
    -- `V j (σ.α 1) - V j (σ.α 0) = Δ`, so `Δ = V j (σ.α 1) - V j (σ.α 0) < 0`.
    have : Δ = V j (σ.α 1) - V j (σ.α 0) := by linarith
    linarith
  -- Numeric bracket from `hbound n`.
  have hbound_num : ∀ n,
      (∑ i, V i (lo i))
        ≤ V j (σ.α n) + ∑ i ∈ Finset.univ.erase j, V i (σ.base i)
      ∧ V j (σ.α n) + ∑ i ∈ Finset.univ.erase j, V i (σ.base i)
        ≤ ∑ i, V i (hi i) := by
    intro n
    obtain ⟨h_hi, h_lo⟩ := hbound n
    have h1 := (hV hi (Function.update σ.base j (σ.α n))).mp h_hi
    have h2 := (hV (Function.update σ.base j (σ.α n)) lo).mp h_lo
    rw [sum_V_update_eq_update V σ.base j (σ.α n)] at h1 h2
    exact ⟨h2, h1⟩
  set C : ℝ := ∑ i ∈ Finset.univ.erase j, V i (σ.base i) with hC_def
  set L : ℝ := ∑ i, V i (lo i) with hL_def
  -- Pick `N` large enough that `V j (σ.α 0) + N * Δ + C < L`, contradicting `hbound`.
  have hposNeg : 0 < -Δ := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((V j (σ.α 0) + C - L) / (-Δ))
  have hN' : (V j (σ.α 0) + C - L) < (N : ℝ) * (-Δ) :=
    (div_lt_iff₀ hposNeg).mp hN
  have hbN := (hbound_num N).1
  rw [harith N] at hbN
  -- `L ≤ V j (σ.α 0) + N * Δ + C`, but `(N : ℝ) * (-Δ) > V j (σ.α 0) + C - L`.
  have : L > V j (σ.α 0) + (N : ℝ) * Δ + C := by linarith
  linarith

/-! ### §11.6  Necessity of the certificate's structural axioms

Bundling the four forward-direction theorems above gives the full
"necessity" half of Wakker IV.2.7: every certificate-witnessed
preference satisfies the seven structural axioms (modulo the
analytic-solvability hypothesis on `V`, which is automatic when
`X j = ℝ` and `V j` is continuous and surjective on its image). -/

/-- **Necessity bundle.**  Every additively-representable preference
satisfies weak order, tradeoff consistency, the Archimedean axiom in
every coordinate, and (under analytic solvability of each `V j`)
restricted solvability. -/
theorem certificate_necessity_bundle
    {P : ProductPref X}
    (hCert : WakkerConstructionCertificate P)
    (hsolv :
      ∀ V : (i : ι) → X i → ℝ, AdditivelyRepresents P V →
        ∀ j, CoordUtilitySolvability V j) :
    IsWeakOrder P ∧
    TradeoffConsistency P ∧
    (∀ j, Archimedean P j) ∧
    RestrictedSolvability P := by
  obtain ⟨V, hV⟩ := hCert
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isWeakOrder_of_additivelyRepresents hV
  · exact tradeoffConsistency_of_additivelyRepresents hV
  · exact fun j => archimedean_of_additivelyRepresents hV j
  · exact restrictedSolvability_of_additivelyRepresents hV (hsolv V hV)

end ProductPref

end WakkerInfra
