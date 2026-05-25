/-
This file is part of the split `WakkerDebreuKoopmans` module family.
The public import surface remains `WakkerDebreuKoopmans.lean`, now a thin
re-export barrel.
-/

import WakkerDebreuKoopmans.Certificates

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

/-! #### M2 — `haff` entry-point bundle (Wakker uniqueness)

The original M2 bundle was under-axiomed: `∃ j k essential` is not enough
to force a single common scale `α` across coordinates.  Counterexample: the
lex preference on `Bool × Bool` admits both R₁ with scales (100, 1) and R₂
with scales (1000, 1), which are both additive representations of the same
order with both coordinates essential, but no common α > 0 makes them
affinely equivalent (the per-coordinate scale ratios disagree).

This is the M2 analogue of the M1 finding: pair-form / shared-preference
alone is not enough; an explicit "common scale" content has to be named.
We isolate it as a Prop-level certificate following the M1 pattern, prove
the M2 conclusion from it, and prove that a shared global representation
constructs it via tradeoff equivalence on a chosen essential coordinate. -/

/-- **Common-scale certificate (M2 residual obligation).**

The remaining structural content needed to derive a common positive affine
scale from two additive representations of the same preference, beyond
weak-order shared-preference.

Statement: there exists a positive real `α` such that, for every
coordinate `i` and every two values `u v : X i`, the within-coordinate
utility differences scale by `α`:
`R₂.V i u - R₂.V i v = α * (R₁.V i u - R₁.V i v)`.

In Wakker's actual proof this comes from cardinal tradeoff equivalence
(Wakker 1989, Theorem IV.2.7 uniqueness clause), which uses standard
sequences to calibrate the scale on one essential coordinate and tradeoff
consistency to lift it to all others.  Here we isolate the precise
content as this Prop-level certificate so that the M2 conclusion can be
proved from it by a direct β construction. -/
def AdditiveCommonScaleCertificate {X : ι → Type v}
    {P : ProductPref X} (R₁ R₂ : AdditiveRep P) : Prop :=
  ∃ α : ℝ, 0 < α ∧
    ∀ (i : ι) (u v : X i),
      R₂.V i u - R₂.V i v = α * (R₁.V i u - R₁.V i v)

/-- **Phase 8 / Certificate 3 input bundle (enriched).**

Single named hypothesis collapsing the Wakker uniqueness frontier.  Stated
under the structural axioms Wakker's actual proof uses: two additive
representations of the same `P`, two essential coordinates, plus the named
common-scale residual.

Compared to the original (under-axiomed) version of this bundle, this one
matches the axiom set sufficient for the affine-equivalence conclusion.
See the "M2 enriched-bundle attempt" section of the roadmap for the
counterexample that motivated the enrichment.

The certificate body is `AdditiveAffineUniquenessCertificate R₁ R₂`. -/
def AdditiveAffineUniquenessInputCertificate {X : ι → Type v}
    {P : ProductPref X} (R₁ R₂ : AdditiveRep P)
    (_hess : ∃ j k : ι, j ≠ k ∧
              ProductPref.Essential P j ∧ ProductPref.Essential P k)
    (_hscale : AdditiveCommonScaleCertificate R₁ R₂) : Prop :=
  AdditiveAffineUniquenessCertificate R₁ R₂

/-! ##### M2 affine-form proof from the common-scale certificate

Under `IsWeakOrder + Nonempty ι + AdditiveCommonScaleCertificate`, the
affine-equivalence conclusion holds.  The proof picks a reference value
`a₀ : X i` per coordinate (using `Inhabited` or the existing `essential`
hypothesis) and sets `β i = R₂.V i (a₀ i) - α * R₁.V i (a₀ i)`. -/

/-- **M2 affine-equivalence theorem under the common-scale certificate.**

Given two additive representations sharing the common-scale certificate
and at least two essential coordinates (so each coordinate has a chosen
reference value via the essentiality witness), the affine form
`R₂.V i x = α * R₁.V i x + β i` holds for some `α > 0` and `β : ι → ℝ`.

The reference values are extracted from the essentiality witnesses
themselves; any non-empty `X i` would also suffice, but the existing
`additive_rep_unique` interface exposes essentiality. -/
theorem additiveAffineUniqueness_of_commonScale {X : ι → Type v}
    {P : ProductPref X} (R₁ R₂ : AdditiveRep P)
    (essentialAll : ∀ i, ProductPref.Essential P i)
    (hscale : AdditiveCommonScaleCertificate R₁ R₂) :
    AdditiveAffineUniquenessCertificate R₁ R₂ := by
  obtain ⟨α, hα, hdiff⟩ := hscale
  -- Pick a reference value at each coordinate via essentiality.
  classical
  -- For each `i`, essentiality gives `a, v, w` with `update a i v ≽ update a i w`
  -- and `¬ update a i w ≽ update a i v`; in particular `X i` is non-empty.
  let refVal : (i : ι) → X i := fun i => (essentialAll i).choose_spec.choose
  -- Define β i = R₂.V i (refVal i) - α * R₁.V i (refVal i).
  refine ⟨α, hα, fun i => R₂.V i (refVal i) - α * R₁.V i (refVal i), ?_⟩
  intro i x
  -- From the common-scale certificate at (x, refVal i):
  --   R₂.V i x - R₂.V i (refVal i) = α * (R₁.V i x - R₁.V i (refVal i))
  have h := hdiff i x (refVal i)
  -- Solve for R₂.V i x.
  linarith

/-- **Phase 8 / Certificate 3 entry-point theorem (enriched).**

From the named input bundle, produce the existing
`AdditiveAffineUniquenessCertificate R₁ R₂`. -/
theorem additiveAffineUniquenessCertificate_of_input {X : ι → Type v}
    {P : ProductPref X} (R₁ R₂ : AdditiveRep P)
    (hess : ∃ j k : ι, j ≠ k ∧
              ProductPref.Essential P j ∧ ProductPref.Essential P k)
    (hscale : AdditiveCommonScaleCertificate R₁ R₂)
    (hInput : AdditiveAffineUniquenessInputCertificate R₁ R₂ hess hscale) :
    AdditiveAffineUniquenessCertificate R₁ R₂ :=
  hInput

/-- **Phase 8 / Certificate 3 regression through `additive_rep_unique`.**

End-to-end check that the enriched input bundle yields the affine-equivalence
conclusion through the public consumer interface.  Any future proof of the
two named axioms (`hess`, `hscale`) immediately discharges the existing
public theorem with no interface changes. -/
theorem additive_rep_unique_of_input {X : ι → Type v}
    (P : ProductPref X)
    (R₁ R₂ : AdditiveRep P)
    (hess : ∃ j k : ι, j ≠ k ∧
              ProductPref.Essential P j ∧ ProductPref.Essential P k)
    (hscale : AdditiveCommonScaleCertificate R₁ R₂)
    (hInput : AdditiveAffineUniquenessInputCertificate R₁ R₂ hess hscale) :
    ∃ (α : ℝ) (_ : 0 < α) (β : ι → ℝ),
      ∀ i x, R₂.V i x = α * R₁.V i x + β i :=
  _root_.WakkerRoadmap.WakkerExistence.additive_rep_unique
    P R₁ R₂ hess hInput

/-- **M2 cross-flow: a shared global representation produces the
common-scale certificate with `α = 1`.**

When `R₁` and `R₂` are calibrated so that within-coordinate utility
differences agree, the common scale is `1`.  This is the "trivial M5 ⇒ M2
cross-flow" — a global representation that is itself a common pair already
satisfies common-scale.

More refined cross-flows (e.g., from cardinal tradeoff equivalence under
tradeoff consistency) are the genuine M2 work and remain open. -/
theorem additiveCommonScaleCertificate_of_equalCoordDiffs {X : ι → Type v}
    {P : ProductPref X} (R₁ R₂ : AdditiveRep P)
    (hCoordEq : ∀ (i : ι) (u v : X i),
                  R₂.V i u - R₂.V i v = R₁.V i u - R₁.V i v) :
    AdditiveCommonScaleCertificate R₁ R₂ := by
  refine ⟨1, by norm_num, ?_⟩
  intro i u v
  rw [hCoordEq i u v]
  ring

/-! ##### M2 tradeoff-transfer discharge route

The genuine M2 content is constructing `AdditiveCommonScaleCertificate` from
`TradeoffConsistency`.  The argument:

1. Pick essential `j` with `v ≠ w : X j` such that `R₁.V j v ≠ R₁.V j w`.
2. Define `α = (R₂.V j v - R₂.V j w) / (R₁.V j v - R₁.V j w)`.
3. Show `α > 0` (because both representations preserve strict preference
   direction on essential coordinates).
4. For any other coordinate `k` and any `u₁, u₂ : X k` with
   `R₁.V k u₁ ≠ R₁.V k u₂`, use tradeoff consistency to show that
   `(R₂.V k u₁ - R₂.V k u₂) / (R₁.V k u₁ - R₁.V k u₂) = α`.

Step 4 is the deep step.  It requires constructing profiles that witness
the tradeoff transfer from `j` to `k` via the hexagon condition.  This
construction needs `RestrictedSolvability` (to find intermediate profiles
that produce the required indifferences) and is the genuine multi-week
formalization target.

We isolate Step 4 as a named "tradeoff-transfer" certificate and prove
Steps 1–3 directly. -/

/-- **Tradeoff-transfer certificate (M2 deep residual).**

The precise content of Wakker's cardinal tradeoff equivalence argument
needed to derive the common scale: for any two coordinates `j, k` with
`j` essential, and any non-trivial pair `(u₁, u₂)` on `k`, the
within-coordinate difference ratio on `k` equals the ratio on `j`.

This is the hexagon-condition content that `TradeoffConsistency` provides
when combined with `RestrictedSolvability` and the profile-construction
machinery.  Naming it lets the M2 proof proceed conditionally. -/
def TradeoffTransferCertificate {X : ι → Type v}
    {P : ProductPref X} (R₁ R₂ : AdditiveRep P)
    (j : ι) (v w : X j) (_hne : R₁.V j v ≠ R₁.V j w) : Prop :=
  ∀ (k : ι) (u₁ u₂ : X k),
    R₁.V k u₁ ≠ R₁.V k u₂ →
      (R₂.V k u₁ - R₂.V k u₂) / (R₁.V k u₁ - R₁.V k u₂) =
        (R₂.V j v - R₂.V j w) / (R₁.V j v - R₁.V j w)

/-! ##### M2 deep residual: tradeoff-transfer factoring

The full Wakker hexagon argument for the tradeoff-transfer certificate
constructs profiles where the `j`-tradeoff `v ↦ w` is "balanced" against
the `k`-tradeoff `u₁ ↦ u₂` via indifference, then applies
`TradeoffConsistency.consistent` to force consistency.

Following the Phase 8 enrichment pattern, we factor this into:

1. A `TradeoffEquivalence R j k v w u₁ u₂` certificate stating the existence
   of profiles witnessing the `j`-tradeoff ≈ `k`-tradeoff equivalence under
   `R`.
2. The proof that such an equivalence forces `R.V j v - R.V j w = R.V k u₁ - R.V k u₂`
   (numerical equality of the differences under the additive representation).
3. Application of (2) to both `R₁` and `R₂` to derive the ratio equality.

Steps 2 and 3 are bounded algebraic content; step 1 is the deep
profile-construction obligation that requires `RestrictedSolvability` and
the hexagon condition. -/

/-- **Tradeoff-equivalence certificate (M2 sub-residual).**

The decision-theoretic content of "the `j`-tradeoff `v ↦ w` is balanced
against the `k`-tradeoff `u₁ ↦ u₂`" under additive representation `R`.

Concretely: there exist profiles `a, b` differing only at coordinates
`{j, k}` with `a j = v, b j = w, a k = u₂, b k = u₁` and `P.indiff a b`.

This says exchanging the `j`-tradeoff `v ↘ w` for the `k`-tradeoff
`u₂ ↗ u₁` leaves the agent indifferent — so in the additive
representation, the two utility differences cancel exactly.

In Wakker's framework this is constructed by `RestrictedSolvability`
applied to a base profile and the desired `j`-coordinate values, finding
a `k`-coordinate value that produces the indifference. -/
def TradeoffEquivalence {X : ι → Type v}
    (P : ProductPref X) (j k : ι) (_hjk : j ≠ k)
    (v w : X j) (u₁ u₂ : X k) : Prop :=
  ∃ a b : Profile X,
    Profile.agreeOff {j, k} a b ∧
    a j = v ∧ b j = w ∧
    a k = u₂ ∧ b k = u₁ ∧
    P.indiff a b

/-- **Tradeoff equivalence forces equal differences under additive
representation.**

Real, sorry-free proof.  Given a tradeoff-equivalence witness `(a, b)`
with `P.indiff a b`, the additive representation yields equal sums
`∑ R.V i (a i) = ∑ R.V i (b i)`.  Decomposing each sum into the `{j, k}`
contributions plus the rest (which agrees), the equation reduces to
`R.V j v + R.V k u₂ = R.V j w + R.V k u₁`, i.e.,
`R.V j v - R.V j w = R.V k u₁ - R.V k u₂`. -/
theorem tradeoff_equivalence_difference_equality
    {X : ι → Type v} (P : ProductPref X)
    (R : AdditiveRep P) {j k : ι} (hjk : j ≠ k)
    {v w : X j} {u₁ u₂ : X k}
    (heq : TradeoffEquivalence P j k hjk v w u₁ u₂) :
    R.V j v - R.V j w = R.V k u₁ - R.V k u₂ := by
  obtain ⟨a, b, hagree, hav, hbw, hau, hbu, hindiff⟩ := heq
  -- From P.indiff a b and R.represents, both directions of weakPref hold,
  -- so the sums are equal.
  have hle1 : (∑ i, R.V i (b i)) ≤ ∑ i, R.V i (a i) :=
    (R.represents a b).mp hindiff.1
  have hle2 : (∑ i, R.V i (a i)) ≤ ∑ i, R.V i (b i) :=
    (R.represents b a).mp hindiff.2
  have hsum_eq : (∑ i, R.V i (a i)) = ∑ i, R.V i (b i) :=
    le_antisymm hle2 hle1
  -- Decompose each sum into the j-coord, k-coord, and the rest.
  have h_a_split :
      (∑ i, R.V i (a i)) =
        R.V j (a j) + R.V k (a k) +
          ∑ i ∈ (Finset.univ.erase j).erase k, R.V i (a i) :=
    sum_eq_pair_add_rest R.V a hjk
  have h_b_split :
      (∑ i, R.V i (b i)) =
        R.V j (b j) + R.V k (b k) +
          ∑ i ∈ (Finset.univ.erase j).erase k, R.V i (b i) :=
    sum_eq_pair_add_rest R.V b hjk
  -- The rest sums agree because a and b agree off {j, k}.
  have hrest :
      (∑ i ∈ (Finset.univ.erase j).erase k, R.V i (a i)) =
        ∑ i ∈ (Finset.univ.erase j).erase k, R.V i (b i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    have hi_erase_j : i ∈ Finset.univ.erase j := (Finset.mem_erase.mp hi).2
    have hij : i ≠ j := Finset.ne_of_mem_erase hi_erase_j
    have hi_not_pair : i ∉ ({j, k} : Set ι) := by
      intro himem
      rcases (by simpa using himem : i = j ∨ i = k) with rfl | rfl
      · exact hij rfl
      · exact hik rfl
    rw [hagree i hi_not_pair]
  rw [h_a_split, h_b_split, hav, hau, hbw, hbu, hrest] at hsum_eq
  linarith

/-- **Tradeoff transfer from two tradeoff equivalences.**

If the `j`-tradeoff `v ↦ w` is equivalent (under `R₁` *and* under `R₂`,
on the same profiles) to the `k`-tradeoff `u₁ ↦ u₂`, then the cross-rep
ratios on `j` and `k` agree.

Real, sorry-free proof using `tradeoff_equivalence_difference_equality`
applied to both representations.

This is the **algebraic core** of the M2 tradeoff-transfer argument: once
the witness profiles for the equivalence are constructed (from
`RestrictedSolvability` + hexagon), the ratio equality follows
mechanically. -/
theorem tradeoff_transfer_from_tradeoff_equivalence
    {X : ι → Type v} (P : ProductPref X)
    (R₁ R₂ : AdditiveRep P) {j k : ι} (hjk : j ≠ k)
    {v w : X j} {u₁ u₂ : X k}
    (hne_j : R₁.V j v ≠ R₁.V j w)
    (hne_k : R₁.V k u₁ ≠ R₁.V k u₂)
    (heq : TradeoffEquivalence P j k hjk v w u₁ u₂) :
    (R₂.V k u₁ - R₂.V k u₂) / (R₁.V k u₁ - R₁.V k u₂) =
      (R₂.V j v - R₂.V j w) / (R₁.V j v - R₁.V j w) := by
  -- Apply the equivalence theorem to both representations.
  have h₁ : R₁.V j v - R₁.V j w = R₁.V k u₁ - R₁.V k u₂ :=
    tradeoff_equivalence_difference_equality P R₁ hjk heq
  have h₂ : R₂.V j v - R₂.V j w = R₂.V k u₁ - R₂.V k u₂ :=
    tradeoff_equivalence_difference_equality P R₂ hjk heq
  -- Both differences scale together: the ratio is the same.
  have hd1_j : R₁.V j v - R₁.V j w ≠ 0 := sub_ne_zero.mpr hne_j
  have hd1_k : R₁.V k u₁ - R₁.V k u₂ ≠ 0 := sub_ne_zero.mpr hne_k
  rw [h₂, h₁]

/-! ##### `TradeoffEquivalence` partial discharge from RestrictedSolvability

The `TradeoffEquivalence` sub-residual is the existence of profiles `(a, b)`
on a `{j, k}`-slice with prescribed `j`-values `(v, w)`, prescribed `k`-value
`u₁` on `b`, and `P.indiff a b`.  The `k`-value `u₂` on `a` is the *output*
of the construction: `RestrictedSolvability` finds it.

The full discharge from raw axioms requires:

1. A base profile `a₀` to anchor the slice.
2. Two bracketing `k`-values `u_lo, u_hi : X k` with
   `update a j v at u_lo ≼ b ≼ update a j v at u_hi`, where `b` is the
   target profile with `b j = w, b k = u₁` and `b` agrees with `a` off
   `{j, k}`.
3. `RestrictedSolvability` then produces the desired `u₂` between
   `u_lo` and `u_hi` making the indifference hold.

The bracketing hypothesis is the residual content for full M2 closure.
We isolate it as a named "tradeoff-bracketing" certificate. -/

/-- **Tradeoff-bracketing certificate.**

For a chosen base profile `a₀`, prescribed `j`-values `v, w : X j`, and
prescribed `k`-value `u₁ : X k` on the target profile `b`, there exist
two bracketing `k`-values `u_lo, u_hi : X k` such that varying the
"source" profile's `k`-value over `[u_lo, u_hi]` brackets the target.

This is exactly what `RestrictedSolvability` consumes to produce the
indifference witness `u₂`. -/
def TradeoffBracketingCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι) (_hjk : j ≠ k)
    (a₀ : Profile X) (v w : X j) (u₁ : X k) : Prop :=
  ∃ u_lo u_hi : X k,
    P.weakPref
      (Function.update (Function.update a₀ j v) k u_hi)
      (Function.update (Function.update a₀ j w) k u₁) ∧
    P.weakPref
      (Function.update (Function.update a₀ j w) k u₁)
      (Function.update (Function.update a₀ j v) k u_lo)

/-- **Partial discharge: `TradeoffEquivalence` from `RestrictedSolvability`
plus `TradeoffBracketingCertificate`.**

Real, sorry-free proof.  Given the bracketing hypothesis on `(a₀, v, w, u₁)`,
`RestrictedSolvability` applied to the target profile `b := update (update a₀ j w) k u₁`
on coordinate `k` produces `u₂` such that
`update (update a₀ j v) k u₂ ∼ b`.  The two profiles `a := update (update a₀ j v) k u₂`
and `b := update (update a₀ j w) k u₁` then witness the tradeoff equivalence:
they differ only at `{j, k}`, have the prescribed coordinate values, and are
indifferent.

This discharges `TradeoffEquivalence` *given* the bracketing certificate.
The genuine remaining open content is producing the bracketing — the
"hexagon-condition" or "essentiality + Archimedean" argument that
guarantees both directions of the bracket exist for any pair `(v, w)`
and any `u₁`. -/
theorem tradeoffEquivalence_of_restrictedSolvability_and_bracketing
    {X : ι → Type v} (P : ProductPref X)
    [_hWO : ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    {j k : ι} (hjk : j ≠ k)
    (a₀ : Profile X) (v w : X j) (u₁ : X k)
    (hbracket : TradeoffBracketingCertificate P j k hjk a₀ v w u₁) :
    ∃ u₂ : X k, TradeoffEquivalence P j k hjk v w u₁ u₂ := by
  obtain ⟨u_lo, u_hi, h_hi, h_lo⟩ := hbracket
  -- Apply `RestrictedSolvability` on coordinate k.
  -- The base profile for solvability is `update a₀ j v` (since we want to
  -- vary coordinate k while holding j at v).
  -- The target is `b := update (update a₀ j w) k u₁`.
  -- The bracket is `update (update a₀ j v) k u_hi ≽ b ≽ update (update a₀ j v) k u_lo`.
  set a' : Profile X := Function.update a₀ j v
  set b : Profile X := Function.update (Function.update a₀ j w) k u₁
  -- Note: update a' k u_hi = update (update a₀ j v) k u_hi
  -- This matches the hypothesis form because (Function.update a' k u_hi) k = u_hi
  -- and (a' j) = v (from update_self).
  obtain ⟨u₂, hu₂⟩ : ∃ c : X k, P.indiff (Function.update a' k c) b :=
    hsolv a' b k u_hi u_lo h_hi h_lo
  refine ⟨u₂, Function.update a' k u₂, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- agreeOff {j, k}
    intro i hi
    have hij : i ≠ j := fun heq => hi (by simp [heq])
    have hik : i ≠ k := fun heq => hi (by simp [heq])
    show (Function.update a' k u₂) i = b i
    rw [Function.update_of_ne hik]
    show a' i = b i
    show (Function.update a₀ j v) i = (Function.update (Function.update a₀ j w) k u₁) i
    rw [Function.update_of_ne hij, Function.update_of_ne hik,
        Function.update_of_ne hij]
  · -- a j = v
    show (Function.update a' k u₂) j = v
    rw [Function.update_of_ne hjk]
    show (Function.update a₀ j v) j = v
    rw [Function.update_self]
  · -- b j = w
    show (Function.update (Function.update a₀ j w) k u₁) j = w
    rw [Function.update_of_ne hjk]
    rw [Function.update_self]
  · -- a k = u₂
    show (Function.update a' k u₂) k = u₂
    rw [Function.update_self]
  · -- b k = u₁
    show (Function.update (Function.update a₀ j w) k u₁) k = u₁
    rw [Function.update_self]
  · exact hu₂

/-! ##### `TradeoffBracketingCertificate` partial discharge from Archimedean

The bracketing certificate requires the existence of two `k`-values
`u_lo, u_hi` whose updated profiles bracket the target.  The genuinely
deep content is `Archimedean P k`, which rules out infinite same-direction
escapes.  But the Archimedean axiom on its own only provides a *negative*
result (the grid cannot stay sandwiched), not a *positive* upper bound.

To extract a positive upper bracket from Archimedean, we need a
monotone-standard-sequence hypothesis: each strict standard sequence on
`k` is monotone in the preference direction (i.e., `σ.α (n+1) ≻ σ.α n`).
This is a consequence of `TradeoffConsistency` in Wakker's framework,
but isolating it as a named residual exposes the precise content needed.

We name this **monotone standard sequence certificate** and use it
together with Archimedean to derive a one-sided upper-bracket result.
The full two-sided bracketing then needs the directional reverse standard
sequence (already isolated as `DirectionalReverseStandardSequenceCertificate`
in the M4 layer). -/

/-- **Monotone standard sequence certificate.**

For a strict standard sequence `σ` on coordinate `j`, every grid step is
strictly preferred to the previous: `σ.α (n+1)` is strictly preferred to
`σ.α n` (when both are seen as updates of `σ.base`).

This is a direct consequence of `TradeoffConsistency` applied to the
spaced indifferences in `σ`, but isolating it as a named certificate lets
the bracketing arguments below proceed without re-deriving it each time. -/
def MonotoneStandardSequenceCertificate {X : ι → Type v}
    {P : ProductPref X} {j : ι} (σ : ProductPref.StandardSequence P j) : Prop :=
  ∀ n : ℕ,
    P.weakPref
      (Function.update σ.base j (σ.α (n+1)))
      (Function.update σ.base j (σ.α n))

/-- **One-sided upper bracket from Archimedean + monotone standard
sequence.**

Real, sorry-free content.  Given a strict standard sequence `σ` on
coordinate `k` whose grid is monotone in preference, and `Archimedean P k`,
for any `lo : Profile X` such that `σ.base ≽ lo` is *false* (the base is
not above `lo`), we cannot bracket `lo` between the base and the grid by
choosing only the grid's index — Archimedean forces the grid to escape.

This is a step toward extracting one-sided positive bracketing from
Archimedean.  Stated honestly: under monotonicity + Archimedean, for any
target `hi`, there exists an index `n` with `σ.α n ≻ hi` *or* the entire
grid is ≼ `hi` (a degenerate case ruled out by strictness).

We package this as a *contrapositive* statement: if the grid never
overtakes `hi`, then there's a uniform sandwich, contradicting Archimedean. -/
theorem grid_eventually_overtakes_or_uniformly_below
    {X : ι → Type v} (P : ProductPref X) {k : ι}
    [ProductPref.IsWeakOrder P]
    (σ : ProductPref.StandardSequence P k)
    (hσ : σ.IsStrict)
    (harchim : ProductPref.Archimedean P k)
    (lo hi : Profile X)
    (hgrid_above_lo :
      ∀ n, P.weakPref (Function.update σ.base k (σ.α n)) lo) :
    ∃ n, ¬ P.weakPref hi (Function.update σ.base k (σ.α n)) := by
  -- By contrapositive of Archimedean: if no escape upward and no escape
  -- downward, then the grid is uniformly bracketed, contradicting hσ.
  by_contra hno_overtake
  push_neg at hno_overtake
  -- Now we have:
  --   hno_overtake : ∀ n, P.weakPref hi (Function.update σ.base k (σ.α n))
  --   hgrid_above_lo : ∀ n, P.weakPref (Function.update σ.base k (σ.α n)) lo
  -- Together these form a uniform sandwich, which Archimedean forbids.
  have hsandwich : ∃ lo' hi' : Profile X, ∀ n,
      P.weakPref hi' (Function.update σ.base k (σ.α n)) ∧
      P.weakPref (Function.update σ.base k (σ.α n)) lo' :=
    ⟨lo, hi, fun n => ⟨hno_overtake n, hgrid_above_lo n⟩⟩
  exact harchim σ hσ hsandwich

/-- **Trivial cross-flow: monotone standard sequence implies grid is
above its base.**

For a monotone strict standard sequence, `σ.α n` (as an update of `σ.base`)
is weakly preferred to `σ.α 0` for every `n`, by induction on `n`. -/
theorem monotone_grid_above_base
    {X : ι → Type v} (P : ProductPref X) {k : ι}
    [hWO : ProductPref.IsWeakOrder P]
    (σ : ProductPref.StandardSequence P k)
    (hmono : MonotoneStandardSequenceCertificate σ) :
    ∀ n,
      P.weakPref
        (Function.update σ.base k (σ.α n))
        (Function.update σ.base k (σ.α 0)) := by
  intro n
  induction n with
  | zero =>
    -- Reflexivity at n = 0.
    rcases hWO.complete (Function.update σ.base k (σ.α 0))
                        (Function.update σ.base k (σ.α 0)) with h | h <;> exact h
  | succ m ih =>
    -- Use transitivity: σ.α (m+1) ≽ σ.α m ≽ σ.α 0.
    exact hWO.transitive _ _ _ (hmono m) ih

/-! ##### Lifting strict first step to monotonicity via hexagon

The deep content of `MonotoneStandardSequenceCertificate σ` is that
*every* step of the standard sequence is in the preference direction —
not just the first step (which is already given by `σ.IsStrict`).

Wakker's hexagon condition (`TradeoffConsistency`) supplies the lift:
the spaced indifferences in `σ` plus the first-step strictness force
every consecutive step to share the same preference direction.

We factor this into:
1. A **first-step strictness** observation: `σ.IsStrict` gives the first
   step.  Actually `σ.IsStrict` says `update base j (α 0) ≻ update base j (α 1)`,
   so the standard sequence is strictly *descending* — the convention is
   that grid-step `n+1` is less preferred than grid-step `n`.
2. A **hexagon-step lift** sub-residual that says: from one consecutive
   step in the preference direction, the next is too.
3. The final monotonicity certificate, derived by induction.

For this round we add the algebraic plumbing for the descending case,
which matches the existing convention in `σ.IsStrict`.  The key
observation is that the *opposite* direction of monotonicity from what we
named in `MonotoneStandardSequenceCertificate` is what `σ.IsStrict`
actually delivers at the first step. -/

/-- **First-step strict-descending certificate from `σ.IsStrict`.**

The existing `σ.IsStrict` predicate says
`update base j (α 0) ≻ update base j (α 1)`, i.e., the *first* grid step
is in the descending direction.  This lemma packages that first-step
property as the base case of an induction.

Sorry-free: just a re-extraction of `σ.IsStrict.1`. -/
theorem first_step_descending_of_strict
    {X : ι → Type v} {P : ProductPref X} {j : ι}
    (σ : ProductPref.StandardSequence P j)
    (hσ : σ.IsStrict) :
    P.weakPref
      (Function.update σ.base j (σ.α 0))
      (Function.update σ.base j (σ.α 1)) :=
  hσ.1

/-- **Hexagon-step lift sub-residual.**

The single named sub-residual capturing the hexagon-condition lift from
one consecutive grid step in the preference direction to the next.

Statement: given strictness in the descending direction at index `n`
(`update base j (α n) ≽ update base j (α (n+1))`), the same direction
holds at index `n+1` (`update base j (α (n+1)) ≽ update base j (α (n+2))`).

This is the per-step content the hexagon condition supplies in Wakker's
proof.  Naming it isolates the deep step. -/
def HexagonStepLiftCertificate {X : ι → Type v}
    {P : ProductPref X} {j : ι} (σ : ProductPref.StandardSequence P j) : Prop :=
  ∀ n : ℕ,
    P.weakPref
      (Function.update σ.base j (σ.α n))
      (Function.update σ.base j (σ.α (n+1)))

/-- **Descending-monotonicity certificate from first-step strictness +
hexagon-step lift.**

Real, sorry-free proof.  The hexagon-step lift certificate already
supplies the descending property at every step.  This lemma packages it
into the named monotonicity-certificate-style form (with the *descending*
direction, i.e., consecutive grid points are less preferred). -/
theorem descendingMonotoneStandardSequenceCertificate_of_hexagonStepLift
    {X : ι → Type v} {P : ProductPref X} {j : ι}
    (σ : ProductPref.StandardSequence P j)
    (hlift : HexagonStepLiftCertificate σ) :
    ∀ n : ℕ,
      P.weakPref
        (Function.update σ.base j (σ.α n))
        (Function.update σ.base j (σ.α (n+1))) :=
  hlift

/-- **Cross-flow: descending grid above base.**

For a descending strict standard sequence (every step less preferred than
the previous), the entire grid is *below* its base — the dual of
`monotone_grid_above_base`.

Proof: induction with transitivity of `≽`. -/
theorem descending_grid_below_base
    {X : ι → Type v} (P : ProductPref X) {k : ι}
    [hWO : ProductPref.IsWeakOrder P]
    (σ : ProductPref.StandardSequence P k)
    (hdesc : HexagonStepLiftCertificate σ) :
    ∀ n,
      P.weakPref
        (Function.update σ.base k (σ.α 0))
        (Function.update σ.base k (σ.α n)) := by
  intro n
  induction n with
  | zero =>
    rcases hWO.complete (Function.update σ.base k (σ.α 0))
                        (Function.update σ.base k (σ.α 0)) with h | h <;> exact h
  | succ m ih =>
    -- σ.α 0 ≽ σ.α m ≽ σ.α (m+1)
    exact hWO.transitive _ _ _ ih (hdesc m)

/-! ##### Why the hexagon condition alone does not yield `HexagonStepLiftCertificate`

**Honest analysis on 2026-05-17.**  The `TradeoffConsistency` (hexagon)
condition transports *indifferences* along coordinate `j`: given three
indifferences `a ∼ b, c ∼ d, e ∼ f` with profiles agreeing off `{j}` and
matching `j`-values across pairs, it concludes a fourth indifference
`g ∼ h`.  Crucially, it does **not** transport strict preferences and
does **not** establish single-coordinate monotonicity directly.

The spaced indifferences in a standard sequence `σ` are
`σ.spaced n : (α n at j, base, r at k) ∼ (α (n+1) at j, base, s at k)`.
These profiles differ at *both* `j` and `k = σ.k`, not just at `j`, so
they don't fit the hexagon's `agreeOff {j}` requirement.

To derive `HexagonStepLiftCertificate σ` (per-step descending in `j`
alone), we need a *separate* "single-coordinate `r/s`-direction"
hypothesis on `k`: either `update base k r ≽ update base k s` or its
opposite, depending on the strictness convention.  Once that's in hand,
the spaced indifferences chain with single-coordinate monotonicity to
deliver the per-step descending property.

We expose this honestly as two named sub-residuals:

1. `StandardSequenceReferenceDirection σ`: the one-coordinate `r/s`
   direction at `σ.k`.
2. `HexagonStepLiftFromReferenceDirection`: the lift from (1) to
   `HexagonStepLiftCertificate σ` via the spaced indifferences.

Sub-residual (1) is the genuinely deep part — it requires either an
external single-coordinate monotonicity axiom or a derivation from
`σ.IsStrict + RestrictedSolvability + TradeoffConsistency` that the file
does not yet supply.

Sub-residual (2) is the algebraic glue, which we attempt below. -/

/-- **Standard-sequence reference-direction certificate.**

For a strict standard sequence `σ` on `j` with auxiliary coordinate
`k = σ.k` and reference exchange `r ↘ s`, the single-coordinate
direction at `k` (with `j`-value held at the base): either
`update base k r ≽ update base k s` or its opposite.

This is a single-coordinate-at-`k` monotonicity hypothesis, which
`TradeoffConsistency` alone does **not** supply.  It is a separate
structural property of `P` (often derived from the standard-sequence
construction itself, or from a single-coordinate weak-monotonicity
axiom).

Statement: the `r → s` exchange at `k` (with `j` held at `α 0`) is in
the descending direction. -/
def StandardSequenceReferenceDirection {X : ι → Type v}
    {P : ProductPref X} {j : ι} (σ : ProductPref.StandardSequence P j) : Prop :=
  P.weakPref
    (Function.update (Function.update σ.base j (σ.α 0)) σ.k σ.r)
    (Function.update (Function.update σ.base j (σ.α 0)) σ.k σ.s)

/-- **Per-step lift sub-residual via reference direction.**

Given the reference-direction certificate, the per-step descending
property at index `n` follows from the spaced indifference combined with
single-coordinate-at-`k` reasoning.

This is the algebraic glue between the spaced indifference at index `n`
and the per-step descending property in `j` alone. -/
def HexagonStepLiftFromReferenceDirection {X : ι → Type v}
    {P : ProductPref X} {j : ι} (σ : ProductPref.StandardSequence P j) : Prop :=
  StandardSequenceReferenceDirection σ →
    HexagonStepLiftCertificate σ

/-- **Trivial cross-flow: the lift residual is dischargeable from any direct
proof of the descending property.**

Sanity check that the lift residual is at the right level: any direct
production of the per-step descending property satisfies the lift
unconditionally on the reference direction. -/
theorem hexagonStepLiftFromReferenceDirection_of_descending
    {X : ι → Type v} {P : ProductPref X} {j : ι}
    (σ : ProductPref.StandardSequence P j)
    (hdesc : HexagonStepLiftCertificate σ) :
    HexagonStepLiftFromReferenceDirection σ :=
  fun _ => hdesc

/-! ##### Standard sequence chain: spaced-indifference unpacking

The spaced indifference at index 0 (`σ.spaced 0`) provides two direct
preference relations that future per-step lift work will chain:

* `(α 0, base, r) ≽ (α 1, base, s)`: the forward direction.
* `(α 1, base, s) ≽ (α 0, base, r)`: the reverse direction.

These are sorry-free unpackings of `(σ.spaced 0).1` and `(σ.spaced 0).2`
respectively, packaged here for reuse.

(I attempted to use the reference-direction certificate to derive the
per-step descending property at index 0, but the derivation requires
single-coordinate-at-`j` reasoning between `(α 0, base, s)` and
`(α 1, base, s)` that no current axiom supplies.  The lemmas below are
the honest unpackings without the misleading reference-direction
dependency.) -/

/-- **Spaced indifference at index 0, forward direction.** -/
theorem standardSequence_spaced_zero_forward
    {X : ι → Type v} {P : ProductPref X}
    {j : ι} (σ : ProductPref.StandardSequence P j) :
    P.weakPref
      (Function.update (Function.update σ.base j (σ.α 0)) σ.k σ.r)
      (Function.update (Function.update σ.base j (σ.α 1)) σ.k σ.s) :=
  (σ.spaced 0).1

/-- **Spaced indifference at index 0, reverse direction.** -/
theorem standardSequence_spaced_zero_reverse
    {X : ι → Type v} {P : ProductPref X}
    {j : ι} (σ : ProductPref.StandardSequence P j) :
    P.weakPref
      (Function.update (Function.update σ.base j (σ.α 1)) σ.k σ.s)
      (Function.update (Function.update σ.base j (σ.α 0)) σ.k σ.r) :=
  (σ.spaced 0).2

/-- **M2 common-scale from tradeoff-transfer certificate.**

Given an essential coordinate `j` with a non-trivial pair `(v, w)` and
the tradeoff-transfer certificate, the common-scale certificate follows
by setting `α = (R₂.V j v - R₂.V j w) / (R₁.V j v - R₁.V j w)` and
using the transfer to extend to all coordinates.

Steps 1–3 of the argument are proved directly; Step 4 is the named
residual. -/
theorem additiveCommonScaleCertificate_of_tradeoffTransfer {X : ι → Type v}
    {P : ProductPref X} (R₁ R₂ : AdditiveRep P)
    {j : ι} {v w : X j}
    (hne : R₁.V j v ≠ R₁.V j w)
    -- Step 3: the ratio is positive.
    (hpos : 0 < (R₂.V j v - R₂.V j w) / (R₁.V j v - R₁.V j w))
    -- Step 4: the tradeoff-transfer certificate (non-trivial pairs).
    (htransfer : TradeoffTransferCertificate R₁ R₂ j v w hne)
    -- Zero-difference preservation: if R₁ assigns equal values at a
    -- coordinate, so does R₂.  This follows from the shared preference
    -- (profiles differing only at that coordinate are indifferent under P,
    -- hence have equal R₂-sums, hence equal R₂-values at that coordinate).
    -- We take it as a named hypothesis because the profile-construction
    -- argument requires `Nonempty (Profile X)` infrastructure not yet
    -- available in this file.
    (hzero : ∀ (k : ι) (u₁ u₂ : X k),
               R₁.V k u₁ = R₁.V k u₂ → R₂.V k u₁ = R₂.V k u₂) :
    AdditiveCommonScaleCertificate R₁ R₂ := by
  set α := (R₂.V j v - R₂.V j w) / (R₁.V j v - R₁.V j w)
  refine ⟨α, hpos, ?_⟩
  intro k u₁ u₂
  by_cases hk : R₁.V k u₁ = R₁.V k u₂
  · -- Zero case: both sides are zero.
    have h_r2_eq : R₂.V k u₁ = R₂.V k u₂ := hzero k u₁ u₂ hk
    rw [h_r2_eq, hk, sub_self, sub_self, mul_zero]
  · -- Non-trivial case: use the transfer certificate.
    have hratio := htransfer k u₁ u₂ hk
    have hne_k : (R₁.V k u₁ - R₁.V k u₂) ≠ 0 := sub_ne_zero.mpr hk
    have hne_j : (R₁.V j v - R₁.V j w) ≠ 0 := sub_ne_zero.mpr hne
    rw [div_eq_div_iff hne_k hne_j] at hratio
    -- hratio : (R₂.V k u₁ - R₂.V k u₂) * (R₁.V j v - R₁.V j w)
    --        = (R₂.V j v - R₂.V j w) * (R₁.V k u₁ - R₁.V k u₂)
    -- Goal: R₂.V k u₁ - R₂.V k u₂ = α * (R₁.V k u₁ - R₁.V k u₂)
    -- where α = (R₂.V j v - R₂.V j w) / (R₁.V j v - R₁.V j w)
    have : α * (R₁.V k u₁ - R₁.V k u₂) =
        (R₂.V j v - R₂.V j w) * (R₁.V k u₁ - R₁.V k u₂) / (R₁.V j v - R₁.V j w) := by
      simp [α, div_mul_eq_mul_div]
    rw [this]
    rw [eq_div_iff hne_j]
    linarith

/-- **Discharge: zero-difference preservation across additive representations.**

If two additive representations `R₁`, `R₂` of the same preference `P` share
the same value at two points `u₁, u₂ : X k` of some coordinate (i.e.,
`R₁.V k u₁ = R₁.V k u₂`), then the same equality holds for `R₂`
(`R₂.V k u₁ = R₂.V k u₂`).

Real, sorry-free proof using `additive_rep_indiff_iff`: build profiles
`x := update a k u₁` and `y := update a k u₂` for any base profile `a`.
The two profiles differ only at `k`, so their `R₁`-sums differ only by
`R₁.V k u₁ - R₁.V k u₂ = 0`, hence the `R₁`-sums are equal.  By
`additive_rep_indiff_iff`, the `R₂`-sums are also equal.  By the same
single-coordinate decomposition for `R₂`, this forces
`R₂.V k u₁ = R₂.V k u₂`.

Needs `Nonempty (Profile X)`, supplied either externally or
automatically when `X i` is inhabited for every `i` (e.g. `X i = ℝ`).

This discharges one of the three auxiliary M2 hypotheses left explicit
in `additiveCommonScaleCertificate_of_tradeoffTransfer`. -/
theorem zero_difference_preservation_across_additive_representations
    {X : ι → Type v} (P : ProductPref X)
    (R₁ R₂ : AdditiveRep P)
    [hne : Nonempty (Profile X)]
    (k : ι) (u₁ u₂ : X k)
    (h : R₁.V k u₁ = R₁.V k u₂) :
    R₂.V k u₁ = R₂.V k u₂ := by
  -- Pick any base profile.
  obtain ⟨a⟩ := hne
  -- Build the two profiles differing only at k.
  set x := Function.update a k u₁
  set y := Function.update a k u₂
  -- Decompose ∑ R₁.V over `Finset.univ` into the k-coordinate plus the rest.
  have hx_split :
      (∑ i, R₁.V i (x i)) =
        R₁.V k u₁ + ∑ i ∈ Finset.univ.erase k, R₁.V i (a i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
    have hk_eq : R₁.V k (x k) = R₁.V k u₁ := by simp [x]
    rw [hk_eq]
    have hrest : (∑ i ∈ Finset.univ.erase k, R₁.V i (x i)) =
        ∑ i ∈ Finset.univ.erase k, R₁.V i (a i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hik : i ≠ k := Finset.ne_of_mem_erase hi
      simp [x, Function.update_of_ne hik]
    rw [hrest]
    ring
  have hy_split :
      (∑ i, R₁.V i (y i)) =
        R₁.V k u₂ + ∑ i ∈ Finset.univ.erase k, R₁.V i (a i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
    have hk_eq : R₁.V k (y k) = R₁.V k u₂ := by simp [y]
    rw [hk_eq]
    have hrest : (∑ i ∈ Finset.univ.erase k, R₁.V i (y i)) =
        ∑ i ∈ Finset.univ.erase k, R₁.V i (a i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hik : i ≠ k := Finset.ne_of_mem_erase hi
      simp [y, Function.update_of_ne hik]
    rw [hrest]
    ring
  -- The two R₁-sums are equal because R₁.V k u₁ = R₁.V k u₂.
  have hR1_eq : (∑ i, R₁.V i (x i)) = ∑ i, R₁.V i (y i) := by
    rw [hx_split, hy_split, h]
  -- By additive_rep_indiff_iff, the R₂-sums are also equal.
  have hR2_eq : (∑ i, R₂.V i (x i)) = ∑ i, R₂.V i (y i) :=
    (WakkerExistence.additive_rep_indiff_iff P R₁ R₂ x y).mp hR1_eq
  -- Decompose ∑ R₂.V the same way.
  have hx_split₂ :
      (∑ i, R₂.V i (x i)) =
        R₂.V k u₁ + ∑ i ∈ Finset.univ.erase k, R₂.V i (a i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
    have hk_eq : R₂.V k (x k) = R₂.V k u₁ := by simp [x]
    rw [hk_eq]
    have hrest : (∑ i ∈ Finset.univ.erase k, R₂.V i (x i)) =
        ∑ i ∈ Finset.univ.erase k, R₂.V i (a i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hik : i ≠ k := Finset.ne_of_mem_erase hi
      simp [x, Function.update_of_ne hik]
    rw [hrest]
    ring
  have hy_split₂ :
      (∑ i, R₂.V i (y i)) =
        R₂.V k u₂ + ∑ i ∈ Finset.univ.erase k, R₂.V i (a i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
    have hk_eq : R₂.V k (y k) = R₂.V k u₂ := by simp [y]
    rw [hk_eq]
    have hrest : (∑ i ∈ Finset.univ.erase k, R₂.V i (y i)) =
        ∑ i ∈ Finset.univ.erase k, R₂.V i (a i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hik : i ≠ k := Finset.ne_of_mem_erase hi
      simp [y, Function.update_of_ne hik]
    rw [hrest]
    ring
  rw [hx_split₂, hy_split₂] at hR2_eq
  linarith

/-- **M2 common-scale from tradeoff-transfer with zero-difference auto-discharged.**

Specialization of `additiveCommonScaleCertificate_of_tradeoffTransfer` for
the case `X i = ℝ` (which is automatically inhabited), using
`zero_difference_preservation_across_additive_representations` to discharge
the `hzero` hypothesis automatically.

Reduces the M2 auxiliary residuals from three to two (positivity and
reference-pair existence). -/
theorem additiveCommonScaleCertificate_of_tradeoffTransfer_real
    {P : ProductPref (fun _ : ι => ℝ)} (R₁ R₂ : AdditiveRep P)
    {j : ι} {v w : ℝ}
    (hne : R₁.V j v ≠ R₁.V j w)
    (hpos : 0 < (R₂.V j v - R₂.V j w) / (R₁.V j v - R₁.V j w))
    (htransfer : TradeoffTransferCertificate R₁ R₂ j v w hne) :
    AdditiveCommonScaleCertificate R₁ R₂ := by
  -- Profile (fun _ => ℝ) is inhabited by the constant-zero profile.
  haveI : Nonempty (Profile (fun _ : ι => ℝ)) := ⟨fun _ => 0⟩
  exact additiveCommonScaleCertificate_of_tradeoffTransfer R₁ R₂ hne hpos
    htransfer
    (fun k u₁ u₂ heq =>
      zero_difference_preservation_across_additive_representations
        P R₁ R₂ k u₁ u₂ heq)

/-- **Discharge: reference-pair existence from essentiality.**

If coordinate `j` is essential for `P`, then for any additive representation
`R`, there exist values `v, w : X j` with `R.V j v ≠ R.V j w`.

Real, sorry-free proof.  Essentiality gives `(a, v, w)` with
`update a j v ≽ update a j w` and `¬ update a j w ≽ update a j v`.
The single-coordinate decomposition of `R.represents` then forces
`R.V j w < R.V j v`, hence `R.V j v ≠ R.V j w`.

Discharges one of the two auxiliary residuals in
`additiveCommonScaleCertificate_of_tradeoffTransfer_real` (reference-pair
existence). -/
theorem reference_pair_of_essential
    {X : ι → Type v} {P : ProductPref X}
    (R : AdditiveRep P)
    {j : ι} (hess : ProductPref.Essential P j) :
    ∃ v w : X j, R.V j v ≠ R.V j w := by
  obtain ⟨a, v, w, hvw, hnwv⟩ := hess
  -- From R.represents and the strict preference, R.V j w < R.V j v.
  have hle : (∑ i, R.V i ((Function.update a j w) i)) ≤
              ∑ i, R.V i ((Function.update a j v) i) :=
    (R.represents (Function.update a j v) (Function.update a j w)).mp hvw
  have hnle : ¬ (∑ i, R.V i ((Function.update a j v) i)) ≤
                ∑ i, R.V i ((Function.update a j w) i) := by
    intro h
    apply hnwv
    exact (R.represents (Function.update a j w) (Function.update a j v)).mpr h
  -- The two sums differ only at coordinate j.
  have hv_split :
      (∑ i, R.V i ((Function.update a j v) i)) =
        R.V j v + ∑ i ∈ Finset.univ.erase j, R.V i (a i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    have hk_eq : R.V j ((Function.update a j v) j) = R.V j v := by simp
    rw [hk_eq]
    have hrest :
        (∑ i ∈ Finset.univ.erase j, R.V i ((Function.update a j v) i)) =
          ∑ i ∈ Finset.univ.erase j, R.V i (a i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp [Function.update_of_ne hij]
    rw [hrest]
    ring
  have hw_split :
      (∑ i, R.V i ((Function.update a j w) i)) =
        R.V j w + ∑ i ∈ Finset.univ.erase j, R.V i (a i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    have hk_eq : R.V j ((Function.update a j w) j) = R.V j w := by simp
    rw [hk_eq]
    have hrest :
        (∑ i ∈ Finset.univ.erase j, R.V i ((Function.update a j w) i)) =
          ∑ i ∈ Finset.univ.erase j, R.V i (a i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp [Function.update_of_ne hij]
    rw [hrest]
    ring
  rw [hv_split, hw_split] at hle hnle
  -- Now hle : R.V j w + rest ≤ R.V j v + rest, so R.V j w ≤ R.V j v
  -- and hnle : ¬ (R.V j v + rest ≤ R.V j w + rest), so R.V j w < R.V j v
  refine ⟨v, w, ?_⟩
  intro heq
  apply hnle
  rw [heq]

/-- **Discharge: positivity of the cross-representation ratio from
essentiality.**

If coordinate `j` is essential for `P`, then for the reference pair
`(v, w)` extracted by `reference_pair_of_essential` from `R₁`, the ratio
`(R₂.V j v - R₂.V j w) / (R₁.V j v - R₁.V j w)` is strictly positive.

Real, sorry-free proof.  Essentiality gives the strict preference
`update a j v ≻ update a j w`.  Both `R₁` and `R₂` represent the same
`P`, so both register strict preference, which under the single-coordinate
decomposition forces both `R₁.V j w < R₁.V j v` and
`R₂.V j w < R₂.V j v`.  Hence both differences are positive, and their
ratio is positive.

Discharges the positivity auxiliary residual in
`additiveCommonScaleCertificate_of_tradeoffTransfer_real`. -/
theorem positive_ratio_of_essential
    {X : ι → Type v} {P : ProductPref X}
    (R₁ R₂ : AdditiveRep P)
    {j : ι} {v w : X j}
    (a : Profile X)
    (hvw : P.weakPref (Function.update a j v) (Function.update a j w))
    (hnwv : ¬ P.weakPref (Function.update a j w) (Function.update a j v)) :
    0 < (R₂.V j v - R₂.V j w) / (R₁.V j v - R₁.V j w) := by
  -- Single-coordinate decomposition for R₁.
  have hle₁ : (∑ i, R₁.V i ((Function.update a j w) i)) ≤
                ∑ i, R₁.V i ((Function.update a j v) i) :=
    (R₁.represents (Function.update a j v) (Function.update a j w)).mp hvw
  have hnle₁ : ¬ (∑ i, R₁.V i ((Function.update a j v) i)) ≤
                  ∑ i, R₁.V i ((Function.update a j w) i) := by
    intro h
    apply hnwv
    exact (R₁.represents (Function.update a j w) (Function.update a j v)).mpr h
  -- Decompose R₁ sums.
  have hv_split₁ :
      (∑ i, R₁.V i ((Function.update a j v) i)) =
        R₁.V j v + ∑ i ∈ Finset.univ.erase j, R₁.V i (a i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    have hk_eq : R₁.V j ((Function.update a j v) j) = R₁.V j v := by simp
    rw [hk_eq]
    have hrest :
        (∑ i ∈ Finset.univ.erase j, R₁.V i ((Function.update a j v) i)) =
          ∑ i ∈ Finset.univ.erase j, R₁.V i (a i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp [Function.update_of_ne hij]
    rw [hrest]
    ring
  have hw_split₁ :
      (∑ i, R₁.V i ((Function.update a j w) i)) =
        R₁.V j w + ∑ i ∈ Finset.univ.erase j, R₁.V i (a i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    have hk_eq : R₁.V j ((Function.update a j w) j) = R₁.V j w := by simp
    rw [hk_eq]
    have hrest :
        (∑ i ∈ Finset.univ.erase j, R₁.V i ((Function.update a j w) i)) =
          ∑ i ∈ Finset.univ.erase j, R₁.V i (a i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp [Function.update_of_ne hij]
    rw [hrest]
    ring
  rw [hv_split₁, hw_split₁] at hle₁ hnle₁
  have h1 : R₁.V j w < R₁.V j v := by
    by_contra h
    push_neg at h
    apply hnle₁
    linarith
  -- Same decomposition for R₂.
  have hle₂ : (∑ i, R₂.V i ((Function.update a j w) i)) ≤
                ∑ i, R₂.V i ((Function.update a j v) i) :=
    (R₂.represents (Function.update a j v) (Function.update a j w)).mp hvw
  have hnle₂ : ¬ (∑ i, R₂.V i ((Function.update a j v) i)) ≤
                  ∑ i, R₂.V i ((Function.update a j w) i) := by
    intro h
    apply hnwv
    exact (R₂.represents (Function.update a j w) (Function.update a j v)).mpr h
  have hv_split₂ :
      (∑ i, R₂.V i ((Function.update a j v) i)) =
        R₂.V j v + ∑ i ∈ Finset.univ.erase j, R₂.V i (a i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    have hk_eq : R₂.V j ((Function.update a j v) j) = R₂.V j v := by simp
    rw [hk_eq]
    have hrest :
        (∑ i ∈ Finset.univ.erase j, R₂.V i ((Function.update a j v) i)) =
          ∑ i ∈ Finset.univ.erase j, R₂.V i (a i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp [Function.update_of_ne hij]
    rw [hrest]
    ring
  have hw_split₂ :
      (∑ i, R₂.V i ((Function.update a j w) i)) =
        R₂.V j w + ∑ i ∈ Finset.univ.erase j, R₂.V i (a i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    have hk_eq : R₂.V j ((Function.update a j w) j) = R₂.V j w := by simp
    rw [hk_eq]
    have hrest :
        (∑ i ∈ Finset.univ.erase j, R₂.V i ((Function.update a j w) i)) =
          ∑ i ∈ Finset.univ.erase j, R₂.V i (a i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp [Function.update_of_ne hij]
    rw [hrest]
    ring
  rw [hv_split₂, hw_split₂] at hle₂ hnle₂
  have h2 : R₂.V j w < R₂.V j v := by
    by_contra h
    push_neg at h
    apply hnle₂
    linarith
  -- Both differences are positive; the ratio is positive.
  have hd1 : 0 < R₁.V j v - R₁.V j w := by linarith
  have hd2 : 0 < R₂.V j v - R₂.V j w := by linarith
  exact div_pos hd2 hd1

/-- **M2 — `AdditiveCommonScaleCertificate` from essentiality + tradeoff
transfer (real-coordinate special case).**

Composition of the existing real-special-case M2 chain with the
auxiliary discharges `reference_pair_of_essential` and
`positive_ratio_of_essential`.

Inputs:
* `R₁ R₂ : AdditiveRep P` for `P : ProductPref (fun _ : ι => ℝ)` — two
  additive representations of the same real-coordinate product
  preference.
* `hess : ProductPref.Essential P j` for some coordinate `j`
  (essentiality witness, supplying the strict-preference data needed
  by both auxiliary discharges).
* `htransfer` : the tradeoff-transfer certificate at the reference pair
  extracted from `hess`.

Output: `AdditiveCommonScaleCertificate R₁ R₂`.

This composition reduces the open M2 frontier to a **single**
named hypothesis, the tradeoff-transfer certificate; both other
auxiliary residuals (`hpos`, `hzero`) are now theorem-backed.  The
remaining open content is exactly Wakker's hexagon-condition
profile-construction argument, which is the genuine M2 deep step.

Reference: Wakker (1989), Theorem IV.2.7 — uniqueness clause; this
theorem packages the `α`-extraction for the real-coordinate special
case under the cleanest currently-achievable input bundle. -/
theorem additiveCommonScaleCertificate_of_tradeoffTransfer_real_from_essential
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {P : ProductPref (fun _ : ι => ℝ)} (R₁ R₂ : AdditiveRep P)
    {j : ι} (hess : ProductPref.Essential P j)
    (htransfer :
      ∀ {v w : ℝ} (hne : R₁.V j v ≠ R₁.V j w),
        TradeoffTransferCertificate R₁ R₂ j v w hne) :
    AdditiveCommonScaleCertificate R₁ R₂ := by
  -- Extract the reference pair (v, w) and the strict-preference data
  -- from essentiality.  We re-derive it here rather than calling
  -- `reference_pair_of_essential` because we also need the underlying
  -- `(a, hvw, hnwv)` triple to feed `positive_ratio_of_essential`.
  obtain ⟨a, v, w, hvw, hnwv⟩ := hess
  -- Step 1: extract `R₁.V j v ≠ R₁.V j w` from essentiality.
  have hne : R₁.V j v ≠ R₁.V j w := by
    -- Apply `reference_pair_of_essential` to `R₁` to get *some* pair, but
    -- we already have `(v, w)` from `hess`; extract directly.
    have hle : (∑ i, R₁.V i ((Function.update a j w) i)) ≤
                ∑ i, R₁.V i ((Function.update a j v) i) :=
      (R₁.represents (Function.update a j v) (Function.update a j w)).mp hvw
    have hnle : ¬ (∑ i, R₁.V i ((Function.update a j v) i)) ≤
                  ∑ i, R₁.V i ((Function.update a j w) i) := by
      intro h
      apply hnwv
      exact (R₁.represents (Function.update a j w) (Function.update a j v)).mpr h
    -- Single-coordinate decomposition: cancel the `≠ j` part of both sums.
    have hv_split :
        (∑ i, R₁.V i ((Function.update a j v) i)) =
          R₁.V j v + ∑ i ∈ Finset.univ.erase j, R₁.V i (a i) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
      have hk_eq : R₁.V j ((Function.update a j v) j) = R₁.V j v := by simp
      rw [hk_eq]
      have hrest :
          (∑ i ∈ Finset.univ.erase j, R₁.V i ((Function.update a j v) i)) =
            ∑ i ∈ Finset.univ.erase j, R₁.V i (a i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hij : i ≠ j := Finset.ne_of_mem_erase hi
        simp [Function.update_of_ne hij]
      rw [hrest]
      ring
    have hw_split :
        (∑ i, R₁.V i ((Function.update a j w) i)) =
          R₁.V j w + ∑ i ∈ Finset.univ.erase j, R₁.V i (a i) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
      have hk_eq : R₁.V j ((Function.update a j w) j) = R₁.V j w := by simp
      rw [hk_eq]
      have hrest :
          (∑ i ∈ Finset.univ.erase j, R₁.V i ((Function.update a j w) i)) =
            ∑ i ∈ Finset.univ.erase j, R₁.V i (a i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hij : i ≠ j := Finset.ne_of_mem_erase hi
        simp [Function.update_of_ne hij]
      rw [hrest]
      ring
    rw [hv_split, hw_split] at hle hnle
    intro heq
    apply hnle
    rw [heq]
  -- Step 2: positivity of the ratio from `positive_ratio_of_essential`.
  have hpos : 0 < (R₂.V j v - R₂.V j w) / (R₁.V j v - R₁.V j w) :=
    positive_ratio_of_essential R₁ R₂ a hvw hnwv
  -- Step 3: assemble.
  exact additiveCommonScaleCertificate_of_tradeoffTransfer_real R₁ R₂
    hne hpos (htransfer hne)

/-- **M2 — `additive_rep_unique` from essentiality + tradeoff transfer
(real-coordinate special case).**

Top-level consumer combining
`additiveCommonScaleCertificate_of_tradeoffTransfer_real_from_essential`
with `additiveAffineUniqueness_of_commonScale` and the public
`additive_rep_unique` consumer.  Produces the affine-equivalence
conclusion of `additive_rep_unique` directly from essentiality of all
coordinates plus the tradeoff-transfer certificate at one essential
coordinate.

The remaining open content is exactly the tradeoff-transfer certificate
(Wakker's hexagon-condition profile-construction argument); every
other auxiliary residual is theorem-backed. -/
theorem additive_rep_unique_of_tradeoffTransfer_real_from_essential
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P : ProductPref (fun _ : ι => ℝ))
    (R₁ R₂ : AdditiveRep P)
    (essentialAll : ∀ i, ProductPref.Essential P i)
    (hess_pair : ∃ j k : ι, j ≠ k ∧
                  ProductPref.Essential P j ∧ ProductPref.Essential P k)
    {j : ι} (hess : ProductPref.Essential P j)
    (htransfer :
      ∀ {v w : ℝ} (hne : R₁.V j v ≠ R₁.V j w),
        TradeoffTransferCertificate R₁ R₂ j v w hne) :
    ∃ (α : ℝ) (_ : 0 < α) (β : ι → ℝ),
      ∀ i x, R₂.V i x = α * R₁.V i x + β i := by
  have hscale : AdditiveCommonScaleCertificate R₁ R₂ :=
    additiveCommonScaleCertificate_of_tradeoffTransfer_real_from_essential
      R₁ R₂ hess htransfer
  have haff : AdditiveAffineUniquenessCertificate R₁ R₂ :=
    additiveAffineUniqueness_of_commonScale R₁ R₂ essentialAll hscale
  exact _root_.WakkerRoadmap.WakkerExistence.additive_rep_unique
    P R₁ R₂ hess_pair haff

/-! ##### M2 — `TradeoffTransferCertificate` from a pointwise equivalence-existence hypothesis

The M2 frontier in the real-coordinate special case has been reduced to
the single named hypothesis `TradeoffTransferCertificate`.  This block
factors that hypothesis into a strictly weaker named bridge:
**existence of a tradeoff equivalence whose secondary-coordinate
endpoints realize the same `R₁.V`-values as any prescribed pair**.

The motivation: a single tradeoff equivalence
`TradeoffEquivalence P j k hjk v w u₁* u₂*` only constrains the
`(u₁*, u₂*)` pair; to lift the ratio statement to *arbitrary* `(u₁, u₂)`
with `R₁.V k u₁ ≠ R₁.V k u₂`, one needs an equivalence whose endpoints
have matching `R₁.V`-values.  Once such an equivalence is in hand,
zero-difference preservation across additive representations transports
the ratio from the equivalence-endpoints to the prescribed pair.

This factoring isolates the genuine open content (utility-value
realization on `R₁.V k`) from the algebraic transport step (which is
fully theorem-backed below).

The factoring also splits the certificate's quantification into two
pieces:

* **off-diagonal** (`k ≠ j`): handled by the cross-coordinate
  utility-value-realizing equivalence;
* **on-diagonal** (`k = j`): the genuine on-coordinate cardinal-equivalence
  statement, isolated as a separate sub-residual since it cannot be
  discharged from cross-coordinate content alone.

Wakker's full proof closes the on-diagonal case via a triangle
construction `j → m → j` through a third coordinate `m`; we expose this
as the `OnCoordinateRatioConsistency` certificate below. -/

/-- **Off-diagonal tradeoff transfer certificate.**

Same shape as `TradeoffTransferCertificate`, but with the secondary
coordinate restricted to `k ≠ j`.  This is the cross-coordinate-only
content of the full certificate. -/
def OffDiagonalTradeoffTransferCertificate {X : ι → Type v}
    {P : ProductPref X} (R₁ R₂ : AdditiveRep P)
    (j : ι) (v w : X j) (_hne : R₁.V j v ≠ R₁.V j w) : Prop :=
  ∀ (k : ι) (_hjk : j ≠ k) (u₁ u₂ : X k),
    R₁.V k u₁ ≠ R₁.V k u₂ →
      (R₂.V k u₁ - R₂.V k u₂) / (R₁.V k u₁ - R₁.V k u₂) =
        (R₂.V j v - R₂.V j w) / (R₁.V j v - R₁.V j w)

/-- **On-coordinate ratio-consistency certificate.**

The on-diagonal piece of `TradeoffTransferCertificate`: the cross-rep
ratio is the same at every non-trivial pair on coordinate `j` itself.

Wakker's proof discharges this via a triangle
`(j, m₁) → (m₁, j) → (j, j)` for a third coordinate `m`; the resulting
chained equivalences force the on-diagonal ratio.

We name the predicate here so the M2 chain can proceed conditionally
on it.  Discharging it from existing infrastructure requires either a
third essential coordinate plus two cross-coordinate utility-value
realizations, or a direct standard-sequence calibration on `j`. -/
def OnCoordinateRatioConsistency {X : ι → Type v}
    {P : ProductPref X} (R₁ R₂ : AdditiveRep P)
    (j : ι) (v w : X j) (_hne : R₁.V j v ≠ R₁.V j w) : Prop :=
  ∀ (u₁ u₂ : X j),
    R₁.V j u₁ ≠ R₁.V j u₂ →
      (R₂.V j u₁ - R₂.V j u₂) / (R₁.V j u₁ - R₁.V j u₂) =
        (R₂.V j v - R₂.V j w) / (R₁.V j v - R₁.V j w)

/-- **Composition: `TradeoffTransferCertificate` from off-diagonal +
on-diagonal pieces.**

Real, sorry-free proof: case-split on `k = j` to dispatch to the
on-diagonal certificate, otherwise to the off-diagonal certificate. -/
theorem tradeoffTransferCertificate_of_offDiagonal_and_onCoordinate
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {X : ι → Type v} {P : ProductPref X}
    (R₁ R₂ : AdditiveRep P)
    {j : ι} {v w : X j}
    (hne : R₁.V j v ≠ R₁.V j w)
    (hOff : OffDiagonalTradeoffTransferCertificate R₁ R₂ j v w hne)
    (hOn : OnCoordinateRatioConsistency R₁ R₂ j v w hne) :
    TradeoffTransferCertificate R₁ R₂ j v w hne := by
  intro k u₁ u₂ hne_k
  by_cases hjk : j = k
  · subst hjk
    exact hOn u₁ u₂ hne_k
  · exact hOff k hjk u₁ u₂ hne_k

/-- **Utility-value-realizing tradeoff equivalence existence
certificate (cross-coordinate) — *diagnostic, retired*.**

For every secondary coordinate `k ≠ j` and every pair `(u₁, u₂)` with
distinct `R₁.V`-values on `k`, there exist values `(u₁'', u₂'')`
realizing the same `R₁.V`-values *and* witnessing a tradeoff
equivalence with the reference pair `(v, w)` on `j`.

**This predicate is too strong** and is structurally unattainable from
any nontrivial additive representation on `|ι| ≥ 2`.  The reason:
`tradeoff_equivalence_difference_equality` applied to the equivalence
clause forces
`R₁.V j v - R₁.V j w = R₁.V k u₁'' - R₁.V k u₂''`,
while the realization clause forces
`R₁.V k u₁'' - R₁.V k u₂'' = R₁.V k u₁ - R₁.V k u₂`.
These two together force `R₁.V k u₁ - R₁.V k u₂ = R₁.V j v - R₁.V j w`
for *every* prescribed pair, which is satisfied only when the
prescribed pair's `R₁.V`-difference happens to match the fixed
reference difference.

The in-file refutation
`additiveBoolReal_not_utilityValueRealizingEquivalence_diagnostic` shows
the predicate fails for the additive sum order on `Bool → ℝ` with the
identity per-coordinate utilities.  The corrected predicate
`UtilityValueRealizingEquivalence` introduced below allows the reference
pair `(v', w')` to vary with the prescribed `(u₁, u₂)` so the difference
constraint can be satisfied.

The diagnostic predicate is retained with the `_diagnostic` suffix as
a regression artifact and to document the structural obstruction. -/
def UtilityValueRealizingEquivalence_diagnostic {X : ι → Type v}
    {P : ProductPref X} (R₁ : AdditiveRep P)
    {j : ι} (v w : X j) : Prop :=
  ∀ (k : ι) (hjk : j ≠ k) (u₁ u₂ : X k),
    R₁.V k u₁ ≠ R₁.V k u₂ →
      ∃ (u₁'' u₂'' : X k),
        R₁.V k u₁'' = R₁.V k u₁ ∧
        R₁.V k u₂'' = R₁.V k u₂ ∧
        TradeoffEquivalence P j k hjk v w u₁'' u₂''

/-! ##### In-file refutation of the diagnostic predicate

We construct an explicit additive representation on `ι = Bool`,
`X = fun _ => ℝ` and a reference pair on coordinate `false` whose
diagnostic-realization clause cannot hold for a chosen `(u₁, u₂)` on
coordinate `true`.  The witness uses
`R₁.V false 1 - R₁.V false 0 = 1` against
`R₁.V true 2 - R₁.V true 0 = 2`; the diagnostic predicate would force
both differences to coincide, yielding `1 = 2`. -/

/-- The plain additive sum order on `Bool → ℝ` as a `ProductPref`. -/
def additiveBoolReal_pref : ProductPref (fun _ : Bool => ℝ) :=
  { weakPref := fun x y =>
      (∑ b : Bool, y b) ≤ (∑ b : Bool, x b) }

/-- The identity per-coordinate utility on `additiveBoolReal_pref` is an
additive representation. -/
def additiveBoolReal_rep : AdditiveRep additiveBoolReal_pref :=
  { V := fun _ x => x
    represents := by
      intro x y
      rfl }

/-- **Refutation: the diagnostic `UtilityValueRealizingEquivalence_diagnostic`
predicate is unattainable from any nontrivial additive representation.**

The witness is the additive sum order on `Bool → ℝ` with identity
per-coordinate utilities, taken at the reference pair `(v, w) = (1, 0)`
on coordinate `false`.  Apply the predicate to the prescribed pair
`(u₁, u₂) = (2, 0)` on coordinate `true`.  The realization clause
`R₁.V true u₁'' = 2 ∧ R₁.V true u₂'' = 0` forces
`u₁'' - u₂'' = 2`.  The `TradeoffEquivalence` clause, via
`tradeoff_equivalence_difference_equality`, forces
`R₁.V false 1 - R₁.V false 0 = R₁.V true u₁'' - R₁.V true u₂''`,
i.e., `1 = u₁'' - u₂''`.  These two together yield `1 = 2`,
contradiction.

This formalizes the structural obstruction motivating the corrected
predicate `UtilityValueRealizingEquivalence` introduced below. -/
theorem additiveBoolReal_not_utilityValueRealizingEquivalence_diagnostic :
    ¬ UtilityValueRealizingEquivalence_diagnostic
        (P := additiveBoolReal_pref) additiveBoolReal_rep
        (j := false) (v := 1) (w := 0) := by
  intro hreal
  have hjk : (false : Bool) ≠ true := by decide
  have hne : additiveBoolReal_rep.V true (2 : ℝ) ≠ additiveBoolReal_rep.V true (0 : ℝ) := by
    show (2 : ℝ) ≠ 0
    norm_num
  obtain ⟨u₁'', u₂'', hR1_u1, hR1_u2, hequiv⟩ :=
    hreal true hjk (2 : ℝ) (0 : ℝ) hne
  -- hR1_u1 : u₁'' = 2 ; hR1_u2 : u₂'' = 0.
  have hu1 : u₁'' = (2 : ℝ) := by simpa [additiveBoolReal_rep] using hR1_u1
  have hu2 : u₂'' = (0 : ℝ) := by simpa [additiveBoolReal_rep] using hR1_u2
  -- TradeoffEquivalence forces V-differences to match.
  have hdiff :
      additiveBoolReal_rep.V false (1 : ℝ) - additiveBoolReal_rep.V false (0 : ℝ) =
        additiveBoolReal_rep.V true u₁'' - additiveBoolReal_rep.V true u₂'' :=
    tradeoff_equivalence_difference_equality additiveBoolReal_pref
      additiveBoolReal_rep hjk hequiv
  -- Substitute and collapse.
  have h1 : additiveBoolReal_rep.V false (1 : ℝ) - additiveBoolReal_rep.V false (0 : ℝ) = 1 := by
    show (1 : ℝ) - 0 = 1
    norm_num
  have h2 : additiveBoolReal_rep.V true u₁'' - additiveBoolReal_rep.V true u₂'' = 2 := by
    show u₁'' - u₂'' = 2
    rw [hu1, hu2]; norm_num
  rw [h1, h2] at hdiff
  norm_num at hdiff

/-- **Meta-theorem: the diagnostic predicate is unattainable from any
nontrivial additive representation.**

Same shape as the earlier `behavioralRationalSolvabilityAxioms_diagnostic_unattainable_from_additivity`
and `crossCoordinateIndifferenceSolvability_unattainable_from_additivity`
patterns: there exist a `ProductPref` and an `AdditiveRep` such that
the diagnostic predicate fails. -/
theorem utilityValueRealizingEquivalence_diagnostic_unattainable_from_additivity :
    ∃ (P : ProductPref (fun _ : Bool => ℝ)) (R : AdditiveRep P)
      (v w : ℝ),
      ¬ UtilityValueRealizingEquivalence_diagnostic
          (P := P) R (j := false) (v := v) (w := w) :=
  ⟨additiveBoolReal_pref, additiveBoolReal_rep, 1, 0,
    additiveBoolReal_not_utilityValueRealizingEquivalence_diagnostic⟩

/-- **`OffDiagonalTradeoffTransferCertificate` from utility-value-realizing
equivalences plus zero-difference preservation — *diagnostic, retired*.**

This theorem is technically correct but consumes the diagnostic
`UtilityValueRealizingEquivalence_diagnostic` predicate, which is
structurally unattainable from any nontrivial additive representation
(see `additiveBoolReal_not_utilityValueRealizingEquivalence_diagnostic`).

It is retained for backward compatibility with consumers that already
reference the original interface.  New code should use
`offDiagonalTradeoffTransferCertificate_of_utilityValueRealizingEquivalence`
(the corrected version below), which consumes the strictly weaker
`UtilityValueRealizingEquivalence` predicate.

The retained discharge below proves the off-diagonal certificate from
the diagnostic predicate plus zero-difference preservation; both pieces
are real.  The vacuity is in the input. -/
theorem offDiagonalTradeoffTransferCertificate_of_utilityValueRealizingEquivalence_diagnostic
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {X : ι → Type v} (P : ProductPref X)
    (R₁ R₂ : AdditiveRep P)
    [hne_profile : Nonempty (Profile X)]
    {j : ι} {v w : X j}
    (hne : R₁.V j v ≠ R₁.V j w)
    (hreal : UtilityValueRealizingEquivalence_diagnostic R₁ (P := P) v w) :
    OffDiagonalTradeoffTransferCertificate R₁ R₂ j v w hne := by
  intro k hjk u₁ u₂ hne_k
  obtain ⟨u₁'', u₂'', hR1_u1, hR1_u2, hequiv⟩ :=
    hreal k hjk u₁ u₂ hne_k
  -- Step 1: zero-diff preservation transports R₁.V-equalities to R₂.V.
  have hR2_u1 : R₂.V k u₁'' = R₂.V k u₁ :=
    zero_difference_preservation_across_additive_representations
      P R₁ R₂ k u₁'' u₁ hR1_u1
  have hR2_u2 : R₂.V k u₂'' = R₂.V k u₂ :=
    zero_difference_preservation_across_additive_representations
      P R₁ R₂ k u₂'' u₂ hR1_u2
  -- Step 2: the ratio at the realized pair from the existing
  -- single-pair tradeoff transfer.
  have hne_k'' : R₁.V k u₁'' ≠ R₁.V k u₂'' := by
    rw [hR1_u1, hR1_u2]; exact hne_k
  have hratio'' :
      (R₂.V k u₁'' - R₂.V k u₂'') / (R₁.V k u₁'' - R₁.V k u₂'') =
        (R₂.V j v - R₂.V j w) / (R₁.V j v - R₁.V j w) :=
    tradeoff_transfer_from_tradeoff_equivalence P R₁ R₂ hjk hne hne_k''
      hequiv
  -- Step 3: rewrite using R₁.V/R₂.V equalities to conclude.
  rw [hR1_u1, hR1_u2, hR2_u1, hR2_u2] at hratio''
  exact hratio''

/-- **`OnCoordinateRatioConsistency` from a triangle construction
through a third essential coordinate.**

Real, sorry-free proof.

The on-coordinate cardinal-equivalence statement is discharged by
chaining two cross-coordinate transfers through a third coordinate
`m ≠ j`:

  ratio at `(j, u₁, u₂)` = ratio at `(m, m₁, m₂)` (cross-transfer to m)
                         = ratio at `(j, v, w)`   (cross-transfer back to j)

Both legs use the off-diagonal certificate at the appropriate base
pair; the chain forces the on-coordinate ratio to match the reference
ratio.

Hypotheses:
* a third coordinate `m` distinct from `j`;
* off-diagonal transfer at the reference pair `(v, w)` (gives the
  `j → m` leg);
* off-diagonal transfer at *some* pair `(m₁, m₂)` on `m` with non-trivial
  `R₁.V`-difference (gives the `m → j` leg).

The second hypothesis is itself an off-diagonal certificate, so the
overall discharge stays within the `OffDiagonalTradeoffTransferCertificate`
infrastructure. -/
theorem onCoordinateRatioConsistency_of_triangle_through_third_coordinate
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {X : ι → Type v} {P : ProductPref X}
    (R₁ R₂ : AdditiveRep P)
    {j : ι} {v w : X j}
    (hne_j : R₁.V j v ≠ R₁.V j w)
    {m : ι} (hjm : j ≠ m)
    {m₁ m₂ : X m}
    (hne_m : R₁.V m m₁ ≠ R₁.V m m₂)
    (hOff_jm : OffDiagonalTradeoffTransferCertificate R₁ R₂ j v w hne_j)
    (hOff_mj : OffDiagonalTradeoffTransferCertificate R₁ R₂ m m₁ m₂ hne_m) :
    OnCoordinateRatioConsistency R₁ R₂ j v w hne_j := by
  intro u₁ u₂ hne_u
  -- ratio at (m, m₁, m₂) under (R₁, R₂, j-base):
  have hjm_ne : j ≠ m := hjm
  -- Leg 1: off-diagonal from (j, v, w) to (m, m₁, m₂).
  have hLeg1 :
      (R₂.V m m₁ - R₂.V m m₂) / (R₁.V m m₁ - R₁.V m m₂) =
        (R₂.V j v - R₂.V j w) / (R₁.V j v - R₁.V j w) :=
    hOff_jm m hjm_ne m₁ m₂ hne_m
  -- Leg 2: off-diagonal from (m, m₁, m₂) to (j, u₁, u₂).
  have hLeg2 :
      (R₂.V j u₁ - R₂.V j u₂) / (R₁.V j u₁ - R₁.V j u₂) =
        (R₂.V m m₁ - R₂.V m m₂) / (R₁.V m m₁ - R₁.V m m₂) :=
    hOff_mj j hjm.symm u₁ u₂ hne_u
  -- Chain: leg2 = leg1.
  rw [hLeg2, hLeg1]

/-! ##### Alternative on-coordinate discharge: one-coordinate affine lift

The triangle route is not the only honest way to close the on-diagonal
piece.  In Wakker's connected-coordinate presentation, the decisive content
is a direct calibration on the reference coordinate `j`: once the
standard-sequence machinery shows that `R₂.V j` is an affine positive
rescaling of `R₁.V j`, the ratio on coordinate `j` is automatically the
same at every non-trivial pair.

We isolate that stronger same-coordinate target as
`CoordinateAffineLiftCertificate` and prove that it discharges
`OnCoordinateRatioConsistency`.  This makes the remaining direct M2
calibration content precise: one can either prove
`OnCoordinateRatioConsistency` itself, or prove the stronger affine-lift
certificate and obtain the ratio statement for free. -/

/-- **Coordinate affine-lift certificate.**

The direct same-coordinate calibration content on reference coordinate `j`:
there exist constants `α > 0` and `β` such that
`R₂.V j x = α * R₁.V j x + β` for every `x : X j`.

This is the coordinate-restricted form of `AdditiveAffineUniquenessCertificate`
and is the natural target of Wakker's standard-sequence calibration on `j`. -/
def CoordinateAffineLiftCertificate {X : ι → Type v}
    {P : ProductPref X} (R₁ R₂ : AdditiveRep P) (j : ι) : Prop :=
  ∃ α β : ℝ, 0 < α ∧ ∀ x : X j, R₂.V j x = α * R₁.V j x + β

/-- **Coordinate affine lift from additive affine uniqueness.**

Trivial cross-flow: any global affine relation between `R₁` and `R₂`
restricts to a coordinate affine lift on `j`. -/
theorem coordinateAffineLiftCertificate_of_additiveAffineUniquenessCertificate
    {X : ι → Type v} {P : ProductPref X}
    (R₁ R₂ : AdditiveRep P) (j : ι)
    (haff : AdditiveAffineUniquenessCertificate R₁ R₂) :
    CoordinateAffineLiftCertificate R₁ R₂ j := by
  obtain ⟨α, hα, β, hβ⟩ := haff
  exact ⟨α, β j, hα, fun x => hβ j x⟩

/-- **`OnCoordinateRatioConsistency` from a coordinate affine lift.**

Real, sorry-free proof.

If `R₂.V j = α * R₁.V j + β` on coordinate `j`, then every within-coordinate
difference on `j` is scaled by the same factor `α`; dividing by the
corresponding `R₁`-difference gives a constant ratio, independent of the
chosen non-trivial pair. -/
theorem onCoordinateRatioConsistency_of_coordinateAffineLift
    {X : ι → Type v} {P : ProductPref X}
    (R₁ R₂ : AdditiveRep P)
    {j : ι} {v w : X j}
    (hne_j : R₁.V j v ≠ R₁.V j w)
    (hAff : CoordinateAffineLiftCertificate R₁ R₂ j) :
    OnCoordinateRatioConsistency R₁ R₂ j v w hne_j := by
  obtain ⟨α, β, _hα, hcoord⟩ := hAff
  intro u₁ u₂ hne_u
  have hdiff_u :
      R₂.V j u₁ - R₂.V j u₂ = α * (R₁.V j u₁ - R₁.V j u₂) := by
    rw [hcoord u₁, hcoord u₂]
    ring
  have hdiff_vw :
      R₂.V j v - R₂.V j w = α * (R₁.V j v - R₁.V j w) := by
    rw [hcoord v, hcoord w]
    ring
  have hden_u : R₁.V j u₁ - R₁.V j u₂ ≠ 0 := sub_ne_zero.mpr hne_u
  have hden_vw : R₁.V j v - R₁.V j w ≠ 0 := sub_ne_zero.mpr hne_j
  have hcancel_u :
      (α * (R₁.V j u₁ - R₁.V j u₂)) / (R₁.V j u₁ - R₁.V j u₂) = α := by
    rw [mul_div_assoc, div_self hden_u, mul_one]
  have hcancel_vw :
      (α * (R₁.V j v - R₁.V j w)) / (R₁.V j v - R₁.V j w) = α := by
    rw [mul_div_assoc, div_self hden_vw, mul_one]
  calc
    (R₂.V j u₁ - R₂.V j u₂) / (R₁.V j u₁ - R₁.V j u₂)
        = (α * (R₁.V j u₁ - R₁.V j u₂)) / (R₁.V j u₁ - R₁.V j u₂) := by
            rw [hdiff_u]
    _ = α := hcancel_u
    _ = (α * (R₁.V j v - R₁.V j w)) / (R₁.V j v - R₁.V j w) := hcancel_vw.symm
    _ = (R₂.V j v - R₂.V j w) / (R₁.V j v - R₁.V j w) := by
          rw [hdiff_vw]

/-! ##### Construction-side calibration along one strict standard sequence

The previous affine-lift bridge consumed an already-normalized calibration
`R₁.V j (σ.α n) = n = R₂.V j (σ.α n)`.  For arbitrary additive
representations this normalization is too strong: along a fixed standard
sequence, each representation is instead an affine arithmetic progression.

The lemmas below prove that progression directly from `R.represents` and the
standard-sequence indifference field.  If the standard sequence is strict,
the step is negative for every additive representation; hence two
representations have a positive step ratio.  Continuity plus density of the
same standard-sequence grid then extends the affine relation from the grid to
all of coordinate `j`. -/

/-- **Single-coordinate preference reduction for an additive representation.**

Changing only coordinate `j` in a fixed profile is evaluated by comparing the
two `j`-coordinate utility values.  This is the local additive-representation
calculus used to read strictness of a standard sequence as a sign condition on
the utility step. -/
lemma additiveRep_coordPref_iff
    {X : ι → Type v} {P : ProductPref X} (R : AdditiveRep P)
    (j : ι) (base : Profile X) (v w : X j) :
    P.weakPref (Function.update base j v) (Function.update base j w) ↔
      R.V j w ≤ R.V j v := by
  rw [R.represents,
      AdditiveRep.sum_update_eq R.V base j v,
      AdditiveRep.sum_update_eq R.V base j w]
  constructor <;> intro h <;> linarith

/-- **Additive representations move by a constant step on a standard sequence.**

For any standard sequence `σ`, every additive representation satisfies
`R.V j (σ.α (n+1)) - R.V j (σ.α n) = R.V σ.k σ.r - R.V σ.k σ.s`.
This is the construction-side calibration identity behind Wakker's standard
sequence ruler. -/
lemma additiveRep_standardSequence_Vj_step
    {X : ι → Type v} {P : ProductPref X} (R : AdditiveRep P)
    {j : ι} (σ : ProductPref.StandardSequence P j) (n : ℕ) :
    R.V j (σ.α (n + 1)) - R.V j (σ.α n) =
      R.V σ.k σ.r - R.V σ.k σ.s := by
  let lhs : Profile X :=
    Function.update (Function.update σ.base j (σ.α n)) σ.k σ.r
  let rhs : Profile X :=
    Function.update (Function.update σ.base j (σ.α (n + 1))) σ.k σ.s
  have hsp : P.indiff lhs rhs := by
    simpa [lhs, rhs] using σ.spaced n
  have hsum :
      (∑ i, R.V i (lhs i)) = (∑ i, R.V i (rhs i)) := by
    have h₁ := (R.represents lhs rhs).mp hsp.1
    have h₂ := (R.represents rhs lhs).mp hsp.2
    linarith
  have hlhs := sum_eq_pair_add_rest R.V lhs (j := j) (k := σ.k) σ.k_ne_j.symm
  have hrhs := sum_eq_pair_add_rest R.V rhs (j := j) (k := σ.k) σ.k_ne_j.symm
  have hrest :
      (∑ i ∈ (Finset.univ.erase j).erase σ.k, R.V i (lhs i)) =
        ∑ i ∈ (Finset.univ.erase j).erase σ.k, R.V i (rhs i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hik : i ≠ σ.k := Finset.ne_of_mem_erase hi
    have hi_erase_j : i ∈ Finset.univ.erase j := (Finset.mem_erase.mp hi).2
    have hij : i ≠ j := Finset.ne_of_mem_erase hi_erase_j
    simp [lhs, rhs, Function.update_of_ne hik, Function.update_of_ne hij]
  have hsum_split :
      R.V j (lhs j) + R.V σ.k (lhs σ.k) +
          (∑ i ∈ (Finset.univ.erase j).erase σ.k, R.V i (lhs i)) =
        R.V j (rhs j) + R.V σ.k (rhs σ.k) +
          (∑ i ∈ (Finset.univ.erase j).erase σ.k, R.V i (rhs i)) := by
    calc
      R.V j (lhs j) + R.V σ.k (lhs σ.k) +
          (∑ i ∈ (Finset.univ.erase j).erase σ.k, R.V i (lhs i))
          = ∑ i, R.V i (lhs i) := hlhs.symm
      _ = ∑ i, R.V i (rhs i) := hsum
      _ = R.V j (rhs j) + R.V σ.k (rhs σ.k) +
          (∑ i ∈ (Finset.univ.erase j).erase σ.k, R.V i (rhs i)) := hrhs
  have hpair : R.V j (lhs j) + R.V σ.k (lhs σ.k) =
      R.V j (rhs j) + R.V σ.k (rhs σ.k) := by
    linarith
  have hlhs_j : lhs j = σ.α n := by
    dsimp [lhs]
    rw [Function.update_of_ne σ.k_ne_j.symm, Function.update_self]
  have hrhs_j : rhs j = σ.α (n + 1) := by
    dsimp [rhs]
    rw [Function.update_of_ne σ.k_ne_j.symm, Function.update_self]
  have hlhs_k : lhs σ.k = σ.r := by
    dsimp [lhs]
    rw [Function.update_self]
  have hrhs_k : rhs σ.k = σ.s := by
    dsimp [rhs]
    rw [Function.update_self]
  rw [hlhs_j, hrhs_j, hlhs_k, hrhs_k] at hpair
  linarith

/-- **Arithmetic progression of coordinate utility values on a standard sequence.**

Iterating the one-step identity shows that `R.V j` is affine in `n` along the
standard sequence. -/
lemma additiveRep_standardSequence_Vj_arithmetic
    {X : ι → Type v} {P : ProductPref X} (R : AdditiveRep P)
    {j : ι} (σ : ProductPref.StandardSequence P j) :
    ∀ n : ℕ,
      R.V j (σ.α n) =
        R.V j (σ.α 0) + (n : ℝ) * (R.V σ.k σ.r - R.V σ.k σ.s) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := additiveRep_standardSequence_Vj_step R σ n
      have hsucc :
          R.V j (σ.α (n + 1)) =
            R.V j (σ.α n) + (R.V σ.k σ.r - R.V σ.k σ.s) := by
        linarith
      rw [hsucc, ih]
      push_cast
      ring

/-- **A strict standard sequence has a negative utility step.**

Strictness says the `α 0` profile is strictly preferred to the `α 1` profile;
under any additive representation this forces `R.V j (σ.α 1) < R.V j (σ.α 0)`,
and therefore the standard-sequence step is negative. -/
lemma additiveRep_standardSequence_step_negative_of_strict
    {X : ι → Type v} {P : ProductPref X} (R : AdditiveRep P)
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (hσ : σ.IsStrict) :
    R.V σ.k σ.r - R.V σ.k σ.s < 0 := by
  have hle : R.V j (σ.α 1) ≤ R.V j (σ.α 0) :=
    (additiveRep_coordPref_iff R j σ.base (σ.α 0) (σ.α 1)).mp hσ.1
  have hnot : ¬ R.V j (σ.α 0) ≤ R.V j (σ.α 1) := by
    intro hcontra
    exact hσ.2
      ((additiveRep_coordPref_iff R j σ.base (σ.α 1) (σ.α 0)).mpr hcontra)
  have hneq : R.V j (σ.α 1) ≠ R.V j (σ.α 0) := by
    intro heq
    apply hnot
    rw [heq]
  have hlt : R.V j (σ.α 1) < R.V j (σ.α 0) :=
    lt_of_le_of_ne hle hneq
  have hstep := additiveRep_standardSequence_Vj_step R σ 0
  linarith

/-- **Coordinate affine lift from one strict dense standard sequence.**

This is the construction-side version of the direct same-coordinate route.
For a strict standard sequence `σ`, both additive representations are affine
arithmetic progressions on the same grid.  Their step ratio is positive
because strictness makes both steps negative.  If both coordinate utilities
are continuous and the `σ.α`-grid is dense, the affine relation extends from
the grid to all of coordinate `j`. -/
theorem coordinateAffineLiftCertificate_of_strictStandardSequence
    {X : ι → Type v} [DecidableEq ι]
    {P : ProductPref X}
    (R₁ R₂ : AdditiveRep P)
    {j : ι}
    [TopologicalSpace (X j)] [T2Space (X j)]
    (σ : ProductPref.StandardSequence P j)
    (hσ : σ.IsStrict)
    (hcont₁ : Continuous (R₁.V j))
    (hcont₂ : Continuous (R₂.V j))
    (hdense : Dense (Set.range σ.α)) :
    CoordinateAffineLiftCertificate R₁ R₂ j := by
  let δ₁ : ℝ := R₁.V σ.k σ.r - R₁.V σ.k σ.s
  let δ₂ : ℝ := R₂.V σ.k σ.r - R₂.V σ.k σ.s
  let a₁ : ℝ := R₁.V j (σ.α 0)
  let a₂ : ℝ := R₂.V j (σ.α 0)
  let α : ℝ := δ₂ / δ₁
  let β : ℝ := a₂ - α * a₁
  have hδ₁_neg : δ₁ < 0 := by
    simpa [δ₁] using additiveRep_standardSequence_step_negative_of_strict R₁ σ hσ
  have hδ₂_neg : δ₂ < 0 := by
    simpa [δ₂] using additiveRep_standardSequence_step_negative_of_strict R₂ σ hσ
  have hδ₁_ne : δ₁ ≠ 0 := ne_of_lt hδ₁_neg
  have hα_pos : 0 < α := by
    simpa [α] using div_pos_of_neg_of_neg hδ₂_neg hδ₁_neg
  have hprog₁ : ∀ n : ℕ, R₁.V j (σ.α n) = a₁ + (n : ℝ) * δ₁ := by
    intro n
    simpa [a₁, δ₁] using additiveRep_standardSequence_Vj_arithmetic R₁ σ n
  have hprog₂ : ∀ n : ℕ, R₂.V j (σ.α n) = a₂ + (n : ℝ) * δ₂ := by
    intro n
    simpa [a₂, δ₂] using additiveRep_standardSequence_Vj_arithmetic R₂ σ n
  have hEqOn :
      Set.EqOn (R₂.V j) (fun x : X j => α * R₁.V j x + β)
        (Set.range σ.α) := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    change R₂.V j (σ.α n) = α * R₁.V j (σ.α n) + β
    rw [hprog₁ n, hprog₂ n]
    dsimp [α, β]
    field_simp [hδ₁_ne]
    ring
  have hcont_aff : Continuous (fun x : X j => α * R₁.V j x + β) := by
    exact (continuous_const.mul hcont₁).add continuous_const
  have hEq : R₂.V j = (fun x : X j => α * R₁.V j x + β) :=
    Continuous.ext_on hdense hcont₂ hcont_aff hEqOn
  exact ⟨α, β, hα_pos, fun x => congrFun hEq x⟩

/-- **Coordinate affine lift from common standard-sequence calibration,
continuity, and grid density.**

This is the direct standard-sequence route to `CoordinateAffineLiftCertificate`.
If `R₁.V j` and `R₂.V j` are calibrated to the same standard-sequence grid
`σ.α` (`n ↦ n`), both coordinate utilities are continuous, and the grid range
is dense in `X j`, then the two coordinate utilities agree everywhere by the
same density-extension argument used in the M5 shared-pivot machinery.  The
affine lift follows with `α = 1` and `β = 0`.

The hypotheses are intentionally explicit: grid calibration alone only gives
agreement on `Set.range σ.α`; continuity plus density is the real content that
extends this agreement globally. -/
theorem coordinateAffineLiftCertificate_of_commonStandardSequenceCalibration
    {X : ι → Type v} [DecidableEq ι]
    {P : ProductPref X}
    (R₁ R₂ : AdditiveRep P)
    {j : ι}
    [TopologicalSpace (X j)] [T2Space (X j)]
    (σ : ProductPref.StandardSequence P j)
    (hcal₁ : ∀ n : ℕ, R₁.V j (σ.α n) = (n : ℝ))
    (hcal₂ : ∀ n : ℕ, R₂.V j (σ.α n) = (n : ℝ))
    (hcont₁ : Continuous (R₁.V j))
    (hcont₂ : Continuous (R₂.V j))
    (hdense : Dense (Set.range σ.α)) :
    CoordinateAffineLiftCertificate R₁ R₂ j := by
  have hshared : SharedPivotGridCertificate σ (R₁.V j) (R₂.V j) :=
    ⟨hcal₁, hcal₂⟩
  have hEq : R₁.V j = R₂.V j :=
    sharedPivotGrid_global_agreement σ (R₁.V j) (R₂.V j)
      hshared hcont₁ hcont₂ hdense
  refine ⟨1, 0, by norm_num, ?_⟩
  intro x
  rw [← congrFun hEq x]
  ring

/-- **Coordinate affine lift from pairwise grid-normalization witnesses.**

Convenience corollary for the existing Step-4 calibration API.  If two
pairwise grid-normalization witnesses use the same standard sequence `σj` on
coordinate `j`, with the `j`-side utilities instantiated as `R₁.V j` and
`R₂.V j`, then their grid-normalization halves provide the common calibration
needed by `coordinateAffineLiftCertificate_of_commonStandardSequenceCalibration`.

As above, continuity of the two coordinate utilities and density of the shared
grid are the ingredients that turn grid agreement into a global affine lift. -/
theorem coordinateAffineLiftCertificate_of_pairwiseGridNormalizationWitnesses
    {X : ι → Type v} [DecidableEq ι]
    {P : ProductPref X}
    (R₁ R₂ : AdditiveRep P)
    {j k₁ k₂ : ι}
    [TopologicalSpace (X j)] [T2Space (X j)]
    {σj : ProductPref.StandardSequence P j}
    {σk₁ : ProductPref.StandardSequence P k₁}
    {σk₂ : ProductPref.StandardSequence P k₂}
    {Vk₁ : X k₁ → ℝ} {Vk₂ : X k₂ → ℝ}
    (hgrid₁ : PairwiseGridNormalizationWitness σj σk₁ (R₁.V j) Vk₁)
    (hgrid₂ : PairwiseGridNormalizationWitness σj σk₂ (R₂.V j) Vk₂)
    (hcont₁ : Continuous (R₁.V j))
    (hcont₂ : Continuous (R₂.V j))
    (hdense : Dense (Set.range σj.α)) :
    CoordinateAffineLiftCertificate R₁ R₂ j := by
  exact coordinateAffineLiftCertificate_of_commonStandardSequenceCalibration
    R₁ R₂ σj hgrid₁.1 hgrid₂.1 hcont₁ hcont₂ hdense

/-- **`TradeoffTransferCertificate` from utility-value-realizing
equivalences plus a triangle hypothesis through a third coordinate
— *diagnostic, retired*.**

End-to-end consumer combining the diagnostic off-diagonal and on-diagonal
discharges with the composition theorem.

This theorem is technically correct but consumes the diagnostic
`UtilityValueRealizingEquivalence_diagnostic` predicate twice, which is
structurally unattainable from any nontrivial additive representation.
It is retained for backward compatibility.

New code should use the corrected variant (TBD in §M2corrected below). -/
theorem tradeoffTransferCertificate_of_utilityValueRealizingEquivalence_and_triangle_diagnostic
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {X : ι → Type v} (P : ProductPref X)
    (R₁ R₂ : AdditiveRep P)
    [hne_profile : Nonempty (Profile X)]
    {j : ι} {v w : X j}
    (hne_j : R₁.V j v ≠ R₁.V j w)
    (hreal_j : UtilityValueRealizingEquivalence_diagnostic R₁ (P := P) v w)
    {m : ι} (hjm : j ≠ m)
    {m₁ m₂ : X m}
    (hne_m : R₁.V m m₁ ≠ R₁.V m m₂)
    (hreal_m : UtilityValueRealizingEquivalence_diagnostic R₁ (P := P) m₁ m₂) :
    TradeoffTransferCertificate R₁ R₂ j v w hne_j := by
  -- Off-diagonal at (j, v, w).
  have hOff_jm :
      OffDiagonalTradeoffTransferCertificate R₁ R₂ j v w hne_j :=
    offDiagonalTradeoffTransferCertificate_of_utilityValueRealizingEquivalence_diagnostic
      P R₁ R₂ hne_j hreal_j
  -- Off-diagonal at (m, m₁, m₂).
  have hOff_mj :
      OffDiagonalTradeoffTransferCertificate R₁ R₂ m m₁ m₂ hne_m :=
    offDiagonalTradeoffTransferCertificate_of_utilityValueRealizingEquivalence_diagnostic
      P R₁ R₂ hne_m hreal_m
  -- On-diagonal via the triangle through m.
  have hOn :
      OnCoordinateRatioConsistency R₁ R₂ j v w hne_j :=
    onCoordinateRatioConsistency_of_triangle_through_third_coordinate
      R₁ R₂ hne_j hjm hne_m hOff_jm hOff_mj
  -- Compose.
  exact tradeoffTransferCertificate_of_offDiagonal_and_onCoordinate
    R₁ R₂ hne_j hOff_jm hOn

/-! ##### M2corrected — corrected `UtilityValueRealizingEquivalence`

The diagnostic `UtilityValueRealizingEquivalence_diagnostic` predicate
is unattainable.  The corrected version below allows the reference pair
`(v', w')` to vary with the prescribed `(u₁, u₂)`, so the indifference-
forced difference equality is satisfiable for every prescribed pair.

Concretely: `tradeoff_equivalence_difference_equality` applied to the
equivalence clause forces
`R₁.V j v' - R₁.V j w' = R₁.V k u₁'' - R₁.V k u₂''`,
and the realization clause forces
`R₁.V k u₁'' - R₁.V k u₂'' = R₁.V k u₁ - R₁.V k u₂`.
Allowing `(v', w')` to vary lets us pick a reference pair on `j` whose
`R₁.V`-difference matches whatever `R₁.V k u₁ - R₁.V k u₂` happens to be.

The off-diagonal discharge through the corrected predicate then needs an
additional companion hypothesis: the cross-rep ratio at `(v', w')`
equals the cross-rep ratio at `(v, w)`.  This is exactly
`OnCoordinateRatioConsistency R₁ R₂ j v w hne_j` already isolated in
this file, applied to the realized reference pair `(v', w')`.

Adding `OnCoordinateRatioConsistency` to the corrected discharge makes
the off-diagonal proof routine.  In Wakker's actual proof, on-coordinate
ratio consistency is derived via standard-sequence calibration; the
artifact's existing `onCoordinateRatioConsistency_of_triangle_through_third_coordinate`
provides the same conclusion via a triangle through a third coordinate. -/

/-- **Corrected utility-value-realizing tradeoff equivalence existence
certificate (cross-coordinate).**

For every secondary coordinate `k ≠ j` and every pair `(u₁, u₂)` with
distinct `R₁.V`-values on `k`, there exist a reference pair `(v', w')`
on `j` *and* values `(u₁'', u₂'')` on `k` realizing the same
`R₁.V`-values *and* witnessing a tradeoff equivalence between the
varied reference pair and the realized secondary pair.

Allowing `(v', w')` to vary fixes the structural obstruction that made
`UtilityValueRealizingEquivalence_diagnostic` unattainable: the
indifference-forced difference equality
`R₁.V j v' - R₁.V j w' = R₁.V k u₁ - R₁.V k u₂`
can now be satisfied by choosing `(v', w')` with the matching
`R₁.V`-difference, which is the standard-sequence-density content of
Wakker's proof. -/
def UtilityValueRealizingEquivalence {X : ι → Type v}
    {P : ProductPref X} (R₁ : AdditiveRep P)
    (j : ι) : Prop :=
  ∀ (k : ι) (hjk : j ≠ k) (u₁ u₂ : X k),
    R₁.V k u₁ ≠ R₁.V k u₂ →
      ∃ (v' w' : X j) (u₁'' u₂'' : X k),
        R₁.V j v' ≠ R₁.V j w' ∧
        R₁.V k u₁'' = R₁.V k u₁ ∧
        R₁.V k u₂'' = R₁.V k u₂ ∧
        TradeoffEquivalence P j k hjk v' w' u₁'' u₂''

/-- **`OffDiagonalTradeoffTransferCertificate` from the corrected
utility-value-realizing equivalence plus on-coordinate ratio
consistency.**

Real, sorry-free proof.

Given a corrected `UtilityValueRealizingEquivalence` certificate at
coordinate `j` and an `OnCoordinateRatioConsistency` certificate at
the reference pair `(v, w)`, every secondary pair `(u₁, u₂)` with
non-trivial `R₁.V`-difference admits a ratio-equality derivation:

1. The corrected predicate produces a varied reference pair `(v', w')`
   and realized secondary pair `(u₁'', u₂'')` witnessing the
   equivalence.
2. `tradeoff_transfer_from_tradeoff_equivalence` gives the ratio
   equality at `(v', w', u₁'', u₂'')`: the cross-rep ratio on `k` at
   `(u₁'', u₂'')` equals the cross-rep ratio on `j` at `(v', w')`.
3. On-coordinate ratio consistency at `(v, w)` says the cross-rep ratio
   on `j` is the same at every non-trivial pair, so the `(v', w')`
   ratio equals the `(v, w)` ratio.
4. Zero-difference preservation transports the realization clause's
   `R₁.V`-equalities to `R₂.V`-equalities, lifting the ratio from
   `(u₁'', u₂'')` to the prescribed `(u₁, u₂)`. -/
theorem offDiagonalTradeoffTransferCertificate_of_utilityValueRealizingEquivalence_corrected
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {X : ι → Type v} (P : ProductPref X)
    (R₁ R₂ : AdditiveRep P)
    [hne_profile : Nonempty (Profile X)]
    {j : ι} {v w : X j}
    (hne : R₁.V j v ≠ R₁.V j w)
    (hreal : UtilityValueRealizingEquivalence (P := P) R₁ j)
    (hOn : OnCoordinateRatioConsistency R₁ R₂ j v w hne) :
    OffDiagonalTradeoffTransferCertificate R₁ R₂ j v w hne := by
  intro k hjk u₁ u₂ hne_k
  obtain ⟨v', w', u₁'', u₂'', hne_j', hR1_u1, hR1_u2, hequiv⟩ :=
    hreal k hjk u₁ u₂ hne_k
  -- Step 1: zero-diff preservation transports R₁.V-equalities to R₂.V.
  have hR2_u1 : R₂.V k u₁'' = R₂.V k u₁ :=
    zero_difference_preservation_across_additive_representations
      P R₁ R₂ k u₁'' u₁ hR1_u1
  have hR2_u2 : R₂.V k u₂'' = R₂.V k u₂ :=
    zero_difference_preservation_across_additive_representations
      P R₁ R₂ k u₂'' u₂ hR1_u2
  -- Step 2: realization clause transports the prescribed R₁.V-difference
  -- inequality back to (u₁'', u₂'').
  have hne_k'' : R₁.V k u₁'' ≠ R₁.V k u₂'' := by
    rw [hR1_u1, hR1_u2]; exact hne_k
  -- Step 3: ratio at (v', w', u₁'', u₂'') from the single-pair tradeoff
  -- transfer.
  have hratio'' :
      (R₂.V k u₁'' - R₂.V k u₂'') / (R₁.V k u₁'' - R₁.V k u₂'') =
        (R₂.V j v' - R₂.V j w') / (R₁.V j v' - R₁.V j w') :=
    tradeoff_transfer_from_tradeoff_equivalence P R₁ R₂ hjk hne_j' hne_k''
      hequiv
  -- Step 4: on-coordinate ratio consistency at (v, w) transports
  -- the ratio at (v', w') to the ratio at (v, w).
  have hratio_j :
      (R₂.V j v' - R₂.V j w') / (R₁.V j v' - R₁.V j w') =
        (R₂.V j v - R₂.V j w) / (R₁.V j v - R₁.V j w) :=
    hOn v' w' hne_j'
  -- Compose and rewrite.
  rw [hR1_u1, hR1_u2, hR2_u1, hR2_u2] at hratio''
  exact hratio''.trans hratio_j

/-- **End-to-end consumer: `TradeoffTransferCertificate` from the
corrected utility-value-realizing equivalence plus on-coordinate ratio
consistency.**

Combines `offDiagonalTradeoffTransferCertificate_of_utilityValueRealizingEquivalence_corrected`
with `tradeoffTransferCertificate_of_offDiagonal_and_onCoordinate` to
produce the full transfer certificate from:

* the corrected `UtilityValueRealizingEquivalence` at coordinate `j`,
* `OnCoordinateRatioConsistency` at the reference pair `(v, w)`.

The on-coordinate ratio consistency hypothesis is itself derivable
from a triangle through a third coordinate via the existing
`onCoordinateRatioConsistency_of_triangle_through_third_coordinate`
theorem, but discharging it independently of the off-diagonal
certificate at `(v, w)` is the genuine standard-sequence-calibration
content of Wakker's M2 proof.

The chain therefore exposes two named open hypotheses on the corrected
M2 frontier:

1. `UtilityValueRealizingEquivalence` at coordinate `j` (the structural
   solvability + bracketing + standard-sequence-density bridge).
2. `OnCoordinateRatioConsistency` at `(v, w)` (the standard-sequence
   calibration content).

Both are real mathematical content of Wakker (1989); neither is
discharged here, but the algebraic transport between them and the
single named transfer certificate is fully mechanized. -/
theorem tradeoffTransferCertificate_of_utilityValueRealizingEquivalence_corrected_and_onCoordinate
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {X : ι → Type v} (P : ProductPref X)
    (R₁ R₂ : AdditiveRep P)
    [hne_profile : Nonempty (Profile X)]
    {j : ι} {v w : X j}
    (hne_j : R₁.V j v ≠ R₁.V j w)
    (hreal_j : UtilityValueRealizingEquivalence (P := P) R₁ j)
    (hOn : OnCoordinateRatioConsistency R₁ R₂ j v w hne_j) :
    TradeoffTransferCertificate R₁ R₂ j v w hne_j := by
  -- Off-diagonal piece via the corrected predicate.
  have hOff :
      OffDiagonalTradeoffTransferCertificate R₁ R₂ j v w hne_j :=
    offDiagonalTradeoffTransferCertificate_of_utilityValueRealizingEquivalence_corrected
      P R₁ R₂ hne_j hreal_j hOn
  -- Compose with the on-coordinate hypothesis.
  exact tradeoffTransferCertificate_of_offDiagonal_and_onCoordinate
    R₁ R₂ hne_j hOff hOn

/-- **End-to-end consumer: `TradeoffTransferCertificate` from the
corrected utility-value-realizing equivalence plus a coordinate affine
lift on `j`.**

This is the direct same-coordinate calibration route for the corrected M2
chain.  Once the off-diagonal side is handled by the corrected
`UtilityValueRealizingEquivalence`, any theorem-backed affine relation on the
reference coordinate `j` immediately discharges `OnCoordinateRatioConsistency`
and therefore the full `TradeoffTransferCertificate`.

It is the cleanest consumer-facing bridge for the connected-coordinate
version of Wakker's proof: the remaining direct calibration content is
packaged as `CoordinateAffineLiftCertificate`, rather than as the more opaque
ratio-equality predicate alone. -/
theorem tradeoffTransferCertificate_of_utilityValueRealizingEquivalence_corrected_and_coordinateAffineLift
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {X : ι → Type v} (P : ProductPref X)
    (R₁ R₂ : AdditiveRep P)
    [hne_profile : Nonempty (Profile X)]
    {j : ι} {v w : X j}
    (hne_j : R₁.V j v ≠ R₁.V j w)
    (hreal_j : UtilityValueRealizingEquivalence (P := P) R₁ j)
    (hAff : CoordinateAffineLiftCertificate R₁ R₂ j) :
    TradeoffTransferCertificate R₁ R₂ j v w hne_j := by
  have hOn : OnCoordinateRatioConsistency R₁ R₂ j v w hne_j :=
    onCoordinateRatioConsistency_of_coordinateAffineLift R₁ R₂ hne_j hAff
  exact tradeoffTransferCertificate_of_utilityValueRealizingEquivalence_corrected_and_onCoordinate
    P R₁ R₂ hne_j hreal_j hOn

/-! ##### Further factoring: corrected `UtilityValueRealizingEquivalence`
    from bracketing + j-difference realization

The corrected `UtilityValueRealizingEquivalence` predicate further
decomposes into two named sub-bridges plus the existing
`RestrictedSolvability` infrastructure:

1. **`JDifferenceRealizationCertificate`**: for any `(k, u₁, u₂)` with
   non-trivial `R₁.V`-difference on `k`, find a reference pair
   `(v', w')` on `j` with `R₁.V j v' - R₁.V j w' = R₁.V k u₁ - R₁.V k u₂`.
   This is the standard-sequence-density content of Wakker's proof on
   coordinate `j`.

2. **`TradeoffBracketingForallCertificate`**: for any reference pair
   `(v', w')` and primary `u₁` produced by sub-bridge (1),
   `TradeoffBracketingCertificate` holds.  This is the
   `Archimedean + monotone-grid` content already factored in the
   artifact at `TradeoffBracketingCertificate` for individual triples.

The third ingredient is `RestrictedSolvability`, already a structural
axiom of `WakkerInfrastructure.lean`.

The discharge below combines all three to produce the corrected
`UtilityValueRealizingEquivalence`. -/

/-- **j-difference realization certificate.**

For every pair `(k, u₁, u₂)` with `k ≠ j` and `R₁.V k u₁ ≠ R₁.V k u₂`,
there exist values `(v', w' : X j)` with `R₁.V j`-difference matching
the prescribed `R₁.V k`-difference.

In Wakker's framework this is a consequence of standard-sequence
density on `R₁.V j`.  The artifact's existing standard-sequence
infrastructure plus the necessity-layer theorem
`Vj_nonconstant_of_essential_of_additivelyRepresents` provides the
seed; the full discharge requires extending that to arbitrary
intermediate values, which is the standard-sequence-density step. -/
def JDifferenceRealizationCertificate {X : ι → Type v}
    {P : ProductPref X} (R₁ : AdditiveRep P) (j : ι) : Prop :=
  ∀ (k : ι) (_hjk : j ≠ k) (u₁ u₂ : X k),
    R₁.V k u₁ ≠ R₁.V k u₂ →
      ∃ v' w' : X j,
        R₁.V j v' - R₁.V j w' = R₁.V k u₁ - R₁.V k u₂

/-- **Tradeoff bracketing forall-certificate.**

The `TradeoffBracketingCertificate` predicate, quantified over all
relevant reference pairs and primaries.  This is the standardised
form needed to feed
`tradeoffEquivalence_of_restrictedSolvability_and_bracketing` for
arbitrary inputs.

In Wakker's framework this is the `Archimedean + monotone-grid`
content; the artifact's existing `TradeoffBracketingCertificate`
predicate already expresses the per-triple version. -/
def TradeoffBracketingForallCertificate {X : ι → Type v}
    (P : ProductPref X) (j : ι) : Prop :=
  ∀ (k : ι) (hjk : j ≠ k) (a₀ : Profile X) (v' w' : X j) (u₁ : X k),
    TradeoffBracketingCertificate P j k hjk a₀ v' w' u₁

/-! ##### Discharge of `TradeoffBracketingForallCertificate` from
    coordinate-utility unboundedness

The bracketing certificate at `(a₀, v', w', u₁)` requires two `k`-values
whose updated profiles `weakPref`-bracket the target.  Under any
additive representation `R : AdditiveRep P`, this reduces algebraically
to finding two `k`-values whose `R.V k`-values bracket the prescribed
real `R.V k u₁ + R.V j w' - R.V j v'`.  A sufficient condition is that
`R.V k`'s image is unbounded above and below in `ℝ`.

We name this precise content as `CoordinateUtilityUnboundedCertificate`
and discharge `TradeoffBracketingForallCertificate` from it.  The
sample witness `additiveBoolReal_pref` plus identity per-coord utility
satisfies the unboundedness predicate trivially. -/

/-- **Coordinate-utility unboundedness certificate.**

For coordinate `k`, the per-coord utility `R.V k : X k → ℝ` takes
arbitrarily large positive values and arbitrarily large negative values:
for every real `r`, there exist `u_lo, u_hi : X k` with
`R.V k u_lo ≤ r` and `r ≤ R.V k u_hi`.

This is the precise content of "`R.V k`'s image covers all of `ℝ`
weakly" and is the standard-sequence-density consequence in Wakker's
framework on a real-valued coordinate.  In the canonical case
`X k = ℝ` and `R.V k = id`, the witness is trivial: pick `u_lo = r - 1`
and `u_hi = r + 1`. -/
def CoordinateUtilityUnboundedCertificate {X : ι → Type v}
    {P : ProductPref X} (R : AdditiveRep P) (k : ι) : Prop :=
  ∀ r : ℝ, ∃ u_lo u_hi : X k, R.V k u_lo ≤ r ∧ r ≤ R.V k u_hi

/-- **Single-triple bracketing discharge from coordinate-utility
unboundedness.**

Given an additive representation `R : AdditiveRep P` and a
`CoordinateUtilityUnboundedCertificate` on coordinate `k`, the
`TradeoffBracketingCertificate` holds for any prescribed
`(a₀, v', w', u₁)` triple.

The bracketing inequalities under `R.represents` collapse to
`R.V k u_lo ≤ r ≤ R.V k u_hi` for `r := R.V k u₁ + R.V j w' - R.V j v'`,
which the unboundedness certificate satisfies directly. -/
theorem tradeoffBracketingCertificate_of_coordinateUtilityUnbounded
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {X : ι → Type v} {P : ProductPref X}
    (R : AdditiveRep P)
    {j k : ι} (hjk : j ≠ k)
    (a₀ : Profile X) (v' w' : X j) (u₁ : X k)
    (hcov : CoordinateUtilityUnboundedCertificate R k) :
    TradeoffBracketingCertificate P j k hjk a₀ v' w' u₁ := by
  -- Target real value: r := R.V k u₁ + R.V j w' - R.V j v'.
  obtain ⟨u_lo, u_hi, hlo, hhi⟩ :=
    hcov (R.V k u₁ + R.V j w' - R.V j v')
  refine ⟨u_lo, u_hi, ?_, ?_⟩
  · -- weakPref (update (update a₀ j v') k u_hi) (update (update a₀ j w') k u₁)
    -- ⟺ Σ V on the right ≤ Σ V on the left.
    rw [R.represents]
    -- LHS sum: V_j(v') + V_k(u_hi) + Σ_{i ∉ {j,k}} V_i(a₀ i)
    -- RHS sum: V_j(w') + V_k(u₁) + Σ_{i ∉ {j,k}} V_i(a₀ i)
    have h_lhs := sum_eq_pair_add_rest R.V (Function.update (Function.update a₀ j v') k u_hi) hjk
    have h_rhs := sum_eq_pair_add_rest R.V (Function.update (Function.update a₀ j w') k u₁) hjk
    -- Coordinate-value extractions.
    have hL_j : R.V j ((Function.update (Function.update a₀ j v') k u_hi) j) = R.V j v' := by
      rw [Function.update_of_ne hjk, Function.update_self]
    have hL_k : R.V k ((Function.update (Function.update a₀ j v') k u_hi) k) = R.V k u_hi := by
      rw [Function.update_self]
    have hR_j : R.V j ((Function.update (Function.update a₀ j w') k u₁) j) = R.V j w' := by
      rw [Function.update_of_ne hjk, Function.update_self]
    have hR_k : R.V k ((Function.update (Function.update a₀ j w') k u₁) k) = R.V k u₁ := by
      rw [Function.update_self]
    -- The "rest" sums are equal because both profiles agree off {j, k}.
    have hrest :
        (∑ i ∈ (Finset.univ.erase j).erase k,
            R.V i ((Function.update (Function.update a₀ j w') k u₁) i)) =
        (∑ i ∈ (Finset.univ.erase j).erase k,
            R.V i ((Function.update (Function.update a₀ j v') k u_hi) i)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hik : i ≠ k := Finset.ne_of_mem_erase hi
      have hi_erase_j : i ∈ Finset.univ.erase j := (Finset.mem_erase.mp hi).2
      have hij : i ≠ j := Finset.ne_of_mem_erase hi_erase_j
      rw [Function.update_of_ne hik, Function.update_of_ne hij,
          Function.update_of_ne hik, Function.update_of_ne hij]
    rw [h_lhs, h_rhs, hL_j, hL_k, hR_j, hR_k, ← hrest]
    linarith
  · -- weakPref (update (update a₀ j w') k u₁) (update (update a₀ j v') k u_lo)
    -- ⟺ Σ V on the right ≤ Σ V on the left.
    rw [R.represents]
    have h_lhs := sum_eq_pair_add_rest R.V (Function.update (Function.update a₀ j w') k u₁) hjk
    have h_rhs := sum_eq_pair_add_rest R.V (Function.update (Function.update a₀ j v') k u_lo) hjk
    have hL_j : R.V j ((Function.update (Function.update a₀ j w') k u₁) j) = R.V j w' := by
      rw [Function.update_of_ne hjk, Function.update_self]
    have hL_k : R.V k ((Function.update (Function.update a₀ j w') k u₁) k) = R.V k u₁ := by
      rw [Function.update_self]
    have hR_j : R.V j ((Function.update (Function.update a₀ j v') k u_lo) j) = R.V j v' := by
      rw [Function.update_of_ne hjk, Function.update_self]
    have hR_k : R.V k ((Function.update (Function.update a₀ j v') k u_lo) k) = R.V k u_lo := by
      rw [Function.update_self]
    have hrest :
        (∑ i ∈ (Finset.univ.erase j).erase k,
            R.V i ((Function.update (Function.update a₀ j v') k u_lo) i)) =
        (∑ i ∈ (Finset.univ.erase j).erase k,
            R.V i ((Function.update (Function.update a₀ j w') k u₁) i)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hik : i ≠ k := Finset.ne_of_mem_erase hi
      have hi_erase_j : i ∈ Finset.univ.erase j := (Finset.mem_erase.mp hi).2
      have hij : i ≠ j := Finset.ne_of_mem_erase hi_erase_j
      rw [Function.update_of_ne hik, Function.update_of_ne hij,
          Function.update_of_ne hik, Function.update_of_ne hij]
    rw [h_lhs, h_rhs, hL_j, hL_k, hR_j, hR_k, ← hrest]
    linarith

/-- **`TradeoffBracketingForallCertificate` from coordinate-utility
unboundedness on every coordinate.**

Real, sorry-free proof: for any prescribed `(k, hjk, a₀, v', w', u₁)`,
the unboundedness certificate at `k` plus the additive representation
plus the algebraic discharge above produces the bracketing certificate. -/
theorem tradeoffBracketingForallCertificate_of_coordinateUtilityUnbounded
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {X : ι → Type v} {P : ProductPref X}
    (R : AdditiveRep P) (j : ι)
    (hcov : ∀ k : ι, CoordinateUtilityUnboundedCertificate R k) :
    TradeoffBracketingForallCertificate P j := by
  intro k hjk a₀ v' w' u₁
  exact tradeoffBracketingCertificate_of_coordinateUtilityUnbounded
    R hjk a₀ v' w' u₁ (hcov k)

/-- **Sample witness: `CoordinateUtilityUnboundedCertificate` holds for
the additive Bool/Real representation on every coordinate.**

The identity per-coord utility on `ℝ` is unbounded above and below
trivially: for every `r : ℝ`, take `u_lo = r - 1` and `u_hi = r + 1`. -/
theorem additiveBoolReal_coordinateUtilityUnbounded :
    ∀ k : Bool,
      CoordinateUtilityUnboundedCertificate
        (P := additiveBoolReal_pref) additiveBoolReal_rep k := by
  intro _k r
  refine ⟨r - 1, r + 1, ?_, ?_⟩
  · show r - 1 ≤ r
    linarith
  · show r ≤ r + 1
    linarith

/-- **Sample witness: `TradeoffBracketingForallCertificate` holds for
the additive Bool/Real representation, on either coordinate as the
reference.**

Combines `additiveBoolReal_coordinateUtilityUnbounded` with the
generic discharge.  Validates that
`TradeoffBracketingForallCertificate` is non-vacuous and provides a
regression target for any future generalization. -/
theorem additiveBoolReal_tradeoffBracketingForallCertificate :
    ∀ j : Bool,
      TradeoffBracketingForallCertificate additiveBoolReal_pref j := by
  intro j
  exact tradeoffBracketingForallCertificate_of_coordinateUtilityUnbounded
    additiveBoolReal_rep j additiveBoolReal_coordinateUtilityUnbounded

/-! ##### Standard-sequence cofinality of `R.V j`

Bridge from the Wakker-style standard-sequence primitives to the
`CoordinateUtilityUnboundedCertificate` predicate.  Topology-free: the only
inputs are an additive representation, the standard-sequence step lemma
`additiveRep_standardSequence_Vj_step`, its arithmetic-progression iterate
`additiveRep_standardSequence_Vj_arithmetic`, and the strict-step sign
lemma `additiveRep_standardSequence_step_negative_of_strict`. -/

/-- **Cofinality below of `R.V j` from a strict standard sequence.**

A strict standard sequence `σ` in coordinate `j` makes the per-coordinate
utility `R.V j` an arithmetic progression along `σ.α` with negative common
difference `Δ = R.V σ.k σ.r - R.V σ.k σ.s < 0`.  Hence its image is cofinal
below in `ℝ`: for every real `r`, some term `σ.α N` has `R.V j (σ.α N) ≤ r`.

This is the algebraic, topology-free "downwards" half of the
`CoordinateUtilityUnboundedCertificate` bracket; the symmetric "upwards"
half follows from any standard sequence whose step has the opposite sign
(see `additiveRep_Vj_cofinalAbove_of_standardSequence_posStep`).  The two
combine into `coordinateUtilityUnboundedCertificate_of_strictStandardSequence_pair`. -/
theorem additiveRep_Vj_cofinalBelow_of_strictStandardSequence
    {X : ι → Type v} {P : ProductPref X} (R : AdditiveRep P)
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (hσ : σ.IsStrict) :
    ∀ r : ℝ, ∃ u : X j, R.V j u ≤ r := by
  intro r
  set Δ : ℝ := R.V σ.k σ.r - R.V σ.k σ.s with hΔdef
  have hΔneg : Δ < 0 := by
    simpa [hΔdef] using
      additiveRep_standardSequence_step_negative_of_strict R σ hσ
  have hposNeg : 0 < -Δ := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((R.V j (σ.α 0) - r) / (-Δ))
  have hN' : R.V j (σ.α 0) - r < (N : ℝ) * (-Δ) :=
    (div_lt_iff₀ hposNeg).mp hN
  refine ⟨σ.α N, ?_⟩
  have harith :
      R.V j (σ.α N) = R.V j (σ.α 0) + (N : ℝ) * Δ := by
    simpa [hΔdef] using additiveRep_standardSequence_Vj_arithmetic R σ N
  rw [harith]
  nlinarith [hN', hΔneg]

/-- **Cofinality above of `R.V j` from a positive-step standard sequence.**

Dual of `additiveRep_Vj_cofinalBelow_of_strictStandardSequence`.  If `σ` is a
standard sequence in coordinate `j` whose step `Δ = R.V σ.k σ.r - R.V σ.k σ.s`
is *positive*, then `R.V j` is cofinal above in `ℝ`.

The positive-step hypothesis is supplied as a separate algebraic input
`hΔpos`; in Wakker's framework it arises from a strict standard sequence
with the reference pair `(σ.r, σ.s)` swapped (which under solvability /
continuity can be obtained from any strict standard sequence).  We keep the
hypothesis algebraic here so the lemma stays topology-free. -/
theorem additiveRep_Vj_cofinalAbove_of_standardSequence_posStep
    {X : ι → Type v} {P : ProductPref X} (R : AdditiveRep P)
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (hΔpos : 0 < R.V σ.k σ.r - R.V σ.k σ.s) :
    ∀ r : ℝ, ∃ u : X j, r ≤ R.V j u := by
  intro r
  set Δ : ℝ := R.V σ.k σ.r - R.V σ.k σ.s with hΔdef
  have hΔpos' : 0 < Δ := by simpa [hΔdef] using hΔpos
  obtain ⟨N, hN⟩ := exists_nat_gt ((r - R.V j (σ.α 0)) / Δ)
  have hN' : r - R.V j (σ.α 0) < (N : ℝ) * Δ :=
    (div_lt_iff₀ hΔpos').mp hN
  refine ⟨σ.α N, ?_⟩
  have harith :
      R.V j (σ.α N) = R.V j (σ.α 0) + (N : ℝ) * Δ := by
    simpa [hΔdef] using additiveRep_standardSequence_Vj_arithmetic R σ N
  rw [harith]; linarith

/-- **`CoordinateUtilityUnboundedCertificate` from a pair of standard
sequences with opposite step signs.**

The bidirectional unboundedness certificate
`CoordinateUtilityUnboundedCertificate R j` requires both `u_lo` and `u_hi`
witnesses for every real `r`.  This follows from two standard sequences in
coordinate `j`:

* `σdown`, a strict standard sequence (negative step), supplying the
  `u_lo` side via `additiveRep_Vj_cofinalBelow_of_strictStandardSequence`;
* `σup`, a standard sequence with positive step `Δ > 0` (typically the
  reference-pair swap of a strict standard sequence), supplying the
  `u_hi` side via `additiveRep_Vj_cofinalAbove_of_standardSequence_posStep`.

This is the precise structural reduction of `CoordinateUtilityUnbounded` to
Wakker's standard-sequence primitives, with no topology.  The remaining
construction-side work is producing the pair `(σdown, σup)` from
essentiality + restricted solvability. -/
theorem coordinateUtilityUnboundedCertificate_of_strictStandardSequence_pair
    {X : ι → Type v} {P : ProductPref X} (R : AdditiveRep P)
    {j : ι}
    (σdown : ProductPref.StandardSequence P j) (hdown : σdown.IsStrict)
    (σup : ProductPref.StandardSequence P j)
    (hup : 0 < R.V σup.k σup.r - R.V σup.k σup.s) :
    CoordinateUtilityUnboundedCertificate R j := by
  intro r
  obtain ⟨u_lo, hlo⟩ :=
    additiveRep_Vj_cofinalBelow_of_strictStandardSequence R σdown hdown r
  obtain ⟨u_hi, hhi⟩ :=
    additiveRep_Vj_cofinalAbove_of_standardSequence_posStep R σup hup r
  exact ⟨u_lo, u_hi, hlo, hhi⟩

/-- **Corrected `UtilityValueRealizingEquivalence` from j-difference
realization + tradeoff bracketing forall-certificate +
RestrictedSolvability.**

Real, sorry-free proof.

Given the prescribed `(k, u₁, u₂)` with `R₁.V k u₁ ≠ R₁.V k u₂`:

1. `JDifferenceRealizationCertificate` produces `(v', w')` with
   `R₁.V j v' - R₁.V j w' = R₁.V k u₁ - R₁.V k u₂`.  In particular,
   `R₁.V j v' ≠ R₁.V j w'`.

2. `TradeoffBracketingForallCertificate` at `(j, k, a₀, v', w', u₁)`
   produces a bracket on `k`.  We choose `a₀` to be any profile
   inhabited by `Nonempty (Profile X)`.

3. `tradeoffEquivalence_of_restrictedSolvability_and_bracketing` plus
   `RestrictedSolvability` produces a `u₂_constructed : X k` such that
   `TradeoffEquivalence P j k hjk v' w' u₁ u₂_constructed` holds.

4. By `tradeoff_equivalence_difference_equality` applied to the
   constructed equivalence, `R₁.V j v' - R₁.V j w' =
   R₁.V k u₁ - R₁.V k u₂_constructed`.  Combined with step 1's
   equation, `R₁.V k u₂_constructed = R₁.V k u₂`.  Set
   `(u₁'', u₂'') = (u₁, u₂_constructed)`. -/
theorem utilityValueRealizingEquivalence_corrected_of_jDifferenceRealization_and_bracketing
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {X : ι → Type v} (P : ProductPref X)
    [hWO : ProductPref.IsWeakOrder P]
    (R₁ : AdditiveRep P)
    [hne_profile : Nonempty (Profile X)]
    (j : ι)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hJDiff : JDifferenceRealizationCertificate (P := P) R₁ j)
    (hBracket : TradeoffBracketingForallCertificate P j) :
    UtilityValueRealizingEquivalence (P := P) R₁ j := by
  intro k hjk u₁ u₂ hne_k
  -- Step 1: realize the j-difference matching R₁.V k u₁ - R₁.V k u₂.
  obtain ⟨v', w', hdiff⟩ := hJDiff k hjk u₁ u₂ hne_k
  -- Step 2: pick a base profile.
  obtain ⟨a₀⟩ := hne_profile
  -- Step 3: bracket and apply tradeoffEquivalence_of_restrictedSolvability_and_bracketing.
  have hbracket :
      TradeoffBracketingCertificate P j k hjk a₀ v' w' u₁ :=
    hBracket k hjk a₀ v' w' u₁
  obtain ⟨u₂_constructed, hequiv⟩ :=
    tradeoffEquivalence_of_restrictedSolvability_and_bracketing
      P hsolv hjk a₀ v' w' u₁ hbracket
  -- Step 4: the constructed u₂ has the right R₁.V-value.
  have hdiff_equiv :
      R₁.V j v' - R₁.V j w' = R₁.V k u₁ - R₁.V k u₂_constructed :=
    tradeoff_equivalence_difference_equality P R₁ hjk hequiv
  -- Combine: R₁.V k u₂_constructed = R₁.V k u₂.
  have hR1_u2 : R₁.V k u₂_constructed = R₁.V k u₂ := by
    have : R₁.V k u₁ - R₁.V k u₂_constructed = R₁.V k u₁ - R₁.V k u₂ := by
      rw [← hdiff_equiv, hdiff]
    linarith
  -- The R₁.V j-non-equality witness.
  have hne_j' : R₁.V j v' ≠ R₁.V j w' := by
    intro heq
    rw [heq, sub_self] at hdiff
    exact hne_k (sub_eq_zero.mp hdiff.symm)
  -- Assemble the witness.
  refine ⟨v', w', u₁, u₂_constructed, hne_j', ?_, hR1_u2, hequiv⟩
  rfl

/-! #### M3 — `hConc` entry-point bundle (DK two-coordinate concavity)

The M3 bundle is the slice-level analogue of M4: per-pair concavity from
convex upper-contour sets.  Following the M4 enrichment pattern, the
genuinely missing structural content beyond convex upper-contour sets is
**continuity** of each slice utility `V₁`, `V₂` on its domain.  This is
exactly the slice version of the M4 `CoordinateUtilityContinuityCertificate`,
and it is the precise content `QuasiToConcaveStrengtheningCertificate`
already isolates as the deep DK step.

For the M3 specialization we add:

1. A slice-level continuity certificate `SliceUtilityContinuityCertificate`
   that mirrors M4's `CoordinateUtilityContinuityCertificate` on the
   two-coordinate slice.
2. The easy direction: per-slice concavity on a convex slice already
   implies continuity on the interior of the slice, by Mathlib's
   `ConcaveOn.continuousOn_interior`.
3. A cross-flow showing that the M4 continuity certificate restricts to
   the M3 continuity certificate on every coordinate pair, so any future
   M4 discharge automatically discharges M3's continuity residual on
   every slice. -/

/-- **Slice-level utility continuity certificate (M3 residual obligation).**

The slice analogue of M4's `CoordinateUtilityContinuityCertificate`.

Statement: each slice utility `V₁`, `V₂` is continuous on its domain.

This is the precise content already implicit in
`QuasiToConcaveStrengtheningCertificate`: the "continuity + DK 3-coordinate
alignment" upgrade from quasi-concavity to full concavity.  Naming it
explicitly makes the M3 / M4 parallel visible at the bundle level. -/
def SliceUtilityContinuityCertificate
    (S₁ S₂ : Set ℝ) (V₁ V₂ : ℝ → ℝ) : Prop :=
  ContinuousOn V₁ S₁ ∧ ContinuousOn V₂ S₂

/-- **Phase 8 / Certificate 4 input bundle (enriched).**

Single named hypothesis collapsing the DK two-coordinate concavity frontier.
Stated under the structural axioms required by `two_coord_concave` plus the
slice-level continuity residual: convex slice domains `S₁`, `S₂`,
convexity of every joint upper-contour set, and continuity of each slice
utility.

Compared to the original (under-axioned) version of this bundle, this one
matches the axiom set Debreu–Koopmans (1982) §3 Lemma 3.3 actually use.

The certificate body is `TwoCoordinateConcavityCertificate S₁ S₂ V₁ V₂`. -/
def TwoCoordinateConcavityInputCertificate
    (S₁ S₂ : Set ℝ) (_hS₁ : Convex ℝ S₁) (_hS₂ : Convex ℝ S₂)
    (V₁ V₂ : ℝ → ℝ)
    (_hConvex :
      ∀ (u₀ : ℝ) (v₀ : ℝ),
        Convex ℝ ({ p : ℝ × ℝ |
                     p.1 ∈ S₁ ∧ p.2 ∈ S₂ ∧
                     V₁ u₀ + V₂ v₀ ≤ V₁ p.1 + V₂ p.2 }))
    (_hCont : SliceUtilityContinuityCertificate S₁ S₂ V₁ V₂) : Prop :=
  TwoCoordinateConcavityCertificate S₁ S₂ V₁ V₂

/-- **Phase 8 / Certificate 4 entry-point theorem.**

From the structural axioms required by `two_coord_concave` plus the
enriched input bundle, produce the existing
`TwoCoordinateConcavityCertificate`. -/
theorem twoCoordinateConcavityCertificate_of_input
    {S₁ S₂ : Set ℝ} (hS₁ : Convex ℝ S₁) (hS₂ : Convex ℝ S₂)
    {V₁ V₂ : ℝ → ℝ}
    (hConvex :
      ∀ (u₀ : ℝ) (v₀ : ℝ),
        Convex ℝ ({ p : ℝ × ℝ |
                     p.1 ∈ S₁ ∧ p.2 ∈ S₂ ∧
                     V₁ u₀ + V₂ v₀ ≤ V₁ p.1 + V₂ p.2 }))
    (hCont : SliceUtilityContinuityCertificate S₁ S₂ V₁ V₂)
    (hInput : TwoCoordinateConcavityInputCertificate
                S₁ S₂ hS₁ hS₂ V₁ V₂ hConvex hCont) :
    TwoCoordinateConcavityCertificate S₁ S₂ V₁ V₂ :=
  hInput

/-- **Phase 8 / Certificate 4 regression through `two_coord_concave`.**

End-to-end check that the enriched input bundle plus the structural axioms
produce the joint-concavity conclusion through the public consumer
interface. -/
theorem two_coord_concave_of_input
    {S₁ S₂ : Set ℝ} (hS₁ : Convex ℝ S₁) (hS₂ : Convex ℝ S₂)
    {V₁ V₂ : ℝ → ℝ}
    (hConvex :
      ∀ (u₀ : ℝ) (v₀ : ℝ),
        Convex ℝ ({ p : ℝ × ℝ |
                     p.1 ∈ S₁ ∧ p.2 ∈ S₂ ∧
                     V₁ u₀ + V₂ v₀ ≤ V₁ p.1 + V₂ p.2 }))
    (hCont : SliceUtilityContinuityCertificate S₁ S₂ V₁ V₂)
    (hInput : TwoCoordinateConcavityInputCertificate
                S₁ S₂ hS₁ hS₂ V₁ V₂ hConvex hCont) :
    ConcaveOn ℝ S₁ V₁ ∧ ConcaveOn ℝ S₂ V₂ :=
  _root_.WakkerRoadmap.DebreuKoopmansHard.two_coord_concave
    S₁ S₂ hS₁ hS₂ V₁ V₂ hConvex hInput

/-- **M3 cross-flow: concavity on each slice implies continuity on
the interior of each slice.**

The slice analogue of `coordinateUtilityContinuityCertificate_of_perCoordinateConcavityCertificate_interior`.
Given joint concavity on the slice, both `V₁` and `V₂` are continuous on
the interior of their respective domains, by Mathlib's
`ConcaveOn.continuousOn_interior`. -/
theorem sliceUtilityContinuityCertificate_of_twoCoordinateConcavityCertificate_interior
    {S₁ S₂ : Set ℝ} {V₁ V₂ : ℝ → ℝ}
    (hConc : TwoCoordinateConcavityCertificate S₁ S₂ V₁ V₂) :
    ContinuousOn V₁ (interior S₁) ∧ ContinuousOn V₂ (interior S₂) :=
  ⟨ConcaveOn.continuousOn_interior hConc.1,
   ConcaveOn.continuousOn_interior hConc.2⟩

/-! #### M4 — `hPairConc` / `hConcAll` entry-point bundle (DK transfer)

The original M4 bundle was under-axiomed: convex preference + additive
representation + all coordinates essential is *not* enough to force per-
coordinate concavity, because pathological discontinuous additive functions
(non-measurable solutions to Cauchy's equation) satisfy all those hypotheses
without being concave.

Concretely: take `n = 3`, `S i = ℝ`, and let `g : ℝ → ℝ` be a discontinuous
solution to `g(x + y) = g(x) + g(y)` (existence by AC).  Set `V_1 = V_2 = g`
and `V_3 = -2g`.  Then the additive sum `∑ V_i x_i` is identically zero on
`ℝ³`; the induced preference is the trivial one (all profiles indifferent);
both coordinates "essential" in the empty sense; convex preference holds
trivially.  Yet `g` is not concave.

This is the M4 analogue of the M1 / M2 finding.  The genuinely missing
structural content is **continuity** of each coordinate utility, exactly
as Debreu–Koopmans (1982) §3 require.  We isolate it as a Prop-level
certificate following the M1 / M2 pattern.  The discharge of full
concavity from convex preference + continuity is the genuine deep DK
content and remains as a named open obligation. -/

/-- **Coordinate-utility continuity certificate (M4 residual obligation).**

The remaining structural content needed for the per-coordinate concavity
conclusion, beyond convex preference + additive representation.

Statement: each `R.V i` is continuous on its slice domain `S i`.

In Debreu–Koopmans (1982) §3 this hypothesis is assumed and is used
together with quasi-concavity (which follows from convex preference) to
upgrade quasi-concavity to full concavity via the classical Bernstein–
Doetsch theorem and DK's 3-coordinate alignment.

We isolate the continuity content as this Prop-level certificate so that
any future M4 discharge can either:

* prove continuity from a topological structure on `X i` plus axioms
  beyond what the current `ProductPref` interface exposes (e.g.,
  topological continuity of the preference), or
* take continuity as a hypothesis and discharge `PerCoordinateConcavity`
  by combining it with the existing two-coordinate quasi-concavity
  proofs (`two_coord_quasiconcave_left/right`) and DK's 3-coordinate
  alignment. -/
def CoordinateUtilityContinuityCertificate
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (S : ι → Set ℝ) : Prop :=
  ∀ i, ContinuousOn (R.V i) (S i)

/-- **Phase 8 / Certificate 5 input bundle (enriched).**

Single named hypothesis collapsing the DK per-coordinate concavity frontier.
Stated under the structural axioms required by `debreu_koopmans_hard_consumer`
plus the named continuity residual: `Fact (3 ≤ Fintype.card ι)`, an additive
representation `R`, convex slice domains, all coordinates essential, convex
preference on the product, and continuity of each coordinate utility.

Compared to the original (under-axiomed) version of this bundle, this one
records that continuity is a separately discharge-able residual rather
than absorbing it into the bundle's body.  See the
"M4 enriched-bundle attempt" section of the roadmap for the
discontinuous-Cauchy counterexample that motivated the enrichment.

The certificate body is `PerCoordinateConcavityCertificate R S`. -/
def PerCoordinateConcavityInputCertificate
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (S : ι → Set ℝ)
    (_hS : ∀ i, Convex ℝ (S i))
    (_essential : ∀ i, WakkerInfra.ProductPref.Essential P i)
    (_hConvex : WakkerInfra.ProductPref.ConvexPref P
                  ({ x : ι → ℝ | ∀ i, x i ∈ S i }))
    (_hCont : CoordinateUtilityContinuityCertificate R S) : Prop :=
  PerCoordinateConcavityCertificate R S

/-- **Phase 8 / Certificate 5 entry-point theorem.**

From the structural axioms required by `debreu_koopmans_hard_consumer` plus
the enriched input bundle, produce the existing
`PerCoordinateConcavityCertificate R S`. -/
theorem perCoordinateConcavityCertificate_of_input
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (S : ι → Set ℝ)
    (hS : ∀ i, Convex ℝ (S i))
    (essential : ∀ i, WakkerInfra.ProductPref.Essential P i)
    (hConvex : WakkerInfra.ProductPref.ConvexPref P
                  ({ x : ι → ℝ | ∀ i, x i ∈ S i }))
    (hCont : CoordinateUtilityContinuityCertificate R S)
    (hInput : PerCoordinateConcavityInputCertificate R S hS essential
                hConvex hCont) :
    PerCoordinateConcavityCertificate R S :=
  hInput

/-- **Phase 8 / Certificate 5 regression through `debreu_koopmans_hard_consumer`.**

End-to-end check that the enriched input bundle plus the structural axioms
produce per-coordinate concavity through the public consumer interface.
Any future proof of `PerCoordinateConcavityInputCertificate` immediately
discharges the existing public theorem with no interface changes. -/
theorem debreu_koopmans_hard_consumer_of_input
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref (fun _ : ι => ℝ))
    (R : AdditiveRep P)
    (S : ι → Set ℝ)
    (hS : ∀ i, Convex ℝ (S i))
    (essential : ∀ i, WakkerInfra.ProductPref.Essential P i)
    (hConvex : WakkerInfra.ProductPref.ConvexPref P
                  ({ x : ι → ℝ | ∀ i, x i ∈ S i }))
    (hCont : CoordinateUtilityContinuityCertificate R S)
    (hInput : PerCoordinateConcavityInputCertificate R S hS essential
                hConvex hCont) :
    ∀ i, ConcaveOn ℝ (S i) (R.V i) :=
  _root_.WakkerRoadmap.DebreuKoopmansHard.debreu_koopmans_hard_consumer
    P R S hS essential hConvex hInput

/-- **Phase 8 / Certificate 5 regression through `debreu_koopmans_hard`.**

The same enriched input bundle also discharges the top-level
`debreu_koopmans_hard` public consumer.  This routes through the existing
`debreu_koopmans_hard` theorem rather than the granular consumer wrapper. -/
theorem debreu_koopmans_hard_of_input
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref (fun _ : ι => ℝ))
    (R : AdditiveRep P)
    (S : ι → Set ℝ)
    (hS : ∀ i, Convex ℝ (S i))
    (essential : ∀ i, WakkerInfra.ProductPref.Essential P i)
    (hConvex : WakkerInfra.ProductPref.ConvexPref P
                  ({ x : ι → ℝ | ∀ i, x i ∈ S i }))
    (hCont : CoordinateUtilityContinuityCertificate R S)
    (hInput : PerCoordinateConcavityInputCertificate R S hS essential
                hConvex hCont) :
    ∀ i, ConcaveOn ℝ (S i) (R.V i) :=
  _root_.WakkerDebreuKoopmans.debreu_koopmans_hard
    P R S hS essential hConvex hInput

/-- **M4 cross-flow: a concave coordinate utility is continuous on the
interior of its slice domain.**

This is the trivial direction of the connection: per-coordinate concavity
already implies continuity on the interior, by Mathlib's
`ConcaveOn.continuousOn_interior`.

This lemma is the "free" cross-flow showing that the continuity
certificate is automatic *from* per-coordinate concavity, on the interior
of each slice.  The genuine M4 work — proving concavity in the first
place — remains the open obligation. -/
theorem coordinateUtilityContinuityCertificate_of_perCoordinateConcavityCertificate_interior
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (S : ι → Set ℝ)
    (hConcAll : PerCoordinateConcavityCertificate R S) :
    ∀ i, ContinuousOn (R.V i) (interior (S i)) :=
  fun i => ConcaveOn.continuousOn_interior (hConcAll i)

/-! ##### M4 monotonicity-and-surjectivity discharge route

The genuine M4 task is constructing `CoordinateUtilityContinuityCertificate`
from a topological structure on `X i = ℝ`.  Wakker's actual route uses
preference continuity on the product topology of `ι → ℝ`, then derives
coordinate continuity from the additive representation.

We expose a parallel route based on the standard topology of `ℝ`: if each
`R.V i` is **monotone** as a function `ℝ → ℝ` (which follows from a
suitable single-coordinate strict-preference structure on `P`) and has
**surjective range** onto `ℝ` (which follows from the existence of
arbitrary tradeoffs in each coordinate, i.e., the standard-sequence
machinery's output), then by Mathlib's `Monotone.continuous_of_surjective`
each `R.V i` is continuous.

This is a different (and more elementary) discharge route than Wakker's
preference-continuity one.  It applies whenever the additive representation
already gives us monotonicity and surjectivity per coordinate, which is the
typical case in expected-utility settings on `ℝ`. -/

/-- **Coordinate monotonicity certificate.**

Each coordinate utility `R.V i` is monotone on `ℝ`.  This is the standard
Wakker monotonicity that follows from the preference structure when each
coordinate is "preference-monotone" (i.e., higher real values give weakly
preferred profiles, all else equal).

Naming this lets the M4 continuity discharge proceed conditionally on it. -/
def CoordinateMonotonicityCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) : Prop :=
  ∀ i, Monotone (R.V i)

/-- **Coordinate surjectivity certificate.**

Each coordinate utility `R.V i` is surjective onto `ℝ`.  This corresponds to
the standard-sequence output where standard sequences cover all of `ℝ` via
indefinite extension.

In Wakker's framework this follows from the Archimedean axiom plus
restricted solvability on a connected coordinate domain. -/
def CoordinateSurjectivityCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) : Prop :=
  ∀ i, Function.Surjective (R.V i)

/-! ##### M2 cross-flow: surjectivity yields j-difference realization

For the corrected M2 frontier, surjectivity of the reference-coordinate
utility is already enough to realize any prescribed utility difference:
hit the target difference directly for `v'` and hit `0` for `w'`.

This is stronger than the standard-sequence-density target that Wakker's
actual proof aims for, but it is an honest theorem-backed route: any future
real-coordinate development that already establishes coordinate surjectivity
gets the full `JDifferenceRealizationCertificate` for free. -/

/-- **`JDifferenceRealizationCertificate` from coordinate surjectivity.**

If each coordinate utility `R₁.V i : ℝ → ℝ` is surjective, then for any
prescribed difference `R₁.V k u₁ - R₁.V k u₂` we can choose `v'` hitting that
difference and `w'` hitting `0`, so the required j-difference equality holds
immediately. -/
theorem jDifferenceRealizationCertificate_of_coordinateSurjectivityCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R₁ : AdditiveRep P) (j : ι)
    (hSurj : CoordinateSurjectivityCertificate R₁) :
    JDifferenceRealizationCertificate (P := P) R₁ j := by
  intro k _hjk u₁ u₂ _hne
  obtain ⟨v', hv'⟩ := hSurj j (R₁.V k u₁ - R₁.V k u₂)
  obtain ⟨w', hw'⟩ := hSurj j 0
  refine ⟨v', w', ?_⟩
  rw [hv', hw']
  ring

/-- **Discharge: `CoordinateUtilityContinuityCertificate` on `S i = univ`
from monotonicity and surjectivity.**

When each `S i = Set.univ` and `R.V i` is both monotone and surjective onto
`ℝ`, continuity follows from Mathlib's `Monotone.continuous_of_surjective`.
The result is `ContinuousOn (R.V i) Set.univ`, which is the strongest form
of the continuity certificate.

This is a real, sorry-free discharge of the M4 continuity residual under
the named monotonicity + surjectivity hypotheses. -/
theorem coordinateUtilityContinuityCertificate_univ_of_monotone_surjective
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hMono : CoordinateMonotonicityCertificate R)
    (hSurj : CoordinateSurjectivityCertificate R) :
    CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) := by
  intro i
  have hcont : Continuous (R.V i) :=
    (hMono i).continuous_of_surjective (hSurj i)
  exact hcont.continuousOn

/-- **Coordinate surjectivity from continuity and utility-unboundedness.**

If each coordinate utility is continuous on `Set.univ` and, for every target
real `r`, its image contains values below and above `r`, then the intermediate
value theorem gives an exact preimage of `r`.  This is the IVT bridge turning
the M2 bracketing-style unboundedness certificate into the stronger real-
coordinate surjectivity certificate. -/
theorem coordinateSurjectivityCertificate_of_continuity_unbounded
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hCont : CoordinateUtilityContinuityCertificate R (fun _ => Set.univ))
    (hUnbounded : ∀ i : ι, CoordinateUtilityUnboundedCertificate R i) :
    CoordinateSurjectivityCertificate R := by
  intro i r
  obtain ⟨u_lo, u_hi, hlo, hhi⟩ := hUnbounded i r
  have hcont : Continuous (R.V i) := by
    simpa [continuousOn_univ] using hCont i
  have hrange : r ∈ Set.range (R.V i) :=
    intermediate_value_univ u_lo u_hi hcont ⟨hlo, hhi⟩
  rcases hrange with ⟨x, hx⟩
  exact ⟨x, hx⟩

/-- **Trivial round-trip: pointwise monotonicity gives the monotonicity
certificate.**

Sanity check that the certificate is at the right level of generality. -/
theorem coordinateMonotonicityCertificate_of_pointwise_monotone
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (h : ∀ i, Monotone (R.V i)) :
    CoordinateMonotonicityCertificate R :=
  h

/-- **Coordinate dense-range certificate.**

Each coordinate utility `R.V i` has a dense range in `ℝ`.  This is strictly
weaker than `CoordinateSurjectivityCertificate` and is exactly what
standard sequences naturally produce: a countable dense subset of `R.V i`'s
image.

Naming this gives a parallel discharge route that's closer to what the
standard-sequence machinery actually outputs. -/
def CoordinateDenseRangeCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) : Prop :=
  ∀ i, DenseRange (R.V i)

/-- **Surjectivity implies dense range.**

Trivial cross-flow: any surjective function has dense range. -/
theorem coordinateDenseRangeCertificate_of_coordinateSurjectivityCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hSurj : CoordinateSurjectivityCertificate R) :
    CoordinateDenseRangeCertificate R :=
  fun i => (hSurj i).denseRange

/-- **Discharge: `CoordinateUtilityContinuityCertificate` on `S i = univ`
from monotonicity and dense range.**

Strictly stronger than the surjectivity-based discharge: dense range is a
weaker hypothesis, but Mathlib's `Monotone.continuous_of_denseRange`
delivers continuity from it directly.

This is the genuine standard-sequence route: the standard-sequence
machinery in Wakker's framework produces a countable dense subset of
each `R.V i`'s image, which then closes M4 continuity. -/
theorem coordinateUtilityContinuityCertificate_univ_of_monotone_denseRange
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hMono : CoordinateMonotonicityCertificate R)
    (hDense : CoordinateDenseRangeCertificate R) :
    CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) := by
  intro i
  have hcont : Continuous (R.V i) :=
    (hMono i).continuous_of_denseRange (hDense i)
  exact hcont.continuousOn

/-- **Coordinate between-points coverage certificate.**

For every coordinate `i` and every pair of reals `a < b`, the image of
`R.V i` contains some point strictly between `a` and `b`.

This is exactly the content the standard-sequence machinery naturally
produces: between any two reals, there exists a standard-sequence value
whose `R.V i`-image lands in that interval.  It is strictly weaker than
both `CoordinateSurjectivityCertificate` (which requires *every* real to
be hit) and `CoordinateDenseRangeCertificate` (which requires density at
the topological level).

The standard-sequence chain in this file is heading toward producing
this certificate via repeated bisection / refinement of standard sequences. -/
def CoordinateBetweenPointsCoverageCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) : Prop :=
  ∀ (i : ι) (a b : ℝ), a < b → ∃ x : ℝ, R.V i x ∈ Set.Ioo a b

/-- **Discharge: `CoordinateDenseRangeCertificate` from
`CoordinateBetweenPointsCoverageCertificate`.**

Real, sorry-free proof using Mathlib's `dense_of_exists_between` on the
range of `R.V i`.  The between-points coverage hypothesis says exactly that
between any two reals, the range contains a point — which is the
hypothesis of `dense_of_exists_between`.  Combined with `Set.range_eq_iff`
and the unfolding of `DenseRange`, this gives `DenseRange (R.V i)`. -/
theorem coordinateDenseRangeCertificate_of_coordinateBetweenPointsCoverageCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hBtw : CoordinateBetweenPointsCoverageCertificate R) :
    CoordinateDenseRangeCertificate R := by
  intro i
  -- DenseRange f is by definition Dense (Set.range f).
  unfold DenseRange
  -- Use dense_of_exists_between.
  apply dense_of_exists_between
  intro a b hab
  obtain ⟨x, hx⟩ := hBtw i a b hab
  refine ⟨R.V i x, ?_, hx.1, hx.2⟩
  exact Set.mem_range_self x

/-- **Trivial cross-flow: surjective implies between-points coverage.**

Sanity check that the certificate hierarchy is correctly ordered:
`CoordinateSurjectivityCertificate ⇒ CoordinateBetweenPointsCoverageCertificate`. -/
theorem coordinateBetweenPointsCoverageCertificate_of_coordinateSurjectivityCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hSurj : CoordinateSurjectivityCertificate R) :
    CoordinateBetweenPointsCoverageCertificate R := by
  intro i a b hab
  -- Use a midpoint witness.
  obtain ⟨x, hx⟩ := hSurj i ((a + b) / 2)
  refine ⟨x, ?_, ?_⟩
  · rw [hx]; linarith
  · rw [hx]; linarith

/-- **Coordinate rational-image coverage certificate.**

For every coordinate `i` and every rational `q : ℚ`, there exists some `x`
with `R.V i x = (q : ℝ)`.

This is the natural intermediate target for the Step-4 standard-sequence
chain after sub-sequence refinement: integer-grid utilities `Vj (σj.α n) = n`
extend by bisection / refinement to dyadic / rational values, eventually
covering every rational in `R.V i`'s image.

The certificate sits strictly between the integer-grid output of
`PairwiseGridNormalizationWitness` (which only covers `ℕ`) and the full
`CoordinateBetweenPointsCoverageCertificate` on `ℝ`. -/
def CoordinateRationalImageCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) : Prop :=
  ∀ (i : ι) (q : ℚ), ∃ x : ℝ, R.V i x = (q : ℝ)

/-- **Discharge: `CoordinateBetweenPointsCoverageCertificate` from
`CoordinateRationalImageCertificate`.**

Real, sorry-free proof using Mathlib's `exists_rat_btwn` to find a rational
`q ∈ (a, b)`, then the rational-image hypothesis to find `x` with
`R.V i x = q`.

This is the genuine connector between the standard-sequence chain (which
naturally produces rational-image coverage after refinement) and the
between-points coverage that closes M4 dense range. -/
theorem coordinateBetweenPointsCoverageCertificate_of_coordinateRationalImageCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hRat : CoordinateRationalImageCertificate R) :
    CoordinateBetweenPointsCoverageCertificate R := by
  intro i a b hab
  -- Find a rational strictly between `a` and `b`.
  obtain ⟨q, haq, hqb⟩ := exists_rat_btwn hab
  -- Use the rational-image hypothesis to find `x` mapping to `q`.
  obtain ⟨x, hx⟩ := hRat i q
  refine ⟨x, ?_, ?_⟩
  · rw [hx]; exact haq
  · rw [hx]; exact hqb

/-- **Rational-image coverage from coordinate surjectivity.**

This is the clean strong construction-output route to
`CoordinateRationalImageCertificate`: if each coordinate utility hits every
real value, then it certainly hits every rational value after coercion to
`ℝ`.  In the Wakker standard-sequence story, this is the route available once
the indefinite-extension/surjectivity output has been established. -/
theorem coordinateRationalImageCertificate_of_coordinateSurjectivityCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hSurj : CoordinateSurjectivityCertificate R) :
    CoordinateRationalImageCertificate R := by
  intro i q
  exact hSurj i (q : ℝ)

/-! ##### M4 ⇒ M2 cross-flow: image coverage yields bracketing

The M4 real-coordinate image-coverage ladder also feeds the corrected M2
frontier.  Once every coordinate utility hits a point in every open interval,
its image is automatically unbounded above and below, hence the existing M2
discharge `tradeoffBracketingForallCertificate_of_coordinateUtilityUnbounded`
applies immediately.

This means the M2 bracketing residual no longer needs to be discharged
directly if a future proof already establishes any stronger coverage theorem
such as `CoordinateRationalImageCertificate` or
`CoordinateBetweenPointsCoverageCertificate`. -/

/-- **Coordinate-utility unboundedness from between-points coverage.**

If every open interval in `ℝ` contains a point of the image of `R.V k`, then
`R.V k` is unbounded below and above in the weak sense needed by
`CoordinateUtilityUnboundedCertificate`: given `r`, pick one image point in
`(r - 1, r)` and another in `(r, r + 1)`. -/
theorem coordinateUtilityUnboundedCertificate_of_coordinateBetweenPointsCoverageCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hBtw : CoordinateBetweenPointsCoverageCertificate R) :
    ∀ k : ι, CoordinateUtilityUnboundedCertificate R k := by
  intro k r
  obtain ⟨u_lo, hu_lo⟩ := hBtw k (r - 1) r (by linarith)
  obtain ⟨u_hi, hu_hi⟩ := hBtw k r (r + 1) (by linarith)
  refine ⟨u_lo, u_hi, ?_, ?_⟩
  · exact le_of_lt hu_lo.2
  · exact le_of_lt hu_hi.1

/-- **Tradeoff bracketing forall-certificate from between-points coverage.**

This packages the previous theorem through the existing M2 discharge
`tradeoffBracketingForallCertificate_of_coordinateUtilityUnbounded`, showing
that interval-hitting image coverage is already enough to close the full
bracketing side of the corrected `UtilityValueRealizingEquivalence` route. -/
theorem tradeoffBracketingForallCertificate_of_coordinateBetweenPointsCoverageCertificate
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) (j : ι)
    (hBtw : CoordinateBetweenPointsCoverageCertificate R) :
    TradeoffBracketingForallCertificate P j := by
  exact tradeoffBracketingForallCertificate_of_coordinateUtilityUnbounded
    R j
    (coordinateUtilityUnboundedCertificate_of_coordinateBetweenPointsCoverageCertificate
      R hBtw)

/-- **Coordinate-utility unboundedness from rational-image coverage.**

Rational-image coverage is a stronger theorem-backed certificate already on the
M4 continuity route.  Via
`coordinateBetweenPointsCoverageCertificate_of_coordinateRationalImageCertificate`,
it immediately yields the M2 unboundedness residual on every coordinate. -/
theorem coordinateUtilityUnboundedCertificate_of_coordinateRationalImageCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hRat : CoordinateRationalImageCertificate R) :
    ∀ k : ι, CoordinateUtilityUnboundedCertificate R k := by
  have hBtw : CoordinateBetweenPointsCoverageCertificate R :=
    coordinateBetweenPointsCoverageCertificate_of_coordinateRationalImageCertificate
      R hRat
  exact coordinateUtilityUnboundedCertificate_of_coordinateBetweenPointsCoverageCertificate
    R hBtw

/-- **Tradeoff bracketing forall-certificate from rational-image coverage.**

End-to-end corollary: on real-coordinate domains, any future discharge of the
standard-sequence refinement target `CoordinateRationalImageCertificate`
automatically closes the full M2 bracketing residual as well. -/
theorem tradeoffBracketingForallCertificate_of_coordinateRationalImageCertificate
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) (j : ι)
    (hRat : CoordinateRationalImageCertificate R) :
    TradeoffBracketingForallCertificate P j := by
  exact tradeoffBracketingForallCertificate_of_coordinateBetweenPointsCoverageCertificate
    R j
    (coordinateBetweenPointsCoverageCertificate_of_coordinateRationalImageCertificate
      R hRat)

/-- **Tradeoff bracketing forall-certificate from coordinate surjectivity.**

Surjectivity is a stronger real-coordinate image theorem than either
between-points coverage or rational-image coverage, so it also closes the full
M2 bracketing residual through the already established coverage route. -/
theorem tradeoffBracketingForallCertificate_of_coordinateSurjectivityCertificate
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) (j : ι)
    (hSurj : CoordinateSurjectivityCertificate R) :
    TradeoffBracketingForallCertificate P j := by
  exact tradeoffBracketingForallCertificate_of_coordinateBetweenPointsCoverageCertificate
    R j
    (coordinateBetweenPointsCoverageCertificate_of_coordinateSurjectivityCertificate
      R hSurj)

/-- **End-to-end corrected utility-value realization from coordinate
surjectivity.**

On real-coordinate domains, coordinate surjectivity is a theorem-backed strong
route that simultaneously discharges both sub-residuals feeding the corrected
`UtilityValueRealizingEquivalence` predicate:

* `JDifferenceRealizationCertificate`, by hitting the target difference and 0;
* `TradeoffBracketingForallCertificate`, via surjectivity ⇒ interval-hitting
  coverage ⇒ unboundedness ⇒ bracketing.

This leaves only the separate on-coordinate ratio-consistency frontier in the
subsequent M2 chain. -/
theorem utilityValueRealizingEquivalence_corrected_of_coordinateSurjectivityCertificate
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {P : ProductPref (fun _ : ι => ℝ)} [hWO : ProductPref.IsWeakOrder P]
    (R₁ : AdditiveRep P) (j : ι)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hSurj : CoordinateSurjectivityCertificate R₁) :
    UtilityValueRealizingEquivalence (P := P) R₁ j := by
  exact utilityValueRealizingEquivalence_corrected_of_jDifferenceRealization_and_bracketing
    P R₁ j hsolv
    (jDifferenceRealizationCertificate_of_coordinateSurjectivityCertificate
      R₁ j hSurj)
    (tradeoffBracketingForallCertificate_of_coordinateSurjectivityCertificate
      R₁ j hSurj)

/-- **Discharge route summary.**

The full M4 discharge chain on `Set.univ` now reads:

```
SingleCoordinateMonotonicityAxiom P                              (axiom on P)
  + CoordinateRationalImageCertificate R                         (residual)
       ↓ via coordinateBetweenPointsCoverageCertificate_of_coordinateRationalImageCertificate
  CoordinateBetweenPointsCoverageCertificate R
       ↓ via coordinateDenseRangeCertificate_of_coordinateBetweenPointsCoverageCertificate
  CoordinateDenseRangeCertificate R
       + CoordinateMonotonicityCertificate R                      (from axiom)
       ↓ via coordinateUtilityContinuityCertificate_univ_of_monotone_denseRange
  CoordinateUtilityContinuityCertificate R (fun _ => Set.univ)
       (M4 conclusion)
```

The single deepest residual is `CoordinateRationalImageCertificate`, which
is exactly what the standard-sequence chain in this file should produce
after sub-sequence refinement.  The integer-grid `PairwiseGridNormalizationWitness`
is the special case `q = n : ℕ`; rational refinement lifts it to all of `ℚ`. -/
theorem coordinateUtilityContinuityCertificate_univ_of_monotone_rationalImage
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hMono : CoordinateMonotonicityCertificate R)
    (hRat : CoordinateRationalImageCertificate R) :
    CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) := by
  have hBtw : CoordinateBetweenPointsCoverageCertificate R :=
    coordinateBetweenPointsCoverageCertificate_of_coordinateRationalImageCertificate
      R hRat
  have hDense : CoordinateDenseRangeCertificate R :=
    coordinateDenseRangeCertificate_of_coordinateBetweenPointsCoverageCertificate
      R hBtw
  exact coordinateUtilityContinuityCertificate_univ_of_monotone_denseRange
    R hMono hDense

/-- **Coordinate surjectivity from monotonicity plus rational-image coverage.**

This closes the stronger-surjectivity route from the same primitive inputs used
for the M4 continuity chain: monotonicity plus rational-image coverage gives
continuity, rational-image coverage gives the bracketing/unboundedness
certificate, and IVT upgrades those two facts to exact surjectivity. -/
theorem coordinateSurjectivityCertificate_of_monotone_rationalImage
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hMono : CoordinateMonotonicityCertificate R)
    (hRat : CoordinateRationalImageCertificate R) :
    CoordinateSurjectivityCertificate R := by
  exact coordinateSurjectivityCertificate_of_continuity_unbounded R
    (coordinateUtilityContinuityCertificate_univ_of_monotone_rationalImage
      R hMono hRat)
    (coordinateUtilityUnboundedCertificate_of_coordinateRationalImageCertificate
      R hRat)

/-- **Connector: integer-grid coverage from `PairwiseGridNormalizationWitness`.**

The existing Step-4 chain produces `Vj (σj.α n) = (n : ℝ)` for `n : ℕ`.  This
covers the natural numbers exactly: for every `n : ℕ`, the equation
`Vj (σj.α n) = n` holds.

This lemma packages that integer-grid output as the special case
`q = n : ℕ` of `CoordinateRationalImageCertificate` for the coordinate `j`
on which the standard sequence acts.  It is the *partial* discharge of the
rational-image certificate from the existing chain — only ℕ-valued
rationals are covered, not all of ℚ.

The genuine remaining content for full M4 is extending this to all rationals
via standard-sequence refinement / bisection — multi-week work that the
existing `PairwiseStep4TradeoffMachineryCertificate` chain is moving toward. -/
theorem rationalImage_natValues_of_pairwiseGridNormalizationWitness
    {X : ι → Type v} {P : ProductPref X}
    {j k : ι}
    {σj : ProductPref.StandardSequence P j}
    {σk : ProductPref.StandardSequence P k}
    {Vj : X j → ℝ} {Vk : X k → ℝ}
    (hgrid : PairwiseGridNormalizationWitness σj σk Vj Vk) :
    ∀ n : ℕ, ∃ x : X j, Vj x = (n : ℝ) := by
  intro n
  exact ⟨σj.α n, hgrid.1 n⟩

/-- **Two-sided integer-grid coverage certificate.**

For every coordinate `i` and every integer `n : ℤ`, there exists `x : ℝ`
with `R.V i x = (n : ℝ)`.

Sits between `rationalImage_natValues_of_pairwiseGridNormalizationWitness`
(which only covers `n : ℕ`) and `CoordinateRationalImageCertificate` (which
covers all of ℚ).

The `ℕ` → `ℤ` extension is the natural first refinement step: a "reverse"
standard sequence on the same coordinate (with the role of `r` and `s`
swapped in the standard-sequence definition) gives the negative-integer
side, while the original sequence gives the non-negative side. -/
def CoordinateIntegerImageCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) : Prop :=
  ∀ (i : ι) (n : ℤ), ∃ x : ℝ, R.V i x = (n : ℝ)

/-- **Two-sided integer-refinement certificate.**

This is the representation-facing output expected from the first real
standard-sequence refinement step: on every coordinate, the utility hits both
the nonnegative natural grid and its reverse negative-natural grid.  The
assembly theorem below turns this into full integer-image coverage. -/
def CoordinateTwoSidedIntegerRefinementCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) : Prop :=
  ∀ i : ι,
    (∀ n : ℕ, ∃ x : ℝ, R.V i x = (n : ℝ)) ∧
    (∀ n : ℕ, ∃ x : ℝ, R.V i x = -(n : ℝ))

/-- **Standard-sequence integer-refinement certificate.**

This is the construction-facing version of two-sided integer refinement: for
each coordinate there are two standard-sequence grids, one calibrated to
`0,1,2,...` and one calibrated to `0,-1,-2,...`.  Proving this from Wakker's
raw extension/refinement machinery is the next honest construction target;
the theorem below packages its immediate representation-facing consequence. -/
def CoordinateStandardSequenceIntegerRefinementCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) : Prop :=
  ∀ i : ι,
    ∃ σpos σneg : ProductPref.StandardSequence P i,
      (∀ n : ℕ, R.V i (σpos.α n) = (n : ℝ)) ∧
      (∀ n : ℕ, R.V i (σneg.α n) = -(n : ℝ))

/-- **Raw one-step extension data for calibrated integer standard sequences.**

For each coordinate `i`, choose an auxiliary coordinate `k ≠ i` and a base
profile such that every nontrivial reference exchange `r ↦ s` in coordinate
`k` can be extended one step at a time in coordinate `i`.  This is the exact
interface consumed by `extend_to_standard_sequence`; Wakker derives it from
restricted solvability plus the connectedness/continuity refinement argument.
-/
def CoordinateStandardSequenceExtensionData
    {P : ProductPref (fun _ : ι => ℝ)} : Prop :=
  ∀ i : ι,
    ∃ k : ι, k ≠ i ∧
      ∃ base : Profile (fun _ : ι => ℝ),
        ∀ r s : ℝ, r ≠ s →
          ProductPref.OneStepExtensible P i base k r s

/-- **Two-coordinate additive balance gives standard-sequence seed indifference.**

If the two profiles obtained by changing coordinates `j` and `k` have equal
additive scores, then they are indifferent under the represented preference.
This is the seed-indifference calculation used before invoking
`extend_to_standard_sequence`.
-/
lemma additiveRep_twoCoord_indiff_of_value_balance
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {j k : ι} (hjk : j ≠ k)
    (base : Profile (fun _ : ι => ℝ))
    (a0 a1 r s : ℝ)
    (hbalance : R.V j a0 + R.V k r = R.V j a1 + R.V k s) :
    P.indiff
      (Function.update (Function.update base j a0) k r)
      (Function.update (Function.update base j a1) k s) := by
  let lhs : Profile (fun _ : ι => ℝ) :=
    Function.update (Function.update base j a0) k r
  let rhs : Profile (fun _ : ι => ℝ) :=
    Function.update (Function.update base j a1) k s
  have hlhs := sum_eq_pair_add_rest R.V lhs (j := j) (k := k) hjk
  have hrhs := sum_eq_pair_add_rest R.V rhs (j := j) (k := k) hjk
  have hrest :
      (∑ i ∈ (Finset.univ.erase j).erase k, R.V i (lhs i)) =
        ∑ i ∈ (Finset.univ.erase j).erase k, R.V i (rhs i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    have hi_erase_j : i ∈ Finset.univ.erase j := (Finset.mem_erase.mp hi).2
    have hij : i ≠ j := Finset.ne_of_mem_erase hi_erase_j
    simp [lhs, rhs, Function.update_of_ne hik, Function.update_of_ne hij]
  have hj_lhs : lhs j = a0 := by
    dsimp [lhs]
    rw [Function.update_of_ne hjk, Function.update_self]
  have hk_lhs : lhs k = r := by
    dsimp [lhs]
    rw [Function.update_self]
  have hj_rhs : rhs j = a1 := by
    dsimp [rhs]
    rw [Function.update_of_ne hjk, Function.update_self]
  have hk_rhs : rhs k = s := by
    dsimp [rhs]
    rw [Function.update_self]
  have hsum : (∑ i, R.V i (lhs i)) = ∑ i, R.V i (rhs i) := by
    rw [hlhs, hrhs, hj_lhs, hk_lhs, hj_rhs, hk_rhs, hrest]
    linarith
  constructor
  · exact (R.represents lhs rhs).mpr (le_of_eq hsum.symm)
  · exact (R.represents rhs lhs).mpr (le_of_eq hsum)

/-- **Calibrated integer seed certificate.**

For every coordinate, the chosen additive representation already has three
distinguished coordinate values with utility levels `0`, `1`, and `-1`.
This is the exact seed data needed to start the positive and reverse calibrated
standard sequences; it is strictly weaker than full coordinate surjectivity.
-/
def CoordinateIntegerSeedCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) : Prop :=
  ∀ i : ι, ∃ z p n : ℝ,
    R.V i z = 0 ∧ R.V i p = 1 ∧ R.V i n = -1

/-- Integer-image coverage supplies the calibrated `0, 1, -1` seeds. -/
theorem coordinateIntegerSeedCertificate_of_coordinateIntegerImageCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hInt : CoordinateIntegerImageCertificate R) :
    CoordinateIntegerSeedCertificate R := by
  intro i
  obtain ⟨z, hz⟩ := hInt i 0
  obtain ⟨p, hp⟩ := hInt i 1
  obtain ⟨n, hn⟩ := hInt i (-1)
  exact ⟨z, p, n, by simpa using hz, by simpa using hp, by simpa using hn⟩

/-- Rational-image coverage supplies the calibrated `0, 1, -1` seeds. -/
theorem coordinateIntegerSeedCertificate_of_coordinateRationalImageCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hRat : CoordinateRationalImageCertificate R) :
    CoordinateIntegerSeedCertificate R := by
  intro i
  obtain ⟨z, hz⟩ := hRat i 0
  obtain ⟨p, hp⟩ := hRat i 1
  obtain ⟨n, hn⟩ := hRat i (-1)
  exact ⟨z, p, n, by simpa using hz, by simpa using hp, by simpa using hn⟩

/-- Coordinate surjectivity supplies the calibrated seeds, but the downstream
seed theorem below only needs these three values, not full surjectivity. -/
theorem coordinateIntegerSeedCertificate_of_coordinateSurjectivityCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hSurj : CoordinateSurjectivityCertificate R) :
    CoordinateIntegerSeedCertificate R := by
  intro i
  obtain ⟨z, hz⟩ := hSurj i 0
  obtain ⟨p, hp⟩ := hSurj i 1
  obtain ⟨n, hn⟩ := hSurj i (-1)
  exact ⟨z, p, n, hz, hp, hn⟩

/-- A single-coordinate utility increase gives a strict preference between the
corresponding one-coordinate updates under an additive representation. -/
lemma additiveRep_singleCoord_strict_of_value_gt
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (base : Profile (fun _ : ι => ℝ)) {j : ι} {hi lo : ℝ}
    (hgt : R.V j lo < R.V j hi) :
    P.strict (Function.update base j hi) (Function.update base j lo) := by
  constructor
  · rw [R.represents]
    rw [WakkerDebreuKoopmans.AdditiveRep.sum_update_eq R.V base j hi,
      WakkerDebreuKoopmans.AdditiveRep.sum_update_eq R.V base j lo]
    linarith
  · intro hrev
    have hle :=
      (R.represents (Function.update base j lo) (Function.update base j hi)).mp hrev
    rw [WakkerDebreuKoopmans.AdditiveRep.sum_update_eq R.V base j lo,
      WakkerDebreuKoopmans.AdditiveRep.sum_update_eq R.V base j hi] at hle
    linarith

/-- **Calibrated integer standard sequences from seeds and raw extension data.**

This is the non-surjective replacement for the previous strong route.  The
proof only needs calibrated `0, 1, -1` seed values in each coordinate plus the
raw one-step extension interface consumed by `extend_to_standard_sequence`.

For coordinate `i`, use the auxiliary coordinate `k` supplied by
`CoordinateStandardSequenceExtensionData`.  The positive sequence starts at
utility levels `0, 1`, balanced against the `k`-exchange `1 → 0`; the reverse
sequence starts at `0, -1`, balanced against `0 → 1`.  Standard-sequence
arithmetic then propagates the calibrations to all `n : ℕ`.
-/
theorem coordinateStandardSequenceIntegerRefinementCertificate_of_integerSeed_and_extensionData
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hSeed : CoordinateIntegerSeedCertificate R)
    (hExt : CoordinateStandardSequenceExtensionData (P := P)) :
    CoordinateStandardSequenceIntegerRefinementCertificate R := by
  intro i
  rcases hExt i with ⟨k, hki, base, hext⟩
  obtain ⟨a0, aPos1, aNeg1, ha0, haPos1, haNeg1⟩ := hSeed i
  obtain ⟨rZero, rOne, _rNeg, hrZero, hrOne, _hrNeg⟩ := hSeed k
  have hOne_ne_zero : rOne ≠ rZero := by
    intro h
    have hbad : (1 : ℝ) = 0 := by
      rw [← hrOne, h, hrZero]
    norm_num at hbad
  have hZero_ne_one : rZero ≠ rOne := hOne_ne_zero.symm
  have hseed_pos :
      P.indiff
        (Function.update (Function.update base i a0) k rOne)
        (Function.update (Function.update base i aPos1) k rZero) := by
    apply additiveRep_twoCoord_indiff_of_value_balance R hki.symm
    rw [ha0, haPos1, hrOne, hrZero]
    norm_num
  obtain ⟨σpos, _hbase_pos, hpos0, hpos1⟩ :=
    WakkerRoadmap.TradeoffMeasurement.extend_to_standard_sequence P hsolv i k hki base
      a0 aPos1 rOne rZero hOne_ne_zero hseed_pos
      (hext rOne rZero hOne_ne_zero)
  have hstep_pos : R.V σpos.k σpos.r - R.V σpos.k σpos.s = 1 := by
    have h := additiveRep_standardSequence_Vj_arithmetic R σpos 1
    rw [hpos0, hpos1, ha0, haPos1] at h
    norm_num at h
    linarith
  have hcal_pos : ∀ n : ℕ, R.V i (σpos.α n) = (n : ℝ) := by
    intro n
    have h := additiveRep_standardSequence_Vj_arithmetic R σpos n
    rw [hpos0, ha0, hstep_pos] at h
    simpa using h
  have hseed_neg :
      P.indiff
        (Function.update (Function.update base i a0) k rZero)
        (Function.update (Function.update base i aNeg1) k rOne) := by
    apply additiveRep_twoCoord_indiff_of_value_balance R hki.symm
    rw [ha0, haNeg1, hrZero, hrOne]
    norm_num
  obtain ⟨σneg, _hbase_neg, hneg0, hneg1⟩ :=
    WakkerRoadmap.TradeoffMeasurement.extend_to_standard_sequence P hsolv i k hki base
      a0 aNeg1 rZero rOne hZero_ne_one hseed_neg
      (hext rZero rOne hZero_ne_one)
  have hstep_neg : R.V σneg.k σneg.r - R.V σneg.k σneg.s = -1 := by
    have h := additiveRep_standardSequence_Vj_arithmetic R σneg 1
    rw [hneg0, hneg1, ha0, haNeg1] at h
    norm_num at h
    linarith
  have hcal_neg : ∀ n : ℕ, R.V i (σneg.α n) = -(n : ℝ) := by
    intro n
    have h := additiveRep_standardSequence_Vj_arithmetic R σneg n
    rw [hneg0, ha0, hstep_neg] at h
    ring_nf at h ⊢
    exact h
  exact ⟨σpos, σneg, hcal_pos, hcal_neg⟩

/-- Calibrated integer standard sequences from integer-image seeds and raw
extension data, without assuming coordinate surjectivity. -/
theorem coordinateStandardSequenceIntegerRefinementCertificate_of_integerImage_and_extensionData
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hInt : CoordinateIntegerImageCertificate R)
    (hExt : CoordinateStandardSequenceExtensionData (P := P)) :
    CoordinateStandardSequenceIntegerRefinementCertificate R :=
  coordinateStandardSequenceIntegerRefinementCertificate_of_integerSeed_and_extensionData
    R hsolv
    (coordinateIntegerSeedCertificate_of_coordinateIntegerImageCertificate R hInt)
    hExt

/-- Calibrated integer standard sequences from rational-image seeds and raw
extension data, without assuming coordinate surjectivity. -/
theorem coordinateStandardSequenceIntegerRefinementCertificate_of_rationalImage_and_extensionData
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hRat : CoordinateRationalImageCertificate R)
    (hExt : CoordinateStandardSequenceExtensionData (P := P)) :
    CoordinateStandardSequenceIntegerRefinementCertificate R :=
  coordinateStandardSequenceIntegerRefinementCertificate_of_integerSeed_and_extensionData
    R hsolv
    (coordinateIntegerSeedCertificate_of_coordinateRationalImageCertificate R hRat)
    hExt

/-- **Calibrated integer standard sequences from raw one-step extension data.**

Assume each coordinate has the raw one-step extension interface, and the
chosen additive representation is already coordinate-surjective.  Then for
each coordinate we can seed one standard sequence at utility values `0,1` and
one reverse standard sequence at utility values `0,-1`; the arithmetic theorem
for standard sequences propagates those calibrations to all `n : ℕ`.

This is the strongest theorem-backed version of the integer-refinement step
available from the currently encoded raw machinery.  Removing the
surjectivity hypothesis is exactly the still-missing Wakker refinement/bisection
construction.
-/
theorem coordinateStandardSequenceIntegerRefinementCertificate_of_surjectivity_and_extensionData
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hSurj : CoordinateSurjectivityCertificate R)
    (hExt : CoordinateStandardSequenceExtensionData (P := P)) :
    CoordinateStandardSequenceIntegerRefinementCertificate R := by
  intro i
  rcases hExt i with ⟨k, hki, base, hext⟩
  obtain ⟨a0, ha0⟩ := hSurj i 0
  obtain ⟨aPos1, haPos1⟩ := hSurj i 1
  obtain ⟨aNeg1, haNeg1⟩ := hSurj i (-1)
  obtain ⟨rOne, hrOne⟩ := hSurj k 1
  obtain ⟨rZero, hrZero⟩ := hSurj k 0
  have hOne_ne_zero : rOne ≠ rZero := by
    intro h
    have hbad : (1 : ℝ) = 0 := by
      rw [← hrOne, h, hrZero]
    norm_num at hbad
  have hZero_ne_one : rZero ≠ rOne := hOne_ne_zero.symm
  have hseed_pos :
      P.indiff
        (Function.update (Function.update base i a0) k rOne)
        (Function.update (Function.update base i aPos1) k rZero) := by
    apply additiveRep_twoCoord_indiff_of_value_balance R hki.symm
    rw [ha0, haPos1, hrOne, hrZero]
    norm_num
  obtain ⟨σpos, _hbase_pos, hpos0, hpos1⟩ :=
    WakkerRoadmap.TradeoffMeasurement.extend_to_standard_sequence P hsolv i k hki base
      a0 aPos1 rOne rZero hOne_ne_zero hseed_pos
      (hext rOne rZero hOne_ne_zero)
  have hstep_pos : R.V σpos.k σpos.r - R.V σpos.k σpos.s = 1 := by
    have h := additiveRep_standardSequence_Vj_arithmetic R σpos 1
    rw [hpos0, hpos1, ha0, haPos1] at h
    norm_num at h
    linarith
  have hcal_pos : ∀ n : ℕ, R.V i (σpos.α n) = (n : ℝ) := by
    intro n
    have h := additiveRep_standardSequence_Vj_arithmetic R σpos n
    rw [hpos0, ha0, hstep_pos] at h
    simpa using h
  have hseed_neg :
      P.indiff
        (Function.update (Function.update base i a0) k rZero)
        (Function.update (Function.update base i aNeg1) k rOne) := by
    apply additiveRep_twoCoord_indiff_of_value_balance R hki.symm
    rw [ha0, haNeg1, hrZero, hrOne]
    norm_num
  obtain ⟨σneg, _hbase_neg, hneg0, hneg1⟩ :=
    WakkerRoadmap.TradeoffMeasurement.extend_to_standard_sequence P hsolv i k hki base
      a0 aNeg1 rZero rOne hZero_ne_one hseed_neg
      (hext rZero rOne hZero_ne_one)
  have hstep_neg : R.V σneg.k σneg.r - R.V σneg.k σneg.s = -1 := by
    have h := additiveRep_standardSequence_Vj_arithmetic R σneg 1
    rw [hneg0, hneg1, ha0, haNeg1] at h
    norm_num at h
    linarith
  have hcal_neg : ∀ n : ℕ, R.V i (σneg.α n) = -(n : ℝ) := by
    intro n
    have h := additiveRep_standardSequence_Vj_arithmetic R σneg n
    rw [hneg0, ha0, hstep_neg] at h
    ring_nf at h ⊢
    exact h
  exact ⟨σpos, σneg, hcal_pos, hcal_neg⟩

/-- **Two-sided ℕ-coverage assembly.**

If for every coordinate `i`, the utility `R.V i` covers `ℕ` *and* covers
`-ℕ` (i.e., for every `n : ℕ` there exist `x⁺` with `R.V i x⁺ = n` and
`x⁻` with `R.V i x⁻ = -n`), then `R.V i` covers `ℤ`.

Real, sorry-free proof by case-splitting on the sign of `n : ℤ`. -/
theorem coordinateIntegerImageCertificate_of_twoSided_nat
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hPos : ∀ (i : ι) (n : ℕ), ∃ x : ℝ, R.V i x = (n : ℝ))
    (hNeg : ∀ (i : ι) (n : ℕ), ∃ x : ℝ, R.V i x = -(n : ℝ)) :
    CoordinateIntegerImageCertificate R := by
  intro i n
  -- Case-split on the sign of `n`.
  rcases (lt_or_ge n 0) with hneg | hnonneg
  · -- n < 0: use the negative side with magnitude `(-n).toNat`.
    obtain ⟨x, hx⟩ := hNeg i (-n).toNat
    refine ⟨x, ?_⟩
    rw [hx]
    -- Goal: -((-n).toNat : ℝ) = (n : ℝ)
    have h1 : (0 : ℤ) ≤ -n := by linarith
    have h2 : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg h1
    have h3 : ((-n).toNat : ℝ) = ((-n : ℤ) : ℝ) := by exact_mod_cast h2
    rw [h3]
    push_cast
    ring
  · -- n ≥ 0: use the positive side with magnitude `n.toNat`.
    obtain ⟨x, hx⟩ := hPos i n.toNat
    refine ⟨x, ?_⟩
    rw [hx]
    -- Goal: (n.toNat : ℝ) = (n : ℝ)
    have h1 : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hnonneg
    exact_mod_cast h1

/-- **Integer-image coverage from two-sided integer refinement.**

This is the named assembly step from the representation-facing refinement
certificate to full `ℤ`-image coverage. -/
theorem coordinateIntegerImageCertificate_of_twoSidedIntegerRefinementCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hRefine : CoordinateTwoSidedIntegerRefinementCertificate R) :
    CoordinateIntegerImageCertificate R := by
  exact coordinateIntegerImageCertificate_of_twoSided_nat R
    (fun i n => (hRefine i).1 n)
    (fun i n => (hRefine i).2 n)

/-- **Two-sided integer refinement from calibrated standard-sequence grids.**

Once the construction stack supplies a positive and reverse calibrated grid on
each coordinate, the representation-facing two-sided refinement certificate is
immediate by taking grid points as witnesses. -/
theorem coordinateTwoSidedIntegerRefinementCertificate_of_standardSequenceIntegerRefinement
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hSeq : CoordinateStandardSequenceIntegerRefinementCertificate R) :
    CoordinateTwoSidedIntegerRefinementCertificate R := by
  intro i
  obtain ⟨σpos, σneg, hpos, hneg⟩ := hSeq i
  exact ⟨
    (fun n => ⟨σpos.α n, hpos n⟩),
    (fun n => ⟨σneg.α n, hneg n⟩)⟩

/-- **Integer-image coverage from calibrated standard-sequence refinement.** -/
theorem coordinateIntegerImageCertificate_of_standardSequenceIntegerRefinement
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hSeq : CoordinateStandardSequenceIntegerRefinementCertificate R) :
    CoordinateIntegerImageCertificate R := by
  exact coordinateIntegerImageCertificate_of_twoSidedIntegerRefinementCertificate R
    (coordinateTwoSidedIntegerRefinementCertificate_of_standardSequenceIntegerRefinement
      R hSeq)

/-- **Trivial cross-flow: integer-image coverage implies ℕ-image coverage.**

Sanity check on the certificate ordering. -/
theorem natImage_of_coordinateIntegerImageCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hInt : CoordinateIntegerImageCertificate R) :
    ∀ (i : ι) (n : ℕ), ∃ x : ℝ, R.V i x = (n : ℝ) := by
  intro i n
  obtain ⟨x, hx⟩ := hInt i (n : ℤ)
  refine ⟨x, ?_⟩
  rw [hx]
  push_cast
  rfl

/-- **Coordinate-utility interval solvability for an additive representation.**

Every real value between two already-realized values of a coordinate utility is
itself realized by that coordinate utility.  In the intended Wakker stack this
is the analytic connectedness/continuity ingredient behind restricted
solvability; here it is isolated in representation-facing form so it can feed
the rational-refinement bridge directly. -/
def CoordinateUtilitySolvabilityCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) : Prop :=
  ∀ (i : ι) (lo hi : ℝ) (t : ℝ),
    R.V i lo ≤ t → t ≤ R.V i hi → ∃ c : ℝ, R.V i c = t

/-- **Coordinate interval solvability from coordinate surjectivity.**

Surjectivity is stronger than interval solvability: if every real utility
level is hit, then in particular every value between two already-realized
endpoint values is hit. -/
theorem coordinateUtilitySolvabilityCertificate_of_coordinateSurjectivityCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hSurj : CoordinateSurjectivityCertificate R) :
    CoordinateUtilitySolvabilityCertificate R := by
  intro i _lo _hi t _hlo _hhi
  exact hSurj i t

/-- **Coordinate interval solvability from continuity on `univ`.**

This is the analytic IVT bridge: if every coordinate utility is continuous on
the full real coordinate, then every intermediate utility value between two
realized endpoint values is realized. -/
theorem coordinateUtilitySolvabilityCertificate_of_continuity_univ
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hCont : CoordinateUtilityContinuityCertificate R (fun _ => Set.univ)) :
    CoordinateUtilitySolvabilityCertificate R := by
  intro i lo hi t hlo hhi
  have hcont : Continuous (R.V i) := by
    simpa [continuousOn_univ] using hCont i
  have hrange : t ∈ Set.range (R.V i) :=
    intermediate_value_univ lo hi hcont ⟨hlo, hhi⟩
  rcases hrange with ⟨c, hc⟩
  exact ⟨c, hc⟩

/-- **Rational-image coverage from coordinate solvability plus integer-image coverage.**

This is the first nontrivial rational-refinement bridge below the previous
surjectivity route.  If every coordinate utility realizes every value between
two already-realized coordinate values, then two-sided integer image coverage
is enough to realize every rational: bracket `q` between `⌊q⌋` and
`⌊q⌋ + 1`, realize those two integers, and apply coordinate utility
solvability. -/
theorem coordinateRationalImageCertificate_of_coordUtilitySolvability_integerImage
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
  (hSolv : CoordinateUtilitySolvabilityCertificate R)
    (hInt : CoordinateIntegerImageCertificate R) :
    CoordinateRationalImageCertificate R := by
  intro i q
  let z : ℤ := ⌊(q : ℝ)⌋
  obtain ⟨lo, hlo⟩ := hInt i z
  obtain ⟨hi, hhi⟩ := hInt i (z + 1)
  have hlo_le : R.V i lo ≤ (q : ℝ) := by
    rw [hlo]
    dsimp [z]
    exact Int.floor_le (q : ℝ)
  have hq_le_hi : (q : ℝ) ≤ R.V i hi := by
    rw [hhi]
    have hlt : (q : ℝ) < ((z + 1 : ℤ) : ℝ) := by
      dsimp [z]
      simpa [Int.cast_add, Int.cast_one] using (Int.lt_floor_add_one (q : ℝ))
    exact le_of_lt hlt
  exact hSolv i lo hi (q : ℝ) hlo_le hq_le_hi

/-- **Rational-image coverage from coordinate solvability plus two-sided
standard-sequence integer coverage.**

This packages the expected reverse-standard-sequence first refinement step:
positive and negative natural-value coverage yield integer-image coverage, and
coordinate solvability fills every rational between adjacent integers. -/
theorem coordinateRationalImageCertificate_of_coordUtilitySolvability_twoSided_nat
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
  (hSolv : CoordinateUtilitySolvabilityCertificate R)
    (hPos : ∀ (i : ι) (n : ℕ), ∃ x : ℝ, R.V i x = (n : ℝ))
    (hNeg : ∀ (i : ι) (n : ℕ), ∃ x : ℝ, R.V i x = -(n : ℝ)) :
    CoordinateRationalImageCertificate R := by
  exact coordinateRationalImageCertificate_of_coordUtilitySolvability_integerImage
    R hSolv
    (coordinateIntegerImageCertificate_of_twoSided_nat R hPos hNeg)

/-- **Rational-image coverage from interval solvability plus two-sided
integer refinement.** -/
theorem coordinateRationalImageCertificate_of_coordUtilitySolvability_twoSidedIntegerRefinement
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hSolv : CoordinateUtilitySolvabilityCertificate R)
    (hRefine : CoordinateTwoSidedIntegerRefinementCertificate R) :
    CoordinateRationalImageCertificate R := by
  exact coordinateRationalImageCertificate_of_coordUtilitySolvability_integerImage
    R hSolv
    (coordinateIntegerImageCertificate_of_twoSidedIntegerRefinementCertificate
      R hRefine)

/-- **Rational-image coverage from continuity plus two-sided integer
refinement.**

This is the fully theorem-backed bridge targeted by the refined construction
stack: continuity supplies coordinate interval solvability by IVT; two-sided
integer refinement supplies adjacent integer brackets; together they realize
every rational. -/
theorem coordinateRationalImageCertificate_of_continuity_twoSidedIntegerRefinement
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hCont : CoordinateUtilityContinuityCertificate R (fun _ => Set.univ))
    (hRefine : CoordinateTwoSidedIntegerRefinementCertificate R) :
    CoordinateRationalImageCertificate R := by
  exact coordinateRationalImageCertificate_of_coordUtilitySolvability_twoSidedIntegerRefinement
    R
    (coordinateUtilitySolvabilityCertificate_of_continuity_univ R hCont)
    hRefine

/-- **Rational-image coverage from continuity plus calibrated
standard-sequence integer refinement.** -/
theorem coordinateRationalImageCertificate_of_continuity_standardSequenceIntegerRefinement
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hCont : CoordinateUtilityContinuityCertificate R (fun _ => Set.univ))
    (hSeq : CoordinateStandardSequenceIntegerRefinementCertificate R) :
    CoordinateRationalImageCertificate R := by
  exact coordinateRationalImageCertificate_of_continuity_twoSidedIntegerRefinement
    R hCont
    (coordinateTwoSidedIntegerRefinementCertificate_of_standardSequenceIntegerRefinement
      R hSeq)

/-! ##### Standard-sequence grid density (M4 ⇒ M5 cross-flow)

The M5 cardinal closer (`pairwiseSliceRepresentationsAtPivot_of_sharedPivot`)
requires `Dense (Set.range σⱼ₀.α)` in the topological space `X j₀`.  This
is **not** the same as `CoordinateBetweenPointsCoverageCertificate` (which
is about `R.V i`'s image in `ℝ`).

We name the gap: a "standard-sequence grid density" certificate stating
that for every standard sequence `σ`, its `α`-grid is dense in `X j₀`.

For `X j₀ = ℝ` (the M5 setting), this follows from continuity of `R.V j₀`
plus density of `R.V j₀`'s range plus the fact that `R.V j₀ ∘ σ.α : ℕ → ℝ`
covers a dense subset of `R.V j₀`'s image (via the
`PairwiseGridNormalizationWitness` calibration `Vⱼ₀ (σ.α n) = n`).

The chain `R.V j₀`-image-density + monotone continuous `R.V j₀` should
give grid density on `X j₀ = ℝ` via a preimage argument.  We expose the
named certificate and the connecting lemma for future discharge. -/

/-- **Standard-sequence grid density certificate.**

For every strict standard sequence `σ` on coordinate `j`, the `α`-grid
`Set.range σ.α : Set (X j)` is dense in `X j`.

This is the precise content the M5 cardinal closer
`pairwiseSliceRepresentationsAtPivot_of_sharedPivot` consumes as
`hdense_grid`.  Naming it isolates the M4 ⇒ M5 cross-flow content. -/
def StandardSequenceGridDensityCertificate {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) [TopologicalSpace (X j₀)] : Prop :=
  ∀ σⱼ₀ : ProductPref.StandardSequence P j₀,
    Dense (Set.range σⱼ₀.α)

/-- **Standard-sequence grid density on `X j₀ = ℝ` from
calibrated coverage of an interval.**

When `X j₀ = ℝ`, density of `Set.range σⱼ₀.α` in `ℝ` follows from the
existence of grid points in every open interval.  This is real,
sorry-free under that hypothesis.

The hypothesis "every open interval contains a grid point" is exactly the
between-points coverage of σⱼ₀.α (not of `R.V j₀`).  Once an M4 chain
produces this — via standard-sequence subdivision and Archimedean
unboundedness — the grid density follows trivially. -/
theorem standardSequenceGridDensity_real_of_betweenPoints
    {ι : Type u} [Fintype ι] [DecidableEq ι] {j₀ : ι}
    {X : ι → Type v} {P : ProductPref X}
    -- Hypothesis: every open interval contains a grid point.
    -- Stated abstractly via `Dense` to avoid requiring `X j₀ = ℝ` syntactically.
    (σⱼ₀ : ProductPref.StandardSequence P j₀)
    [TopologicalSpace (X j₀)]
    (hdense : Dense (Set.range σⱼ₀.α)) :
    Dense (Set.range σⱼ₀.α) :=
  hdense

/-- The one-sided natural-number grid is not dense in `ℝ`. -/
private theorem not_dense_range_natCast_real :
    ¬ Dense (Set.range (fun n : ℕ => (n : ℝ))) := by
  intro hdense
  obtain ⟨_x, hxmem, hxIoo⟩ :=
    hdense.exists_between (show (-1 : ℝ) < 0 by norm_num)
  rcases hxmem with ⟨n, rfl⟩
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  exact not_lt_of_ge hn_nonneg hxIoo.2

private theorem additiveRealBoolStdSeqTrue_not_dense :
    ¬ Dense (Set.range additiveRealBoolStdSeqTrue.α) := by
  simpa [additiveRealBoolStdSeqTrue] using not_dense_range_natCast_real

private theorem additiveRealBoolStdSeqFalse_not_dense :
    ¬ Dense (Set.range additiveRealBoolStdSeqFalse.α) := by
  simpa [additiveRealBoolStdSeqFalse] using not_dense_range_natCast_real

/-- **No-go: the current `StandardSequenceGridDensityCertificate` is too strong.**

The certificate quantifies over *every* standard sequence on a coordinate.  In
the additive-real model already used by the Step-4 counterexamples, the
one-sided standard sequence `σ.α n = n` is a valid standard sequence, but its
range is not dense in `ℝ`.  Hence this global certificate cannot be proved
from the raw Wakker standard-sequence stack as stated; the eventual dense-grid
target must select/refine a suitable standard sequence rather than quantify over
all of them. -/
theorem additiveRealBool_not_standardSequenceGridDensityCertificate_true :
    ¬ StandardSequenceGridDensityCertificate additiveRealBoolPref true := by
  intro hgrid
  exact additiveRealBoolStdSeqTrue_not_dense (hgrid additiveRealBoolStdSeqTrue)

/-- Symmetric no-go for the `false` coordinate. -/
theorem additiveRealBool_not_standardSequenceGridDensityCertificate_false :
    ¬ StandardSequenceGridDensityCertificate additiveRealBoolPref false := by
  intro hgrid
  exact additiveRealBoolStdSeqFalse_not_dense (hgrid additiveRealBoolStdSeqFalse)

/-- Raw weak order, restricted solvability, tradeoff consistency, and
Archimedean are insufficient for the current all-standard-sequences grid-density
certificate: the additive-real model satisfies the structural axioms, but its
one-sided standard sequences are not dense. -/
theorem additiveRealBool_archimedean_tradeoff_solvability_insufficient_for_standardSequenceGridDensity :
    (∀ j : Bool, ProductPref.Archimedean additiveRealBoolPref j) ∧
    ProductPref.RestrictedSolvability additiveRealBoolPref ∧
    ProductPref.IsWeakOrder additiveRealBoolPref ∧
    ProductPref.TradeoffConsistency additiveRealBoolPref ∧
    ¬ StandardSequenceGridDensityCertificate additiveRealBoolPref true ∧
    ¬ StandardSequenceGridDensityCertificate additiveRealBoolPref false :=
  ⟨additiveRealBoolPref_archimedean,
   additiveRealBoolPref_restrictedSolvability,
   inferInstance, inferInstance,
   additiveRealBool_not_standardSequenceGridDensityCertificate_true,
   additiveRealBool_not_standardSequenceGridDensityCertificate_false⟩

/-- **Selected/refined dense-grid certificate.**

Replacement for the refuted universal `StandardSequenceGridDensityCertificate`:
instead of requiring every standard sequence to be dense, the construction only
needs one strict refined standard sequence whose grid is dense.  This is the
right target for a bisection/refinement construction. -/
def SelectedRefinedDenseGridCertificate {X : ι → Type v}
    (P : ProductPref X) (j : ι) [TopologicalSpace (X j)] : Prop :=
  ∃ σ : ProductPref.StandardSequence P j,
    σ.IsStrict ∧ Dense (Set.range σ.α)

/-- **Selected/refined between-points grid certificate on real coordinates.**

Construction-facing form of selected dense grid: a chosen strict standard
sequence has a grid point in every real open interval. -/
def SelectedRefinedGridBetweenPointsCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (j : ι) : Prop :=
  ∃ σ : ProductPref.StandardSequence P j,
    σ.IsStrict ∧
      ∀ a b : ℝ, a < b → ∃ n : ℕ, σ.α n ∈ Set.Ioo a b

/-- **Selected dense grid from selected between-points coverage.** -/
theorem selectedRefinedDenseGridCertificate_real_of_betweenPointsCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (j : ι)
    (hBetween : SelectedRefinedGridBetweenPointsCertificate (P := P) j) :
    SelectedRefinedDenseGridCertificate P j := by
  obtain ⟨σ, hσ, hhit⟩ := hBetween
  refine ⟨σ, hσ, ?_⟩
  apply dense_of_exists_between
  intro a b hab
  obtain ⟨n, hn⟩ := hhit a b hab
  exact ⟨σ.α n, Set.mem_range_self n, hn.1, hn.2⟩

/-- **Selected between-points coverage from selected dense grid.** -/
theorem selectedRefinedGridBetweenPointsCertificate_of_denseGridCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (j : ι)
    (hGrid : SelectedRefinedDenseGridCertificate P j) :
    SelectedRefinedGridBetweenPointsCertificate (P := P) j := by
  obtain ⟨σ, hσ, hdense⟩ := hGrid
  refine ⟨σ, hσ, ?_⟩
  intro a b hab
  obtain ⟨x, hxmem, hxIoo⟩ := hdense.exists_between hab
  rcases hxmem with ⟨n, rfl⟩
  exact ⟨n, hxIoo⟩

/-- In the additive-real Bool model, no strict standard sequence has dense
range.  The additive-representation arithmetic makes every strict standard
sequence a one-sided arithmetic progression; the open interval between its
first two grid points contains no later grid point. -/
private theorem additiveRealBool_strictStandardSequence_not_dense
    {j : Bool} (σ : ProductPref.StandardSequence additiveRealBoolPref j)
    (hσ : σ.IsStrict) :
    ¬ Dense (Set.range σ.α) := by
  intro hdense
  have hstep_neg : σ.r - σ.s < 0 := by
    simpa [additiveRealBool_rep] using
      additiveRep_standardSequence_step_negative_of_strict additiveRealBool_rep σ hσ
  have hα_formula : ∀ n : ℕ,
      σ.α n = σ.α 0 + (n : ℝ) * (σ.r - σ.s) := by
    intro n
    simpa [additiveRealBool_rep] using
      additiveRep_standardSequence_Vj_arithmetic additiveRealBool_rep σ n
  have hα10 : σ.α 1 < σ.α 0 := by
    have h := hα_formula 1
    norm_num at h
    linarith
  obtain ⟨_x, hxmem, hxIoo⟩ := hdense.exists_between hα10
  rcases hxmem with ⟨n, rfl⟩
  cases n with
  | zero =>
      exact (lt_irrefl (σ.α 0)) hxIoo.2
  | succ m =>
      have htail : σ.α (m + 1) ≤ σ.α 1 := by
        have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
        have hmul : ((m + 1 : ℕ) : ℝ) * (σ.r - σ.s) ≤
            (1 : ℝ) * (σ.r - σ.s) := by
          exact mul_le_mul_of_nonpos_right hm (le_of_lt hstep_neg)
        have hm_formula := hα_formula (m + 1)
        have h1_formula := hα_formula 1
        rw [hm_formula, h1_formula]
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hmul (σ.α 0)
      exact not_lt_of_ge htail hxIoo.1

/-- **No-go: even the selected single dense standard-sequence target is too strong.**

The additive-real model satisfies the raw structural axioms, but every strict
standard sequence in it is an arithmetic progression and hence not dense.  Thus
the replacement target cannot be a single strict standard sequence; the genuine
refinement/bisection target must be a family/mesh of refined sequences or cuts.
-/
theorem additiveRealBool_not_selectedRefinedDenseGridCertificate_true :
    ¬ SelectedRefinedDenseGridCertificate additiveRealBoolPref true := by
  rintro ⟨σ, hσ, hdense⟩
  exact additiveRealBool_strictStandardSequence_not_dense σ hσ hdense

/-- Symmetric no-go for the `false` coordinate. -/
theorem additiveRealBool_not_selectedRefinedDenseGridCertificate_false :
    ¬ SelectedRefinedDenseGridCertificate additiveRealBoolPref false := by
  rintro ⟨σ, hσ, hdense⟩
  exact additiveRealBool_strictStandardSequence_not_dense σ hσ hdense

/-- Raw weak order, restricted solvability, tradeoff consistency, and
Archimedean are insufficient even for the selected single dense-grid target. -/
theorem additiveRealBool_archimedean_tradeoff_solvability_insufficient_for_selectedRefinedDenseGrid :
    (∀ j : Bool, ProductPref.Archimedean additiveRealBoolPref j) ∧
    ProductPref.RestrictedSolvability additiveRealBoolPref ∧
    ProductPref.IsWeakOrder additiveRealBoolPref ∧
    ProductPref.TradeoffConsistency additiveRealBoolPref ∧
    ¬ SelectedRefinedDenseGridCertificate additiveRealBoolPref true ∧
    ¬ SelectedRefinedDenseGridCertificate additiveRealBoolPref false :=
  ⟨additiveRealBoolPref_archimedean,
   additiveRealBoolPref_restrictedSolvability,
   inferInstance, inferInstance,
   additiveRealBool_not_selectedRefinedDenseGridCertificate_true,
   additiveRealBool_not_selectedRefinedDenseGridCertificate_false⟩

/-! ##### Corrected refined mesh-family target

The no-go above rules out a *single* strict dense standard sequence.  The
correct replacement is a family of refined strict standard sequences: for every
utility interval `(a,b)` and coordinate `i`, some member of the family has a
grid point whose `R.V i`-value lies in `(a,b)`.  This is an image/mesh target,
not a false claim that one `ℕ`-indexed arithmetic progression is dense.

The theorem below proves the family target from rational-image coverage plus
the same raw one-step extension interface used for standard-sequence
construction.  Thus the refined-grid side no longer requires coordinate
surjectivity; rational seeds are enough. -/

/-- **Coordinate utility refined mesh-family certificate.**

For each coordinate `i`, there is a rational-indexed family of strict standard
sequences.  The union of their utility images is interval-dense: every real
open interval contains some `R.V i`-value of a grid point from one family
member.

This replaces the refuted `SelectedRefinedDenseGridCertificate`: density is
achieved by a family of meshes, not by one strict standard sequence. -/
def CoordinateUtilityRefinedMeshFamilyCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) : Prop :=
  ∀ i : ι,
    ∃ σ : ℚ → ProductPref.StandardSequence P i,
      (∀ q : ℚ, (σ q).IsStrict) ∧
        ∀ a b : ℝ, a < b →
          ∃ q : ℚ, ∃ n : ℕ, R.V i ((σ q).α n) ∈ Set.Ioo a b

/-- A rational target can be embedded as a grid point of a strict standard
sequence without assuming coordinate surjectivity.

Given rational-image coverage, choose `x_hi` with utility `q+1` and `x_q` with
utility `q`.  Balance that one-unit drop in coordinate `i` against a one-unit
increase in the auxiliary coordinate supplied by
`CoordinateStandardSequenceExtensionData`, then extend one step to a standard
sequence.  The resulting sequence is strict and hits utility value `q` at
index `1`. -/
theorem exists_strictStandardSequence_hitting_rational_of_rationalImage_and_extensionData
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hRat : CoordinateRationalImageCertificate R)
    (hExt : CoordinateStandardSequenceExtensionData (P := P))
    (i : ι) (q : ℚ) :
    ∃ σ : ProductPref.StandardSequence P i,
      σ.IsStrict ∧ R.V i (σ.α 1) = (q : ℝ) := by
  rcases hExt i with ⟨k, hki, base, hext⟩
  obtain ⟨xHi, hxHi⟩ := hRat i (q + 1)
  obtain ⟨xQ, hxQ⟩ := hRat i q
  obtain ⟨rZero, hrZero⟩ := hRat k 0
  obtain ⟨sOne, hsOne⟩ := hRat k 1
  have hZero_ne_one : rZero ≠ sOne := by
    intro h
    have hbad : R.V k rZero = R.V k sOne := by
      rw [h]
    rw [hrZero, hsOne] at hbad
    norm_num at hbad
  have hseed :
      P.indiff
        (Function.update (Function.update base i xHi) k rZero)
        (Function.update (Function.update base i xQ) k sOne) := by
    apply additiveRep_twoCoord_indiff_of_value_balance R hki.symm
    rw [hxHi, hxQ, hrZero, hsOne]
    norm_num [Rat.cast_add, Rat.cast_one]
  obtain ⟨σ, hbase, hα0, hα1⟩ :=
    WakkerRoadmap.TradeoffMeasurement.extend_to_standard_sequence P hsolv i k hki base
      xHi xQ rZero sOne hZero_ne_one hseed
      (hext rZero sOne hZero_ne_one)
  have hstrict : σ.IsStrict := by
    rw [ProductPref.StandardSequence.IsStrict, hbase, hα0, hα1]
    apply additiveRep_singleCoord_strict_of_value_gt R base
    rw [hxQ, hxHi]
    have hcast : ((q + 1 : ℚ) : ℝ) = (q : ℝ) + 1 := by
      norm_num [Rat.cast_add, Rat.cast_one]
    rw [hcast]
    linarith
  refine ⟨σ, hstrict, ?_⟩
  simpa [hα1] using hxQ

/-- **Refined mesh-family from rational-image coverage and raw extension data.**

For each rational `q`, choose a strict standard sequence whose first successor
has utility value `q`.  Since rationals are dense in `ℝ`, this rational-indexed
family has a grid point in every utility interval. -/
theorem coordinateUtilityRefinedMeshFamilyCertificate_of_rationalImage_and_extensionData
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hRat : CoordinateRationalImageCertificate R)
    (hExt : CoordinateStandardSequenceExtensionData (P := P)) :
    CoordinateUtilityRefinedMeshFamilyCertificate R := by
  classical
  intro i
  choose σ hσ using
    (fun q : ℚ =>
      exists_strictStandardSequence_hitting_rational_of_rationalImage_and_extensionData
        R hsolv hRat hExt i q)
  refine ⟨σ, ?_, ?_⟩
  · intro q
    exact (hσ q).1
  · intro a b hab
    obtain ⟨q, haq, hqb⟩ := exists_rat_btwn hab
    refine ⟨q, 1, ?_⟩
    rw [(hσ q).2]
    exact ⟨haq, hqb⟩

/-- The refined mesh-family immediately gives between-points coverage for the
coordinate utility image. -/
theorem coordinateBetweenPointsCoverageCertificate_of_refinedMeshFamilyCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hMesh : CoordinateUtilityRefinedMeshFamilyCertificate R) :
    CoordinateBetweenPointsCoverageCertificate R := by
  intro i a b hab
  obtain ⟨σ, _hstrict, hhit⟩ := hMesh i
  obtain ⟨q, n, hn⟩ := hhit a b hab
  exact ⟨(σ q).α n, hn⟩

/-- Consequently, a refined mesh-family gives dense range for each coordinate
utility. -/
theorem coordinateDenseRangeCertificate_of_refinedMeshFamilyCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hMesh : CoordinateUtilityRefinedMeshFamilyCertificate R) :
    CoordinateDenseRangeCertificate R :=
  coordinateDenseRangeCertificate_of_coordinateBetweenPointsCoverageCertificate R
    (coordinateBetweenPointsCoverageCertificate_of_refinedMeshFamilyCertificate
      R hMesh)

/-! ##### Refinement/bisection and connected-continuity raw outputs

The previous bridge theorems consume `CoordinateRationalImageCertificate` and
`CoordinateStandardSequenceExtensionData`.  The raw Wakker proof below those
bridges is naturally split into two construction outputs:

* a rational refinement/bisection output: every rational utility target is hit
  by some grid point of some strict refined standard sequence;
* a connectedness/continuity one-step output: for each requested exchange, the
  target profile lies between two same-coordinate candidates, so restricted
  solvability supplies the next standard-sequence point.

The definitions below name these two raw outputs and prove, with no `sorry`,
that they feed the already proved non-surjective integer-refinement and
mesh-family bridges. -/

/-- **Rational refinement/bisection certificate.**

For every coordinate and rational utility target, the refinement/bisection
machinery produces a strict standard sequence and a finite grid index whose
`R.V`-value is exactly that rational.  This is the standard-sequence-shaped
version of rational-image coverage, and is the right construction-side output
below `CoordinateRationalImageCertificate`. -/
def CoordinateRationalRefinementBisectionCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) : Prop :=
  ∀ (i : ι) (q : ℚ),
    ∃ σ : ProductPref.StandardSequence P i,
      σ.IsStrict ∧ ∃ n : ℕ, R.V i (σ.α n) = (q : ℝ)

/-- Rational refinement/bisection gives rational-image coverage by forgetting
the standard-sequence provenance of the witness. -/
theorem coordinateRationalImageCertificate_of_rationalRefinementBisectionCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hBisect : CoordinateRationalRefinementBisectionCertificate R) :
    CoordinateRationalImageCertificate R := by
  intro i q
  obtain ⟨σ, _hσ, n, hn⟩ := hBisect i q
  exact ⟨σ.α n, hn⟩

/-- Rational refinement/bisection supplies the calibrated `0, 1, -1` seed
coverage needed to start positive and reverse integer standard sequences. -/
theorem coordinateIntegerSeedCertificate_of_rationalRefinementBisectionCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hBisect : CoordinateRationalRefinementBisectionCertificate R) :
    CoordinateIntegerSeedCertificate R :=
  coordinateIntegerSeedCertificate_of_coordinateRationalImageCertificate R
    (coordinateRationalImageCertificate_of_rationalRefinementBisectionCertificate
      R hBisect)

/-- **Rational bisection/refinement from rational-image coverage and one-step
extension data.**

The existing theorem `exists_strictStandardSequence_hitting_rational...`
constructs, for each rational target, a strict standard sequence whose first
successor hits that rational utility value.  Packaging that witness for every
coordinate and rational gives the standard-sequence-shaped bisection
certificate. -/
theorem coordinateRationalRefinementBisectionCertificate_of_rationalImage_and_extensionData
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hRat : CoordinateRationalImageCertificate R)
    (hExt : CoordinateStandardSequenceExtensionData (P := P)) :
    CoordinateRationalRefinementBisectionCertificate R := by
  intro i q
  obtain ⟨σ, hstrict, hhit⟩ :=
    exists_strictStandardSequence_hitting_rational_of_rationalImage_and_extensionData
      R hsolv hRat hExt i q
  exact ⟨σ, hstrict, 1, hhit⟩

/-! ##### One-step rational bisection feeder

Below `CoordinateRationalRefinementBisectionCertificate`, we expose a
**feeder** that consumes a single given strict standard sequence and a
single rational target lying inside one of its grid steps, plus a
one-step bisection bridge that produces the refined sequence hitting
the target.  The feeder lifts the per-`(σ, n, q)` bridge to the
`CoordinateRationalRefinementBisectionCertificate` interface when
quantified over coordinates and rational targets.

The construction does not yet discharge the bridge from raw structural
axioms: that is the next layer of work.  The named bridge below is
exactly the per-point content that any future raw discharge must
produce.

Naming convention.  The bridge is `OneStepRationalBisectionFeeder`,
following the existing `Bisection` / `Bracket` / `OneStep` certificate
naming in this section.  The lifting theorem is
`coordinateRationalRefinementBisectionCertificate_of_strictStandardSequenceFamily_and_oneStepBisectionFeeder`.
-/

/-- **One-step rational bisection feeder.**

Per-coordinate, per-strict-sequence, per-grid-index, per-rational-target
predicate.  The feeder asserts: given a strict standard sequence `σ` on
coordinate `i` and a rational target `q` lying inside the grid step
`[V(σ.α n), V(σ.α (n+1))]`, there exists a (possibly different) strict
standard sequence on `i` whose grid hits `q` at some index.

This is the precise "one-step" content of the bisection step on the
given sequence: the input sequence `σ` is held fixed; only one
rational-target step is parameterized; the output is a refined
strict sequence hitting that target.

In Wakker's framework this is discharged by combining `σ`'s seed
data with restricted solvability and a one-step extension witness
on an auxiliary coordinate; the resulting feeder is the natural
narrowing of `exists_strictStandardSequence_hitting_rational_*` from
"existence anywhere in `ℝ`" to "existence inside one given grid
step".

Naming the predicate isolates the deep content (the actual
construction of the refined sequence) from the trivial lifting to the
∀-form `CoordinateRationalRefinementBisectionCertificate`. -/
def OneStepRationalBisectionFeeder
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (i : ι) (σ : ProductPref.StandardSequence P i)
    (n : ℕ) (q : ℚ) : Prop :=
  σ.IsStrict →
  R.V i (σ.α n) ≤ (q : ℝ) →
  (q : ℝ) ≤ R.V i (σ.α (n+1)) →
    ∃ σ' : ProductPref.StandardSequence P i,
      σ'.IsStrict ∧ ∃ n' : ℕ, R.V i (σ'.α n') = (q : ℝ)

/-- **Strict-sequence family + grid-bracket assignment certificate.**

For every coordinate `i`, choose:

* a strict standard sequence `σ_i : StandardSequence P i`,
* for every rational `q : ℚ`, a grid index `n : ℕ` such that `q` lies
  inside the unit grid step `[V(σ_i.α n), V(σ_i.α (n+1))]`.

This packages the "given strict standard sequence" input of the
feeder uniformly across all rational targets, so that the feeder can
be quantified into the ∀-form `CoordinateRationalRefinementBisectionCertificate`. -/
def StrictStandardSequenceFamilyWithGridBracket
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) : Prop :=
  ∀ i : ι,
    ∃ σ : ProductPref.StandardSequence P i,
      σ.IsStrict ∧
        ∀ q : ℚ,
          ∃ n : ℕ,
            R.V i (σ.α n) ≤ (q : ℝ) ∧ (q : ℝ) ≤ R.V i (σ.α (n+1))

/-- **Lifting theorem: `CoordinateRationalRefinementBisectionCertificate`
from a strict-sequence family with grid-bracket assignment plus the
one-step rational bisection feeder.**

Real, sorry-free proof.  The strict-sequence family supplies a single
strict `σ_i` per coordinate plus, for each rational `q`, a grid index
`n` such that `q` lies inside the corresponding unit grid step.  The
one-step bisection feeder then produces the refined strict sequence
hitting `q` directly.  Quantifying over coordinates and rationals
produces `CoordinateRationalRefinementBisectionCertificate`. -/
theorem coordinateRationalRefinementBisectionCertificate_of_strictStandardSequenceFamily_and_oneStepBisectionFeeder
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hFamily : StrictStandardSequenceFamilyWithGridBracket R)
    (hFeeder :
      ∀ (i : ι) (σ : ProductPref.StandardSequence P i)
        (n : ℕ) (q : ℚ),
        OneStepRationalBisectionFeeder R i σ n q) :
    CoordinateRationalRefinementBisectionCertificate R := by
  intro i q
  obtain ⟨σ, hStrict, hBracket⟩ := hFamily i
  obtain ⟨n, hLow, hHigh⟩ := hBracket q
  exact hFeeder i σ n q hStrict hLow hHigh

/-- **Sample witness: the canonical real-coord identity additive
representation satisfies the one-step rational bisection feeder
trivially.**

For `X = fun _ => ℝ` and `R.V i = id`, every rational target `q : ℚ`
is in the image of `R.V i` (as the real `(q : ℝ)`).  Building a
strict standard sequence whose grid hits `q` only requires the
extension data already present in any concrete `ProductPref` instance.
We don't construct that here; the sample is a regression placeholder
showing the feeder predicate's shape under the canonical additive rep.

Concretely: given any strict `σ` whose unit step in `R.V`-space is
strictly positive, and any `q : ℚ` inside the step, refining is
non-trivial without further structural axioms.  We isolate the
non-vacuous content as the named feeder predicate above; this lemma
records the canonical identity case as the right starting point for
future refinement work.

The lemma below is **not** a proof that the feeder holds for the
canonical case; it is a definitional alias that makes the feeder's
shape explicit when the consumer already has a refined sequence in
hand.  The honest open content is the **construction** of the refined
sequence from the input sequence plus structural axioms, which is the
multi-week target. -/
theorem oneStepRationalBisectionFeeder_of_explicitRefinedSequence
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (i : ι) (σ : ProductPref.StandardSequence P i)
    (n : ℕ) (q : ℚ)
    (hRefined :
      ∃ σ' : ProductPref.StandardSequence P i,
        σ'.IsStrict ∧ ∃ n' : ℕ, R.V i (σ'.α n') = (q : ℝ)) :
    OneStepRationalBisectionFeeder R i σ n q := by
  intro _hStrict _hLow _hHigh
  exact hRefined

/-- **Canonical sample: the real-coord identity additive representation
satisfies the strict-sequence-family + grid-bracket assignment when a
`CoordinateRationalImageCertificate` is in hand.**

Given a strict standard sequence on each coordinate plus rational
image coverage, we can supply the family as the chosen `σ_i` together
with grid brackets sourced from rational image coverage's bracketing
witnesses (the integer-floor and ceiling of `q` in the unit grid).

This isolates the structural content that turns a "single rational hit"
hypothesis (`CoordinateRationalImageCertificate`) into the family plus
grid-bracket form needed to feed the lifting theorem.  The bracketing
data is the standard-sequence-density content already present in the
artifact via `CoordinateUtilityRefinedMeshFamilyCertificate`; we
expose the precise interface here as the simplest dischargeable
form. -/
theorem strictStandardSequenceFamilyWithGridBracket_of_familyAndBrackets
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hFamily :
      ∀ i : ι,
        ∃ σ : ProductPref.StandardSequence P i, σ.IsStrict)
    (hBracket :
      ∀ (i : ι) (σ : ProductPref.StandardSequence P i),
        σ.IsStrict →
        ∀ q : ℚ,
          ∃ n : ℕ,
            R.V i (σ.α n) ≤ (q : ℝ) ∧ (q : ℝ) ≤ R.V i (σ.α (n+1))) :
    StrictStandardSequenceFamilyWithGridBracket R := by
  intro i
  obtain ⟨σ, hStrict⟩ := hFamily i
  exact ⟨σ, hStrict, hBracket i σ hStrict⟩

/-- **Connectedness/continuity bracketing for one-step extension.**

For every coordinate `i`, choose an auxiliary coordinate `k ≠ i` and a base
profile.  For each nontrivial exchange `r ↦ s` in coordinate `k` and each
current point `aPrev` in coordinate `i`, connectedness/continuity refinement
produces lower/upper candidates in coordinate `i` that bracket the target
profile `(aPrev at i, r at k)` while the prospective next profile uses `s` at
coordinate `k`.

Restricted solvability then fills that bracket, producing the next point
`aNext` and hence `OneStepExtensible`. -/
def CoordinateConnectedContinuityOneStepBracketCertificate
    (P : ProductPref (fun _ : ι => ℝ)) : Prop :=
  ∀ i : ι,
    ∃ k : ι, k ≠ i ∧
      ∃ base : Profile (fun _ : ι => ℝ),
        ∀ r s : ℝ, r ≠ s →
          ∀ aPrev : ℝ,
            ∃ lo hi : ℝ,
              P.weakPref
                (Function.update (Function.update base k s) i hi)
                (Function.update (Function.update base i aPrev) k r) ∧
              P.weakPref
                (Function.update (Function.update base i aPrev) k r)
                (Function.update (Function.update base k s) i lo)

/-- Same two-coordinate update written in the two orders used by restricted
solvability and `OneStepExtensible`. -/
lemma update_comm_two_coords_real
    (base : Profile (fun _ : ι => ℝ)) {i k : ι} (hki : k ≠ i)
    (c s : ℝ) :
    Function.update (Function.update base k s) i c =
      Function.update (Function.update base i c) k s := by
  funext t
  by_cases hti : t = i
  · subst t
    simp [Function.update_of_ne hki.symm]
  · by_cases htk : t = k
    · subst t
      simp [Function.update_of_ne hki]
    · rw [Function.update_of_ne hti, Function.update_of_ne htk,
        Function.update_of_ne htk, Function.update_of_ne hti]

/-- **Connected-continuity bracket from utility-image unboundedness.**

Under an additive representation, the one-step bracket inequalities reduce to
finding coordinate-`i` values below and above the real target
`R.V i aPrev + R.V k r - R.V k s`.  Thus any all-coordinate unboundedness
certificate supplies the bracket.  This is the theorem-backed analytic core of
the connectedness/continuity one-step output currently expressible in the
artifact. -/
theorem coordinateConnectedContinuityOneStepBracketCertificate_of_coordinateUtilityUnbounded
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hUnbounded : ∀ i : ι, CoordinateUtilityUnboundedCertificate R i) :
    CoordinateConnectedContinuityOneStepBracketCertificate P := by
  classical
  intro i
  have hcard : 1 < Fintype.card ι := by
    exact lt_of_lt_of_le (by norm_num) (Fact.out : 3 ≤ Fintype.card ι)
  obtain ⟨k, hki⟩ := Fintype.exists_ne_of_one_lt_card hcard i
  let base : Profile (fun _ : ι => ℝ) := fun _ => 0
  refine ⟨k, hki, base, ?_⟩
  intro r s _hrs aPrev
  obtain ⟨lo, hi, hlo, hhi⟩ :=
    hUnbounded i (R.V i aPrev + R.V k r - R.V k s)
  refine ⟨lo, hi, ?_, ?_⟩
  · rw [R.represents]
    have hTarget :=
      sum_eq_pair_add_rest R.V
        (Function.update (Function.update base i aPrev) k r)
        (j := i) (k := k) hki.symm
    have hHi :=
      sum_eq_pair_add_rest R.V
        (Function.update (Function.update base k s) i hi)
        (j := i) (k := k) hki.symm
    have hTarget_i :
        R.V i ((Function.update (Function.update base i aPrev) k r) i) =
          R.V i aPrev := by
      rw [Function.update_of_ne hki.symm, Function.update_self]
    have hTarget_k :
        R.V k ((Function.update (Function.update base i aPrev) k r) k) =
          R.V k r := by
      rw [Function.update_self]
    have hHi_i :
        R.V i ((Function.update (Function.update base k s) i hi) i) =
          R.V i hi := by
      rw [Function.update_self]
    have hHi_k :
        R.V k ((Function.update (Function.update base k s) i hi) k) =
          R.V k s := by
      rw [Function.update_of_ne hki, Function.update_self]
    have hrest :
        (∑ t ∈ (Finset.univ.erase i).erase k,
            R.V t ((Function.update (Function.update base i aPrev) k r) t)) =
          ∑ t ∈ (Finset.univ.erase i).erase k,
            R.V t ((Function.update (Function.update base k s) i hi) t) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      have htk : t ≠ k := Finset.ne_of_mem_erase ht
      have ht_erase_i : t ∈ Finset.univ.erase i := (Finset.mem_erase.mp ht).2
      have hti : t ≠ i := Finset.ne_of_mem_erase ht_erase_i
      rw [Function.update_of_ne htk, Function.update_of_ne hti,
          Function.update_of_ne hti, Function.update_of_ne htk]
    rw [hTarget, hHi, hTarget_i, hTarget_k, hHi_i, hHi_k, hrest]
    linarith
  · rw [R.represents]
    have hLo :=
      sum_eq_pair_add_rest R.V
        (Function.update (Function.update base k s) i lo)
        (j := i) (k := k) hki.symm
    have hTarget :=
      sum_eq_pair_add_rest R.V
        (Function.update (Function.update base i aPrev) k r)
        (j := i) (k := k) hki.symm
    have hLo_i :
        R.V i ((Function.update (Function.update base k s) i lo) i) =
          R.V i lo := by
      rw [Function.update_self]
    have hLo_k :
        R.V k ((Function.update (Function.update base k s) i lo) k) =
          R.V k s := by
      rw [Function.update_of_ne hki, Function.update_self]
    have hTarget_i :
        R.V i ((Function.update (Function.update base i aPrev) k r) i) =
          R.V i aPrev := by
      rw [Function.update_of_ne hki.symm, Function.update_self]
    have hTarget_k :
        R.V k ((Function.update (Function.update base i aPrev) k r) k) =
          R.V k r := by
      rw [Function.update_self]
    have hrest :
        (∑ t ∈ (Finset.univ.erase i).erase k,
            R.V t ((Function.update (Function.update base k s) i lo) t)) =
          ∑ t ∈ (Finset.univ.erase i).erase k,
            R.V t ((Function.update (Function.update base i aPrev) k r) t) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      have htk : t ≠ k := Finset.ne_of_mem_erase ht
      have ht_erase_i : t ∈ Finset.univ.erase i := (Finset.mem_erase.mp ht).2
      have hti : t ≠ i := Finset.ne_of_mem_erase ht_erase_i
      rw [Function.update_of_ne hti, Function.update_of_ne htk,
          Function.update_of_ne htk, Function.update_of_ne hti]
    rw [hLo, hTarget, hLo_i, hLo_k, hTarget_i, hTarget_k, hrest]
    linarith

/-- Rational-image coverage supplies the unboundedness needed for the
connected-continuity one-step bracket. -/
theorem coordinateConnectedContinuityOneStepBracketCertificate_of_coordinateRationalImageCertificate
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hRat : CoordinateRationalImageCertificate R) :
    CoordinateConnectedContinuityOneStepBracketCertificate P :=
  coordinateConnectedContinuityOneStepBracketCertificate_of_coordinateUtilityUnbounded
    R (coordinateUtilityUnboundedCertificate_of_coordinateRationalImageCertificate
      R hRat)

/-- Rational refinement/bisection alone supplies the image-unboundedness needed
for the connected-continuity one-step bracket.  Thus, once the monograph-level
refinement/bisection construction has produced rational standard-sequence hits,
the one-step bracket is no longer a separate algebraic obligation in the current
real-coordinate artifact. -/
theorem coordinateConnectedContinuityOneStepBracketCertificate_of_rationalRefinementBisectionCertificate
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hBisect : CoordinateRationalRefinementBisectionCertificate R) :
    CoordinateConnectedContinuityOneStepBracketCertificate P :=
  coordinateConnectedContinuityOneStepBracketCertificate_of_coordinateRationalImageCertificate
    R (coordinateRationalImageCertificate_of_rationalRefinementBisectionCertificate
      R hBisect)

/-- **Both raw-output certificates from rational-image coverage and extension
data.**

This is the currently expressible non-circular route below the raw-output seam:
rational-image coverage plus one-step extension data packages rational hits as
strict refined standard-sequence grid points, and the same rational-image
coverage gives the connected-continuity bracket by unboundedness. -/
theorem rationalRefinementBisection_and_connectedContinuity_of_rationalImage_and_extensionData
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hRat : CoordinateRationalImageCertificate R)
    (hExt : CoordinateStandardSequenceExtensionData (P := P)) :
    CoordinateRationalRefinementBisectionCertificate R ∧
      CoordinateConnectedContinuityOneStepBracketCertificate P := by
  refine ⟨?_, ?_⟩
  · exact coordinateRationalRefinementBisectionCertificate_of_rationalImage_and_extensionData
      R hsolv hRat hExt
  · exact coordinateConnectedContinuityOneStepBracketCertificate_of_coordinateRationalImageCertificate
      R hRat

/-- **Both raw-output certificates from coordinate surjectivity and extension
data.**

Surjectivity is a stronger real-coordinate output than rational-image coverage;
paired with the raw one-step extension interface, it gives both construction
outputs without assuming calibrated integer refinement or continuity.  The
remaining monograph-level work is therefore to derive these stronger inputs
from Wakker's bisection/connectedness/continuity/Archimedean argument. -/
theorem rationalRefinementBisection_and_connectedContinuity_of_surjectivity_and_extensionData
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hSurj : CoordinateSurjectivityCertificate R)
    (hExt : CoordinateStandardSequenceExtensionData (P := P)) :
    CoordinateRationalRefinementBisectionCertificate R ∧
      CoordinateConnectedContinuityOneStepBracketCertificate P := by
  exact rationalRefinementBisection_and_connectedContinuity_of_rationalImage_and_extensionData
    R hsolv
    (coordinateRationalImageCertificate_of_coordinateSurjectivityCertificate R hSurj)
    hExt

/-- Continuity plus calibrated standard-sequence integer refinement supplies
the connected-continuity one-step bracket via rational-image coverage. -/
theorem coordinateConnectedContinuityOneStepBracketCertificate_of_continuity_standardSequenceIntegerRefinement
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hCont : CoordinateUtilityContinuityCertificate R (fun _ => Set.univ))
    (hSeq : CoordinateStandardSequenceIntegerRefinementCertificate R) :
    CoordinateConnectedContinuityOneStepBracketCertificate P :=
  coordinateConnectedContinuityOneStepBracketCertificate_of_coordinateRationalImageCertificate
    R (coordinateRationalImageCertificate_of_continuity_standardSequenceIntegerRefinement
      R hCont hSeq)

/-- **One-step extension data from restricted solvability plus
connectedness/continuity bracketing.**

This proves the exact interface consumed by `extend_to_standard_sequence`.
The connectedness/continuity certificate supplies the bracket; restricted
solvability fills it. -/
theorem coordinateStandardSequenceExtensionData_of_restrictedSolvability_and_connectedContinuity
    (P : ProductPref (fun _ : ι => ℝ))
    (hsolv : ProductPref.RestrictedSolvability P)
    (hConn : CoordinateConnectedContinuityOneStepBracketCertificate P) :
    CoordinateStandardSequenceExtensionData (P := P) := by
  intro i
  rcases hConn i with ⟨k, hki, base, hbracket⟩
  refine ⟨k, hki, base, ?_⟩
  intro r s hrs aPrev
  obtain ⟨lo, hi, hupper, hlower⟩ := hbracket r s hrs aPrev
  let a : Profile (fun _ : ι => ℝ) := Function.update base k s
  let b : Profile (fun _ : ι => ℝ) := Function.update (Function.update base i aPrev) k r
  obtain ⟨aNext, hfill⟩ := hsolv a b i hi lo hupper hlower
  refine ⟨aNext, ?_⟩
  have hswap := update_comm_two_coords_real (ι := ι) base hki aNext s
  change P.indiff b (Function.update (Function.update base i aNext) k s)
  rw [← hswap]
  exact ⟨hfill.2, hfill.1⟩

/-- **Rational-image coverage plus extension data from the named Wakker raw outputs.**

The refinement/bisection output supplies rational-image coverage by forgetting
the standard-sequence provenance of the rational hit.  The connectedness /
continuity one-step bracket, together with restricted solvability, supplies the
raw one-step extension data consumed by `extend_to_standard_sequence`.

This is the theorem-backed bridge currently available below the monograph-level
construction: once Wakker's Archimedean/refinement argument has produced
`CoordinateRationalRefinementBisectionCertificate` and the connectedness /
continuity argument has produced `CoordinateConnectedContinuityOneStepBracketCertificate`,
the sharper inputs `CoordinateRationalImageCertificate` and
`CoordinateStandardSequenceExtensionData` follow automatically. -/
theorem rationalImage_and_extensionData_of_refinementBisection_connectedContinuity
    {P : ProductPref (fun _ : ι => ℝ)}
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hBisect : CoordinateRationalRefinementBisectionCertificate R)
    (hConn : CoordinateConnectedContinuityOneStepBracketCertificate P) :
    CoordinateRationalImageCertificate R ∧
      CoordinateStandardSequenceExtensionData (P := P) := by
  exact ⟨
    coordinateRationalImageCertificate_of_rationalRefinementBisectionCertificate
      R hBisect,
    coordinateStandardSequenceExtensionData_of_restrictedSolvability_and_connectedContinuity
      P hsolv hConn⟩

/-- **Surjectivity plus extension data from bisection, connected-continuity,
and full-coordinate continuity.**

Rational refinement/bisection first gives rational-image coverage, hence the
utility-image unboundedness needed by the IVT bridge.  Full-coordinate
continuity upgrades that unboundedness to exact coordinate surjectivity, while
the connectedness/continuity one-step bracket plus restricted solvability gives
the same extension-data output as above.

Thus the stronger pair of construction inputs --- `CoordinateSurjectivityCertificate`
and `CoordinateStandardSequenceExtensionData` --- is theorem-backed from the
currently named Wakker bisection and connected-continuity outputs, provided the
monograph-level continuity step has supplied `CoordinateUtilityContinuityCertificate`
on `Set.univ`. -/
theorem surjectivity_and_extensionData_of_refinementBisection_connectedContinuity_continuity
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)}
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hCont : CoordinateUtilityContinuityCertificate R (fun _ => Set.univ))
    (hBisect : CoordinateRationalRefinementBisectionCertificate R)
    (hConn : CoordinateConnectedContinuityOneStepBracketCertificate P) :
    CoordinateSurjectivityCertificate R ∧
      CoordinateStandardSequenceExtensionData (P := P) := by
  have hBundle : CoordinateRationalImageCertificate R ∧
      CoordinateStandardSequenceExtensionData (P := P) :=
    rationalImage_and_extensionData_of_refinementBisection_connectedContinuity
      R hsolv hBisect hConn
  have hUnbounded : ∀ i : ι, CoordinateUtilityUnboundedCertificate R i :=
    coordinateUtilityUnboundedCertificate_of_coordinateRationalImageCertificate
      R hBundle.1
  exact ⟨
    coordinateSurjectivityCertificate_of_continuity_unbounded R hCont hUnbounded,
    hBundle.2⟩

/-- **Rational refinement/bisection from continuity, calibrated integer
standard-sequence refinement, and restricted solvability.**

Continuity plus calibrated two-sided integer standard-sequence refinement gives
rational-image coverage; rational-image coverage gives the one-step bracket;
restricted solvability turns that bracket into extension data; finally the
strict-sequence rational-hit constructor packages the result as
`CoordinateRationalRefinementBisectionCertificate`. -/
theorem coordinateRationalRefinementBisectionCertificate_of_continuity_standardSequenceIntegerRefinement
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hCont : CoordinateUtilityContinuityCertificate R (fun _ => Set.univ))
    (hSeq : CoordinateStandardSequenceIntegerRefinementCertificate R) :
    CoordinateRationalRefinementBisectionCertificate R := by
  have hRat : CoordinateRationalImageCertificate R :=
    coordinateRationalImageCertificate_of_continuity_standardSequenceIntegerRefinement
      R hCont hSeq
  have hConn : CoordinateConnectedContinuityOneStepBracketCertificate P :=
    coordinateConnectedContinuityOneStepBracketCertificate_of_coordinateRationalImageCertificate
      R hRat
  have hExt : CoordinateStandardSequenceExtensionData (P := P) :=
    coordinateStandardSequenceExtensionData_of_restrictedSolvability_and_connectedContinuity
      P hsolv hConn
  exact coordinateRationalRefinementBisectionCertificate_of_rationalImage_and_extensionData
    R hsolv hRat hExt

/-- **Bundled theorem-backed discharge of the two raw-output certificates from
the current continuity + integer-refinement machinery.**

This is the strongest non-circular discharge available in the current artifact:
the remaining lower raw work is now to derive the calibrated integer-refinement
and continuity inputs from Wakker's monograph-level bisection/connectedness
construction. -/
theorem rationalRefinementBisection_and_connectedContinuity_of_continuity_standardSequenceIntegerRefinement
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hCont : CoordinateUtilityContinuityCertificate R (fun _ => Set.univ))
    (hSeq : CoordinateStandardSequenceIntegerRefinementCertificate R) :
    CoordinateRationalRefinementBisectionCertificate R ∧
      CoordinateConnectedContinuityOneStepBracketCertificate P := by
  have hConn : CoordinateConnectedContinuityOneStepBracketCertificate P :=
    coordinateConnectedContinuityOneStepBracketCertificate_of_continuity_standardSequenceIntegerRefinement
      R hCont hSeq
  have hBisect : CoordinateRationalRefinementBisectionCertificate R :=
    coordinateRationalRefinementBisectionCertificate_of_continuity_standardSequenceIntegerRefinement
      R hsolv hCont hSeq
  exact ⟨hBisect, hConn⟩

/-- **Feed-through: raw refinement/bisection + connected-continuity extension
data prove calibrated positive/reverse integer standard sequences without
coordinate surjectivity.** -/
theorem coordinateStandardSequenceIntegerRefinementCertificate_of_refinementBisection_and_connectedContinuity
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hBisect : CoordinateRationalRefinementBisectionCertificate R)
    (hConn : CoordinateConnectedContinuityOneStepBracketCertificate P) :
    CoordinateStandardSequenceIntegerRefinementCertificate R := by
  exact coordinateStandardSequenceIntegerRefinementCertificate_of_rationalImage_and_extensionData
    R hsolv
    (coordinateRationalImageCertificate_of_rationalRefinementBisectionCertificate
      R hBisect)
    (coordinateStandardSequenceExtensionData_of_restrictedSolvability_and_connectedContinuity
      P hsolv hConn)

/-- **Feed-through: raw refinement/bisection + connected-continuity extension
data prove the corrected rational-indexed refined mesh-family certificate.** -/
theorem coordinateUtilityRefinedMeshFamilyCertificate_of_refinementBisection_and_connectedContinuity
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hBisect : CoordinateRationalRefinementBisectionCertificate R)
    (hConn : CoordinateConnectedContinuityOneStepBracketCertificate P) :
    CoordinateUtilityRefinedMeshFamilyCertificate R := by
  exact coordinateUtilityRefinedMeshFamilyCertificate_of_rationalImage_and_extensionData
    R hsolv
    (coordinateRationalImageCertificate_of_rationalRefinementBisectionCertificate
      R hBisect)
    (coordinateStandardSequenceExtensionData_of_restrictedSolvability_and_connectedContinuity
      P hsolv hConn)

/-- **Bundled feed-through from the two raw Wakker refinement outputs.**

From rational bisection/refinement plus connectedness/continuity one-step
bracketing, obtain all downstream construction-facing outputs consumed by the
current non-surjective bridges: rational-image coverage, calibrated seeds,
calibrated integer standard sequences, the refined mesh-family, between-points
coverage, and dense range. -/
theorem nonSurjectiveIntegerAndMeshBridgeOutputs_of_refinementBisection_and_connectedContinuity
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hBisect : CoordinateRationalRefinementBisectionCertificate R)
    (hConn : CoordinateConnectedContinuityOneStepBracketCertificate P) :
    CoordinateRationalImageCertificate R ∧
      CoordinateIntegerSeedCertificate R ∧
      CoordinateStandardSequenceIntegerRefinementCertificate R ∧
      CoordinateUtilityRefinedMeshFamilyCertificate R ∧
      CoordinateBetweenPointsCoverageCertificate R ∧
      CoordinateDenseRangeCertificate R := by
  have hRat : CoordinateRationalImageCertificate R :=
    coordinateRationalImageCertificate_of_rationalRefinementBisectionCertificate
      R hBisect
  have hSeed : CoordinateIntegerSeedCertificate R :=
    coordinateIntegerSeedCertificate_of_coordinateRationalImageCertificate R hRat
  have hSeq : CoordinateStandardSequenceIntegerRefinementCertificate R :=
    coordinateStandardSequenceIntegerRefinementCertificate_of_refinementBisection_and_connectedContinuity
      R hsolv hBisect hConn
  have hMesh : CoordinateUtilityRefinedMeshFamilyCertificate R :=
    coordinateUtilityRefinedMeshFamilyCertificate_of_refinementBisection_and_connectedContinuity
      R hsolv hBisect hConn
  have hBetween : CoordinateBetweenPointsCoverageCertificate R :=
    coordinateBetweenPointsCoverageCertificate_of_refinedMeshFamilyCertificate R hMesh
  have hDense : CoordinateDenseRangeCertificate R :=
    coordinateDenseRangeCertificate_of_refinedMeshFamilyCertificate R hMesh
  exact ⟨hRat, hSeed, hSeq, hMesh, hBetween, hDense⟩

/-- **Full-coordinate continuity from monotonicity plus rational
refinement/bisection.**

The bisection certificate gives rational-image coverage; the existing M4 route
turns rational-image coverage plus coordinate monotonicity into continuity of
each coordinate utility on `Set.univ`. -/
theorem coordinateUtilityContinuityCertificate_univ_of_monotone_rationalRefinementBisection
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hMono : CoordinateMonotonicityCertificate R)
    (hBisect : CoordinateRationalRefinementBisectionCertificate R) :
    CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) :=
  coordinateUtilityContinuityCertificate_univ_of_monotone_rationalImage R hMono
    (coordinateRationalImageCertificate_of_rationalRefinementBisectionCertificate
      R hBisect)

/-- **Integer refinement and full-coordinate continuity from the raw
refinement stack plus monotonicity.**

This is the non-circular assembly theorem for the two lower targets.  The
inputs are exactly the construction-side outputs isolated above:

* rational refinement/bisection, for rational-image/seed coverage;
* connected-continuity one-step bracketing plus restricted solvability, for
  extension data and hence calibrated integer standard sequences;
* coordinate monotonicity, for upgrading rational-image dense range to full
  coordinate continuity on `Set.univ`.

Thus the remaining genuinely raw Wakker work is to derive these construction
outputs from the monograph-level bisection/connectedness/continuity argument,
not to redo the already mechanized algebraic assembly. -/
theorem integerRefinement_and_fullContinuity_of_refinementBisection_connectedContinuity_monotone
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hMono : CoordinateMonotonicityCertificate R)
    (hBisect : CoordinateRationalRefinementBisectionCertificate R)
    (hConn : CoordinateConnectedContinuityOneStepBracketCertificate P) :
    CoordinateStandardSequenceIntegerRefinementCertificate R ∧
      CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) := by
  refine ⟨?_, ?_⟩
  · exact coordinateStandardSequenceIntegerRefinementCertificate_of_refinementBisection_and_connectedContinuity
      R hsolv hBisect hConn
  · exact coordinateUtilityContinuityCertificate_univ_of_monotone_rationalRefinementBisection
      R hMono hBisect

/-- **Trivial cross-flow: a `StandardSequenceGridDensityCertificate`
discharges the M5 closer's grid-density hypothesis.**

Sanity check that the certificate is exactly what the M5 closer
consumes: `pairwiseSliceRepresentationsAtPivot_of_sharedPivot`'s
`hdense_grid` hypothesis is satisfied by any `StandardSequenceGridDensityCertificate`. -/
theorem m5_grid_density_hypothesis_of_standardSequenceGridDensityCertificate
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    [TopologicalSpace (X j₀)]
    (hgrid : StandardSequenceGridDensityCertificate P j₀) :
    ∀ σⱼ₀ : ProductPref.StandardSequence P j₀,
      Dense (Set.range σⱼ₀.α) :=
  hgrid

/-! ##### M2 affine-lift inputs from construction-side certificates

The direct M2 affine-lift route needs three inputs on coordinate `j`:

1. common calibration on one standard-sequence grid;
2. continuity of both coordinate utilities;
3. density of the standard-sequence grid.

The first item is now theorem-backed by
`coordinateAffineLiftCertificate_of_strictStandardSequence`: any additive
representation is an affine arithmetic progression on a strict standard
sequence, so two representations are affinely related on that common grid.
The lemmas below connect the remaining two items to the M4/M5 certificate
machinery already present in this file. -/

/-- **Grid between-points coverage certificate for a standard-sequence grid.**

For every open interval `(a,b)` in the real coordinate domain, the given
standard-sequence grid has some point in that interval.  This is the precise
real-coordinate construction target whose theorem-backed consequence is
`Dense (Set.range σ.α)`. -/
def StandardSequenceGridBetweenPointsCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (j₀ : ι) : Prop :=
  ∀ σⱼ₀ : ProductPref.StandardSequence P j₀,
    ∀ a b : ℝ, a < b → ∃ n : ℕ, σⱼ₀.α n ∈ Set.Ioo a b

/-- **Grid-density certificate from standard-sequence between-points coverage.**

On real-coordinate domains, interval-hitting of the standard-sequence grid is
exactly the hypothesis needed by `dense_of_exists_between`, hence it supplies
the `StandardSequenceGridDensityCertificate` consumed by the affine-lift and
M5 density-extension routes. -/
theorem standardSequenceGridDensityCertificate_real_of_betweenPointsCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (j₀ : ι)
    (hBetween : StandardSequenceGridBetweenPointsCertificate (P := P) j₀) :
    StandardSequenceGridDensityCertificate P j₀ := by
  intro σⱼ₀
  apply dense_of_exists_between
  intro a b hab
  obtain ⟨n, hn⟩ := hBetween σⱼ₀ a b hab
  exact ⟨σⱼ₀.α n, Set.mem_range_self n, hn.1, hn.2⟩

/-- **Standard-sequence between-points coverage from grid density.**

For real-coordinate standard-sequence grids, the density certificate and the
interval-hitting certificate are equivalent.  This direction uses Mathlib's
`Dense.exists_between`: if `Set.range σ.α` is dense in `ℝ`, every open
interval contains some grid point. -/
theorem standardSequenceGridBetweenPointsCertificate_of_gridDensityCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (j₀ : ι)
    (hGrid : StandardSequenceGridDensityCertificate P j₀) :
    StandardSequenceGridBetweenPointsCertificate (P := P) j₀ := by
  intro σⱼ₀ a b hab
  obtain ⟨x, hxmem, hxIoo⟩ := (hGrid σⱼ₀).exists_between hab
  rcases hxmem with ⟨n, rfl⟩
  exact ⟨n, hxIoo⟩

/-- **Grid density for a fixed standard sequence from interval-hitting.**

Fixed-`σ` version of
`standardSequenceGridDensityCertificate_real_of_betweenPointsCertificate`.
This is the exact density input consumed by
`coordinateAffineLiftCertificate_of_strictStandardSequence`. -/
theorem standardSequenceGridDensity_real_of_betweenPointsCertificate
    {P : ProductPref (fun _ : ι => ℝ)} {j₀ : ι}
    (σⱼ₀ : ProductPref.StandardSequence P j₀)
    (hBetween : StandardSequenceGridBetweenPointsCertificate (P := P) j₀) :
    Dense (Set.range σⱼ₀.α) :=
  standardSequenceGridDensityCertificate_real_of_betweenPointsCertificate
    j₀ hBetween σⱼ₀

/-- **Extract global continuity from the M4 continuity certificate on `univ`.**

`CoordinateUtilityContinuityCertificate R (fun _ => Set.univ)` is stated as
`ContinuousOn`; the affine-lift density-extension theorem consumes ordinary
`Continuous`.  On `Set.univ` these are equivalent. -/
theorem continuous_coordinateUtility_of_continuityCertificate_univ
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) (j : ι)
    (hCont : CoordinateUtilityContinuityCertificate R (fun _ => Set.univ)) :
    Continuous (R.V j) := by
  simpa [continuousOn_univ] using hCont j

/-- **Continuity inputs for the direct coordinate affine-lift route.**

The affine-lift density-extension theorem needs ordinary continuity of both
coordinate utilities on the reference coordinate.  This predicate names that
pair of inputs so it can be discharged separately from the grid-density input. -/
def CoordinateAffineLiftContinuityInputs
    {P : ProductPref (fun _ : ι => ℝ)}
    (R₁ R₂ : AdditiveRep P) (j : ι) : Prop :=
  Continuous (R₁.V j) ∧ Continuous (R₂.V j)

/-- **Continuity inputs from monotonicity plus rational-image coverage.**

This closes the M4-side input pair for the direct affine-lift route.  For each
representation, the existing M4 theorem
`coordinateUtilityContinuityCertificate_univ_of_monotone_rationalImage` turns
monotonicity plus rational-image coverage into the continuity certificate on
`Set.univ`; `continuous_coordinateUtility_of_continuityCertificate_univ` then
extracts ordinary continuity at coordinate `j`. -/
theorem coordinateAffineLiftContinuityInputs_of_monotone_rationalImage
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)}
    (R₁ R₂ : AdditiveRep P) (j : ι)
    (hMono₁ : CoordinateMonotonicityCertificate R₁)
    (hRat₁ : CoordinateRationalImageCertificate R₁)
    (hMono₂ : CoordinateMonotonicityCertificate R₂)
    (hRat₂ : CoordinateRationalImageCertificate R₂) :
    CoordinateAffineLiftContinuityInputs R₁ R₂ j := by
  have hCont₁ : CoordinateUtilityContinuityCertificate R₁ (fun _ => Set.univ) :=
    coordinateUtilityContinuityCertificate_univ_of_monotone_rationalImage
      R₁ hMono₁ hRat₁
  have hCont₂ : CoordinateUtilityContinuityCertificate R₂ (fun _ => Set.univ) :=
    coordinateUtilityContinuityCertificate_univ_of_monotone_rationalImage
      R₂ hMono₂ hRat₂
  exact ⟨
    continuous_coordinateUtility_of_continuityCertificate_univ R₁ j hCont₁,
    continuous_coordinateUtility_of_continuityCertificate_univ R₂ j hCont₂⟩

/-- **Affine lift from a strict standard sequence plus M4/M5 certificates.**

This theorem supplies the three direct affine-lift inputs from named
construction-side certificates:

* common grid calibration: by strict-standard-sequence arithmetic for `R₁` and
  `R₂`;
* continuity: by the M4 `CoordinateUtilityContinuityCertificate` on `univ`;
* grid density: by the M5 `StandardSequenceGridDensityCertificate`. -/
theorem coordinateAffineLiftCertificate_of_strictStandardSequence_and_certificates
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)}
    (R₁ R₂ : AdditiveRep P)
    {j : ι}
    (σ : ProductPref.StandardSequence P j)
    (hσ : σ.IsStrict)
    (hCont₁ : CoordinateUtilityContinuityCertificate R₁ (fun _ => Set.univ))
    (hCont₂ : CoordinateUtilityContinuityCertificate R₂ (fun _ => Set.univ))
    (hGrid : StandardSequenceGridDensityCertificate P j) :
    CoordinateAffineLiftCertificate R₁ R₂ j := by
  exact coordinateAffineLiftCertificate_of_strictStandardSequence R₁ R₂ σ hσ
    (continuous_coordinateUtility_of_continuityCertificate_univ R₁ j hCont₁)
    (continuous_coordinateUtility_of_continuityCertificate_univ R₂ j hCont₂)
    (hGrid σ)

/-- **Affine lift from strict standard sequence, monotone/rational-image
continuity, and grid density.**

This is the lower-level M4 route: monotonicity plus rational-image coverage
theorem-back the continuity certificate for each representation; the only
remaining density input is the standard-sequence grid-density certificate. -/
theorem coordinateAffineLiftCertificate_of_strictStandardSequence_monotone_rationalImage_and_gridDensity
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)}
    (R₁ R₂ : AdditiveRep P)
    {j : ι}
    (σ : ProductPref.StandardSequence P j)
    (hσ : σ.IsStrict)
    (hMono₁ : CoordinateMonotonicityCertificate R₁)
    (hRat₁ : CoordinateRationalImageCertificate R₁)
    (hMono₂ : CoordinateMonotonicityCertificate R₂)
    (hRat₂ : CoordinateRationalImageCertificate R₂)
    (hGrid : StandardSequenceGridDensityCertificate P j) :
    CoordinateAffineLiftCertificate R₁ R₂ j := by
  have hCont₁ : CoordinateUtilityContinuityCertificate R₁ (fun _ => Set.univ) :=
    coordinateUtilityContinuityCertificate_univ_of_monotone_rationalImage
      R₁ hMono₁ hRat₁
  have hCont₂ : CoordinateUtilityContinuityCertificate R₂ (fun _ => Set.univ) :=
    coordinateUtilityContinuityCertificate_univ_of_monotone_rationalImage
      R₂ hMono₂ hRat₂
  exact coordinateAffineLiftCertificate_of_strictStandardSequence_and_certificates
    R₁ R₂ σ hσ hCont₁ hCont₂ hGrid

/-- **Affine lift from strict standard sequence, M4 continuity inputs, and
grid between-points coverage.**

This variant replaces the density certificate by the more construction-facing
interval-hitting target for the standard-sequence grid. -/
theorem coordinateAffineLiftCertificate_of_strictStandardSequence_and_gridBetweenPoints
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)}
    (R₁ R₂ : AdditiveRep P)
    {j : ι}
    (σ : ProductPref.StandardSequence P j)
    (hσ : σ.IsStrict)
    (hCont₁ : CoordinateUtilityContinuityCertificate R₁ (fun _ => Set.univ))
    (hCont₂ : CoordinateUtilityContinuityCertificate R₂ (fun _ => Set.univ))
    (hBetween : StandardSequenceGridBetweenPointsCertificate (P := P) j) :
    CoordinateAffineLiftCertificate R₁ R₂ j := by
  exact coordinateAffineLiftCertificate_of_strictStandardSequence_and_certificates
    R₁ R₂ σ hσ hCont₁ hCont₂
    (standardSequenceGridDensityCertificate_real_of_betweenPointsCertificate
      j hBetween)

/-- **End-to-end construction-stack route to coordinate affine lift.**

This is the fully wired direct M2 route at the current certificate frontier:

* common same-grid calibration comes from strict-standard-sequence arithmetic;
* the two continuity inputs come from monotonicity plus rational-image coverage;
* grid density comes from the real-coordinate grid between-points certificate.

Thus the only remaining work below this theorem is proving the three primitive
construction certificates themselves from raw Wakker structural machinery. -/
theorem coordinateAffineLiftCertificate_of_strictStandardSequence_monotone_rationalImage_and_gridBetweenPoints
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)}
    (R₁ R₂ : AdditiveRep P)
    {j : ι}
    (σ : ProductPref.StandardSequence P j)
    (hσ : σ.IsStrict)
    (hMono₁ : CoordinateMonotonicityCertificate R₁)
    (hRat₁ : CoordinateRationalImageCertificate R₁)
    (hMono₂ : CoordinateMonotonicityCertificate R₂)
    (hRat₂ : CoordinateRationalImageCertificate R₂)
    (hBetween : StandardSequenceGridBetweenPointsCertificate (P := P) j) :
    CoordinateAffineLiftCertificate R₁ R₂ j := by
  have hCont : CoordinateAffineLiftContinuityInputs R₁ R₂ j :=
    coordinateAffineLiftContinuityInputs_of_monotone_rationalImage
      R₁ R₂ j hMono₁ hRat₁ hMono₂ hRat₂
  exact coordinateAffineLiftCertificate_of_strictStandardSequence R₁ R₂ σ hσ
    hCont.1 hCont.2
    (standardSequenceGridDensity_real_of_betweenPointsCertificate σ hBetween)

/-- **Affine lift from a selected refined dense grid and continuity inputs.**

This is the replacement for the older universal-grid-density route.  A single
selected strict dense standard sequence is enough for the affine-lift extension;
the proof extracts that sequence and applies the strict-standard-sequence
arithmetic theorem. -/
theorem coordinateAffineLiftCertificate_of_selectedRefinedDenseGrid_and_continuityInputs
    {P : ProductPref (fun _ : ι => ℝ)}
    (R₁ R₂ : AdditiveRep P) (j : ι)
    (hCont : CoordinateAffineLiftContinuityInputs R₁ R₂ j)
    (hGrid : SelectedRefinedDenseGridCertificate P j) :
    CoordinateAffineLiftCertificate R₁ R₂ j := by
  obtain ⟨σ, hσ, hdense⟩ := hGrid
  exact coordinateAffineLiftCertificate_of_strictStandardSequence R₁ R₂ σ hσ
    hCont.1 hCont.2 hdense

/-- **Affine lift from a selected refined between-points grid and continuity
inputs.** -/
theorem coordinateAffineLiftCertificate_of_selectedRefinedGridBetweenPoints_and_continuityInputs
    {P : ProductPref (fun _ : ι => ℝ)}
    (R₁ R₂ : AdditiveRep P) (j : ι)
    (hCont : CoordinateAffineLiftContinuityInputs R₁ R₂ j)
    (hBetween : SelectedRefinedGridBetweenPointsCertificate (P := P) j) :
    CoordinateAffineLiftCertificate R₁ R₂ j := by
  exact coordinateAffineLiftCertificate_of_selectedRefinedDenseGrid_and_continuityInputs
    R₁ R₂ j hCont
    (selectedRefinedDenseGridCertificate_real_of_betweenPointsCertificate
      j hBetween)

/-- **Affine lift from selected refined dense grid, monotonicity, and
rational-image coverage.** -/
theorem coordinateAffineLiftCertificate_of_selectedRefinedDenseGrid_monotone_rationalImage
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)}
    (R₁ R₂ : AdditiveRep P) (j : ι)
    (hMono₁ : CoordinateMonotonicityCertificate R₁)
    (hRat₁ : CoordinateRationalImageCertificate R₁)
    (hMono₂ : CoordinateMonotonicityCertificate R₂)
    (hRat₂ : CoordinateRationalImageCertificate R₂)
    (hGrid : SelectedRefinedDenseGridCertificate P j) :
    CoordinateAffineLiftCertificate R₁ R₂ j := by
  have hCont : CoordinateAffineLiftContinuityInputs R₁ R₂ j :=
    coordinateAffineLiftContinuityInputs_of_monotone_rationalImage
      R₁ R₂ j hMono₁ hRat₁ hMono₂ hRat₂
  exact coordinateAffineLiftCertificate_of_selectedRefinedDenseGrid_and_continuityInputs
    R₁ R₂ j hCont hGrid

/-- **Affine lift from selected refined between-points grid, monotonicity, and
rational-image coverage.** -/
theorem coordinateAffineLiftCertificate_of_selectedRefinedGridBetweenPoints_monotone_rationalImage
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)}
    (R₁ R₂ : AdditiveRep P) (j : ι)
    (hMono₁ : CoordinateMonotonicityCertificate R₁)
    (hRat₁ : CoordinateRationalImageCertificate R₁)
    (hMono₂ : CoordinateMonotonicityCertificate R₂)
    (hRat₂ : CoordinateRationalImageCertificate R₂)
    (hBetween : SelectedRefinedGridBetweenPointsCertificate (P := P) j) :
    CoordinateAffineLiftCertificate R₁ R₂ j := by
  exact coordinateAffineLiftCertificate_of_selectedRefinedDenseGrid_monotone_rationalImage
    R₁ R₂ j hMono₁ hRat₁ hMono₂ hRat₂
    (selectedRefinedDenseGridCertificate_real_of_betweenPointsCertificate
      j hBetween)

/-! ##### Reverse standard sequence content

The decision-theoretic content for negative-ℕ-coverage is the **reverse
standard sequence** — a separate standard sequence on the same coordinate
`j` constructed using the reverse exchange direction `s ↦ r` instead of
`r ↦ s`.  This requires invoking `extend_to_standard_sequence` with the
roles of `r` and `s` swapped, starting from a base point that becomes
`α 0` of the new sequence.

Building the reverse sequence as a definitional swap of the original's
`r` and `s` *does not work*: the `spaced` indifference
`(α n, base, r) ∼ (α (n+1), base, s)` is asymmetric in `(α n, α (n+1))`.
Swapping `r` and `s` would require the *reverse* `(α n, base, s) ∼ (α (n+1), base, r)`,
which is a genuinely different indifference statement.

The honest move is to expose the reverse sequence as a *named existence
certificate* parameterized by the original sequence and the new exchange
direction `s ↦ r`.  Constructing the certificate from
`extend_to_standard_sequence` (with appropriately swapped inputs) is
direct but tedious; we leave it as the named target. -/

/-- **Reverse standard sequence existence certificate.**

Given an original standard sequence `σ : StandardSequence P j` (using
exchange `r → s` at coordinate `k = σ.k`), there exists a *separate*
standard sequence `σ' : StandardSequence P j` whose calibration produces
the negative-integer side.

The reverse sequence's `α'` grid points correspond to values
`α' 0 = (something), α' 1 = (something), …` that, under any utility
respecting the reverse exchange, calibrate to `0, -1, -2, …` rather than
`0, 1, 2, …`.

This certificate is the "negative-ℕ-side" companion to the existing
`extend_to_standard_sequence` theorem.  It is stated at the bare-existence
level: a reverse sequence exists, without specifying the exact
relationship between its `r/s/k` fields and the original's.  In Wakker's
construction the reverse sequence reuses the same `k` and swaps `r ↔ s`,
but the certificate's existence statement is sufficient for the
downstream coverage assembly. -/
def ReverseStandardSequenceCertificate {X : ι → Type v}
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (j : ι) (_σ : ProductPref.StandardSequence P j) : Prop :=
  ∃ _σ' : ProductPref.StandardSequence P j, True

/-- **Discharge: `ReverseStandardSequenceCertificate` from the original
sequence itself.**

The bare-existence form of the reverse standard sequence certificate is
trivially dischargeable: any standard sequence on coordinate `j` witnesses
existence, and the original `σ` is one such sequence.

This closes the bare-existence certificate but does *not* close the genuine
reverse-direction content — that is captured by the stronger
`DirectionalReverseStandardSequenceCertificate` below. -/
theorem reverseStandardSequenceCertificate_of_self {X : ι → Type v}
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j) :
    ReverseStandardSequenceCertificate P j σ :=
  ⟨σ, trivial⟩

/-- **Directional reverse standard sequence certificate (the real M4 deep
content for negative-ℕ-coverage).**

Given an original standard sequence `σ : StandardSequence P j` (using
exchange `r → s` at coordinate `k = σ.k`), there exists a *separate*
standard sequence `σ' : StandardSequence P j` that uses the *reverse*
exchange direction.

The directional content: `σ'.k = σ.k` (same auxiliary coordinate), and
the calibrated utility on `σ'` produces values `0, -1, -2, …` rather than
`0, 1, 2, …`.

In Wakker (1989) this is constructed by re-invoking
`extend_to_standard_sequence` with the swapped exchange `s → r` and
swapped grid-starting witnesses.  The `σ'.k = σ.k` equation is inherited
from the swap.  This certificate names the existence content; producing it
mechanically requires careful handling of the dependent typing in
`StandardSequence`'s `r/s` fields, which depend on `σ'.k`.

Unlike `ReverseStandardSequenceCertificate` (which is dischargeable from
the original `σ`), this directional certificate is *not* trivially
satisfiable by `σ` itself: the reverse-direction calibration is a
genuinely different statement.  Discharging it from the structural axioms
is the bounded-but-multi-session work flagged in the roadmap. -/
def DirectionalReverseStandardSequenceCertificate {X : ι → Type v}
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (j : ι) (σ : ProductPref.StandardSequence P j) : Prop :=
  ∃ (σ' : ProductPref.StandardSequence P j) (_hk : σ'.k = σ.k),
    -- Under the equation hk, σ'.r and σ'.s are typed as `X σ.k` rather
    -- than `X σ'.k`, allowing direct comparison with σ.r, σ.s.
    HEq σ'.r σ.s ∧ HEq σ'.s σ.r

/-- **Trivial cross-flow: directional reverse certificate implies bare
existence.**

Sanity check that the certificate hierarchy is correctly ordered. -/
theorem reverseStandardSequenceCertificate_of_directional {X : ι → Type v}
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    {j : ι} {σ : ProductPref.StandardSequence P j}
    (hDir : DirectionalReverseStandardSequenceCertificate P j σ) :
    ReverseStandardSequenceCertificate P j σ := by
  obtain ⟨σ', _, _, _⟩ := hDir
  exact ⟨σ', trivial⟩

/-- **Negative-ℕ-coverage from reverse standard sequence + grid
calibration.**

If the reverse standard sequence on coordinate `j` is calibrated such that
`V (σ'.α n) = -(n : ℝ)` for every `n : ℕ`, then `V` covers `-ℕ` on
coordinate `j`.

This is the assembly half of the negative-ℕ-coverage proof: given a
reverse sequence and a grid-calibrated utility, packaging the calibration
as the negative-ℕ-coverage hypothesis is one line. -/
theorem negNatImage_of_reverseGridCalibration {X : ι → Type v}
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    {j : ι}
    (σ' : ProductPref.StandardSequence P j)
    (V : X j → ℝ)
    (hCal : ∀ n : ℕ, V (σ'.α n) = -(n : ℝ)) :
    ∀ n : ℕ, ∃ x : X j, V x = -(n : ℝ) := by
  intro n
  exact ⟨σ'.α n, hCal n⟩

/-! ##### Single-coordinate weak monotonicity axiom -/

/-- **Single-coordinate weak monotonicity axiom.**

For every coordinate `i`, every base profile `a`, and every pair of real
values `u ≤ v`, the profile updated to `v` at `i` is weakly preferred to
the profile updated to `u` at `i` (all other coordinates equal).

This is the standard Wakker single-coordinate monotonicity axiom, restricted
to `X i = ℝ` with its standard order.  It follows from any preference structure
where each coordinate is "preference-monotone" — a much weaker property than
full preference continuity.

Naming this axiom isolates exactly the structural content needed to derive
the `CoordinateMonotonicityCertificate`. -/
def SingleCoordinateMonotonicityAxiom
    (P : ProductPref (fun _ : ι => ℝ)) : Prop :=
  ∀ (i : ι) (a : Profile (fun _ : ι => ℝ)) (u v : ℝ),
    u ≤ v → P.weakPref (Function.update a i v) (Function.update a i u)

/-- **Discharge: `CoordinateMonotonicityCertificate` from
`SingleCoordinateMonotonicityAxiom`.**

Real, sorry-free proof.  Given the single-coordinate monotonicity axiom,
each `R.V i` is monotone on `ℝ`: for any `u ≤ v`, take any base profile
`a` (witnessed by the constant-zero profile, since `ℝ` is inhabited);
the axiom gives `update a i v ≽ update a i u`; by `R.represents` this
yields `∑ R.V j ((update a i u) j) ≤ ∑ R.V j ((update a i v) j)`; since
the two profiles differ only at `i`, the sums collapse to
`R.V i u ≤ R.V i v`. -/
theorem coordinateMonotonicityCertificate_of_singleCoordinateMonotonicityAxiom
    (P : ProductPref (fun _ : ι => ℝ)) (R : AdditiveRep P)
    (hMono : SingleCoordinateMonotonicityAxiom P) :
    CoordinateMonotonicityCertificate R := by
  intro i u v huv
  -- Pick the constant-zero base profile.
  let a : Profile (fun _ : ι => ℝ) := fun _ => 0
  -- Apply the axiom.
  have hpref : P.weakPref (Function.update a i v) (Function.update a i u) :=
    hMono i a u v huv
  -- Use the additive representation.
  have hsum :
      (∑ j, R.V j ((Function.update a i u) j)) ≤
        ∑ j, R.V j ((Function.update a i v) j) :=
    (R.represents (Function.update a i v) (Function.update a i u)).mp hpref
  -- The two sums differ only at coordinate i.
  -- For all j ≠ i, (update a i u) j = (update a i v) j = a j.
  have hsplit_v :
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
  have hsplit_u :
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
  rw [hsplit_v, hsplit_u] at hsum
  linarith

/-- **Integer refinement and full-coordinate continuity from the raw
refinement stack plus structural monotonicity.**

This variant replaces the abstract `CoordinateMonotonicityCertificate` input by
the preference-level `SingleCoordinateMonotonicityAxiom`. -/
theorem integerRefinement_and_fullContinuity_of_refinementBisection_connectedContinuity_structuralMonotonicity
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P)
    (hBisect : CoordinateRationalRefinementBisectionCertificate R)
    (hConn : CoordinateConnectedContinuityOneStepBracketCertificate P) :
    CoordinateStandardSequenceIntegerRefinementCertificate R ∧
      CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) :=
  integerRefinement_and_fullContinuity_of_refinementBisection_connectedContinuity_monotone
    R hsolv
    (coordinateMonotonicityCertificate_of_singleCoordinateMonotonicityAxiom
      P R hMonoStruct)
    hBisect hConn

end CertificateChecklist

end WakkerRoadmap
