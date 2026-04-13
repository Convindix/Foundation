module

public import Foundation.FirstOrder.SetTheory.Basic.Hierarchy
public import Foundation.FirstOrder.SetTheory.Basic.Misc

@[expose] public section
/-!
# Fragments of set theory
-/

namespace LO.FirstOrder.SetTheory

/-! ### Kripke-Platek set theory -/
inductive KripkePlatek : Theory ℒₛₑₜ
  /-- Axiom of equality. -/
  | axiom_of_equality : ∀ φ ∈ 𝗘𝗤, KripkePlatek φ
  /-- Axiom of empty set. -/
  | axiom_of_empty_set : KripkePlatek Axiom.empty
  /-- Axiom of extentionality. -/
  | axiom_of_extentionality : KripkePlatek Axiom.extentionality
  /-- Axiom of pairing. -/
  | axiom_of_pairing : KripkePlatek Axiom.pairing
  /-- Axiom of union. -/
  | axiom_of_union : KripkePlatek Axiom.union
  /-- Axiom schema of induction. -/
  | axiom_of_induction (φ : SyntacticSemiformula ℒₛₑₜ 1) : KripkePlatek (Axiom.inductionSchema φ)
  /-- Axiom schema of separation, for `𝚺 0` formulas. -/
  | axiom_of_separation (φ : SyntacticSemiformula ℒₛₑₜ 1) : Hierarchy 𝚺 0 φ → KripkePlatek (Axiom.separationSchema φ)
  /-- Axiom schema of collection, for `𝚺 0` formulas. -/
  | axiom_of_collection (φ : SyntacticSemiformula ℒₛₑₜ 2) : Hierarchy 𝚺 0 φ → KripkePlatek (Axiom.collectionSchema φ)

notation "𝗞𝗣" => KripkePlatek

/-! ### Fragments of Zermelo-Fraenkel set theory -/
inductive ZermeloFraenkelFragment (n : ℕ) : Theory ℒₛₑₜ
  /-- Axiom of equality. -/
  | axiom_of_equality : ∀ φ ∈ 𝗘𝗤, ZermeloFraenkelFragment n φ
  /-- Axiom of empty set. -/
  | axiom_of_empty_set : ZermeloFraenkelFragment n Axiom.empty
  /-- Axiom of extentionality. -/
  | axiom_of_extentionality : ZermeloFraenkelFragment n Axiom.extentionality
  /-- Axiom of pairing. -/
  | axiom_of_pairing : ZermeloFraenkelFragment n Axiom.pairing
  /-- Axiom of union. -/
  | axiom_of_union : ZermeloFraenkelFragment n Axiom.union
  /-- Axiom of power set. -/
  | axiom_of_power_set : ZermeloFraenkelFragment n Axiom.power
  /-- Axiom of infinity. -/
  | axiom_of_infinity : ZermeloFraenkelFragment n Axiom.infinity
  /-- Axiom of foundation. -/
  | axiom_of_foundation : ZermeloFraenkelFragment n Axiom.foundation
  /-- Axiom schema of separation. -/
  | axiom_of_separation (φ : SyntacticSemiformula ℒₛₑₜ 1) : ZermeloFraenkelFragment n (Axiom.separationSchema φ)
  /-- Axiom schema of replacement, for `𝚺 n` formulas. -/
  | axiom_of_replacement (φ : SyntacticSemiformula ℒₛₑₜ 2) : Hierarchy 𝚺 n φ → ZermeloFraenkelFragment n (Axiom.replacementSchema φ)

notation "𝚺" n:arg "-𝗭𝗙" => ZermeloFraenkelFragment n

lemma zffragment_subset_zf (n : ℕ) : 𝚺 n-𝗭𝗙 ⊆ 𝗭𝗙 := by
  rintro φ ⟨h⟩
  · exact ZermeloFraenkel.axiom_of_equality φ (by assumption)
  · exact ZermeloFraenkel.axiom_of_empty_set
  · exact ZermeloFraenkel.axiom_of_extentionality
  · exact ZermeloFraenkel.axiom_of_pairing
  · exact ZermeloFraenkel.axiom_of_union
  · exact ZermeloFraenkel.axiom_of_power_set
  · exact ZermeloFraenkel.axiom_of_infinity
  · exact ZermeloFraenkel.axiom_of_foundation
  · exact ZermeloFraenkel.axiom_of_separation _
  · exact ZermeloFraenkel.axiom_of_replacement _

instance {n : ℕ} : 𝚺 n-𝗭𝗙 ⪯ 𝗭𝗙 := Entailment.WeakerThan.ofSubset (zffragment_subset_zf n)

end LO.FirstOrder.SetTheory
