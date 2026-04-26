/-
  RSF — Recursive Foundation / Well-Foundedness (Theorem T5)
  Pinnacle Quantum Group — April 2026

  Proves that RSF's Axiom 7 (Recursive Foundation) implies
  well-foundedness of the generation relation: no infinite
  descending chains of generation exist.
  Reference: RSF README §Axiom 7, RSSN LEMMA_DERIVATIONS.md
-/
import Mathlib

noncomputable section

namespace RSF.RecursiveFoundation

/-! ## 1. Generation Relation -/

structure FoundedSystem (α : Type*) where
  elements : Set α
  generate : α → Set α
  foundation : ∀ (S : Set α), S ⊆ elements → S.Nonempty →
    ∃ m ∈ S, ∀ x ∈ S, x ∉ generate m

def genRel (α : Type*) (sys : FoundedSystem α) : α → α → Prop :=
  fun x y => x ∈ sys.generate y

/-! ## 2. Well-Foundedness from Foundation Axiom -/

theorem foundation_implies_no_infinite_descent (α : Type*) (sys : FoundedSystem α)
    (chain : ℕ → α) (hchain : ∀ n, chain n ∈ sys.elements)
    (hdesc : ∀ n, chain (n + 1) ∈ sys.generate (chain n)) :
    False := by
  have hS : (Set.range chain).Nonempty := ⟨chain 0, Set.mem_range.mpr ⟨0, rfl⟩⟩
  have hSub : Set.range chain ⊆ sys.elements := by
    rintro _ ⟨n, rfl⟩; exact hchain n
  obtain ⟨m, ⟨k, rfl⟩, hm⟩ := sys.foundation (Set.range chain) hSub hS
  exact hm (chain (k + 1)) ⟨k + 1, rfl⟩ (hdesc k)

/-! ## 3. Foundation Implies Irreflexivity -/

theorem foundation_implies_irreflexive (α : Type*) (sys : FoundedSystem α)
    (x : α) (hx : x ∈ sys.elements) :
    x ∉ sys.generate x := by
  intro hgen
  have hS : ({x} : Set α).Nonempty := Set.singleton_nonempty x
  have hSub : ({x} : Set α) ⊆ sys.elements := Set.singleton_subset_iff.mpr hx
  obtain ⟨m, hm_mem, hm_prop⟩ := sys.foundation {x} hSub hS
  rw [Set.mem_singleton_iff] at hm_mem
  -- hm_mem : m = x; rewrite goal/hyp via hm_mem instead of subst (which can
  -- pick either direction in v4.5.0)
  exact hm_prop x (Set.mem_singleton x) (hm_mem ▸ hgen)

/-! ## 4. Foundation Implies Asymmetry -/

theorem foundation_implies_asymmetric (α : Type*) (sys : FoundedSystem α)
    (x y : α) (hx : x ∈ sys.elements) (hy : y ∈ sys.elements)
    (hxy : x ∈ sys.generate y) (hyx : y ∈ sys.generate x) :
    False := by
  have hS : ({x, y} : Set α).Nonempty := ⟨x, Set.mem_insert x {y}⟩
  have hSub : ({x, y} : Set α) ⊆ sys.elements := by
    intro a ha; rcases Set.mem_insert_iff.mp ha with rfl | h
    · exact hx
    · exact Set.mem_singleton_iff.mp h ▸ hy
  obtain ⟨m, hm_mem, hm_prop⟩ := sys.foundation {x, y} hSub hS
  -- Avoid `subst`/`rfl` patterns that pick the wrong direction in v4.5.0;
  -- use explicit ▸ rewriting instead.
  rcases Set.mem_insert_iff.mp hm_mem with hmx | h
  · -- hmx : m = x
    exact hm_prop y (Set.mem_insert_of_mem x (Set.mem_singleton y)) (hmx ▸ hyx)
  · rw [Set.mem_singleton_iff] at h
    -- h : m = y
    exact hm_prop x (Set.mem_insert x {y}) (h ▸ hxy)

/-! ## 5. Structural Induction Principle -/

theorem structural_induction (α : Type*) (sys : FoundedSystem α)
    (P : α → Prop)
    (hind : ∀ x ∈ sys.elements, (∀ y ∈ sys.generate x, y ∈ sys.elements → P y) → P x)
    (x : α) (hx : x ∈ sys.elements) : P x := by
  sorry

end RSF.RecursiveFoundation
