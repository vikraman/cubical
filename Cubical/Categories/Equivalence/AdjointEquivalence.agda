
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

open import Cubical.Categories.Adjoint
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Equivalence.Base
open import Cubical.HITs.PropositionalTruncation

module Cubical.Categories.Equivalence.AdjointEquivalence
  {ℓC ℓ'C : Level} {ℓD ℓ'D : Level}
  where

open UnitCounit

module _ (C : Category ℓC ℓ'C) (D : Category ℓD ℓ'D) where
  module _
    (fun : Functor C D) (inv : Functor D C)
    (η : 𝟙⟨ C ⟩ ≅ᶜ inv ∘F fun) (ε : fun ∘F inv ≅ᶜ 𝟙⟨ D ⟩)
    (triang : TriangleIdentities fun inv (NatIso.trans η) (NatIso.trans ε))
    where

    open TriangleIdentities triang
    private
      module C = Category C
      module D = Category D
      module fun = Functor fun
      module inv = Functor inv

    reverse-triangle : TriangleIdentities inv fun
                                          (NatIso.trans (symNatIso ε))
                                          (NatIso.trans (symNatIso η))
    reverse-triangle .TriangleIdentities.Δ₁ d =
        sym (C.⋆IdR _)
      ∙ cong (λ x → (  inv ⟪ NatIso.trans (symNatIso ε) ⟦ d ⟧ ⟫
                ⋆⟨ C ⟩ NatIso.trans (symNatIso η) ⟦ inv ⟅ d ⟆ ⟧)
                ⋆⟨ C ⟩ x)
             (sym (Δ₂ d))
      ∙ C.⋆Assoc _ _ _
      ∙ cong (λ x → inv ⟪ NatIso.trans (symNatIso ε) ⟦ d ⟧ ⟫ ⋆⟨ C ⟩ x)
             (sym $ C.⋆Assoc _ _ _)
      ∙ cong (λ x → inv ⟪ NatIso.trans (symNatIso ε) ⟦ d ⟧ ⟫ ⋆⟨ C ⟩
               (x ⋆⟨ C ⟩ inv ⟪ NatIso.trans ε ⟦ d ⟧ ⟫))
               (isIso.sec (NatIso.nIso η (inv ⟅ d ⟆)))
      ∙ cong (λ x → inv ⟪ NatIso.trans (symNatIso ε) ⟦ d ⟧ ⟫ ⋆⟨ C ⟩ x)
             (C.⋆IdL _)
      ∙ sym (inv.F-seq _ _)
      ∙ cong (λ x → inv ⟪ x ⟫) (isIso.sec (NatIso.nIso ε d))
      ∙ inv.F-id
    reverse-triangle .TriangleIdentities.Δ₂ c =
        sym (D.⋆IdL _)
      ∙ cong (λ x →   x
               ⋆⟨ D ⟩ (NatIso.trans (symNatIso ε) ⟦ fun ⟅ c ⟆ ⟧
               ⋆⟨ D ⟩ fun ⟪ NatIso.trans (symNatIso η) ⟦ c ⟧ ⟫))
             (sym (Δ₁ c))
      ∙ D.⋆Assoc _ _ _
      ∙ cong (λ x → fun ⟪ NatIso.trans η ⟦ c ⟧ ⟫ ⋆⟨ D ⟩ x)
             (sym $ D.⋆Assoc _ _ _)
      ∙ cong (λ x → fun ⟪ NatIso.trans η ⟦ c ⟧ ⟫ ⋆⟨ D ⟩
               (x ⋆⟨ D ⟩ fun ⟪ NatIso.trans (symNatIso η) ⟦ c ⟧ ⟫))
             (isIso.ret (NatIso.nIso ε (fun ⟅ c ⟆)))
      ∙ cong (λ x → fun ⟪ NatIso.trans η ⟦ c ⟧ ⟫ ⋆⟨ D ⟩ x) (D.⋆IdL _)
      ∙ sym (fun.F-seq _ _)
      ∙ cong (λ x → fun ⟪ x ⟫) (isIso.ret (NatIso.nIso η c))
      ∙ fun.F-id

  record AdjointEquivalence : Type (ℓ-max (ℓ-max ℓC ℓ'C) (ℓ-max ℓD ℓ'D)) where
    field
      fun : Functor C D
      inv : Functor D C
      η : 𝟙⟨ C ⟩ ≅ᶜ inv ∘F fun
      ε : fun ∘F inv ≅ᶜ 𝟙⟨ D ⟩
      triangleIdentities : TriangleIdentities fun inv (NatIso.trans η) (NatIso.trans ε)

    to≃ᶜ : C ≃ᶜ D
    _≃ᶜ_.func to≃ᶜ = fun
    _≃ᶜ_.isEquiv to≃ᶜ = ∣ record { invFunc = inv ; η = η ; ε = ε } ∣₁

module _
  {C : Category ℓC ℓ'C} {D : Category ℓD ℓ'D}
  (adj-equiv : AdjointEquivalence C D)
  where

  open AdjointEquivalence adj-equiv
  adjunction : fun ⊣ inv
  adjunction = record {
      η = NatIso.trans η
    ; ε = NatIso.trans ε
    ; triangleIdentities = triangleIdentities }

  reverse-adjunction : inv ⊣ fun
  reverse-adjunction = record {
      η = NatIso.trans (symNatIso ε)
    ; ε = NatIso.trans (symNatIso η)
    ; triangleIdentities = reverse-triangle C D fun inv η ε triangleIdentities }
