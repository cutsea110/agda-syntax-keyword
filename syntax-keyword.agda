-- http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Version-2-2-8
open import Data.Nat
open import Data.Unit using (⊤)


postulate
  State  : Set → Set → Set
  put    : ∀ {S} → S → State S ⊤
  get    : ∀ {S} → State S S
  return : ∀ {A S} → A → State S A
  bind   : ∀ {A B S} → State S B → (B → State S A) → State S A

syntax bind e₁ (λ x → e₂) = x ← e₁ , e₂

increment : State ℕ ⊤
increment = x ← get ,
            put (1 + x) -- x is in scope of e₂
