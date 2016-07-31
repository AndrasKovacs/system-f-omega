
module Examples where

open import Term hiding (η; _◇_)
open import Type hiding (add)
import Type as Ty

open import Relation.Binary.PropositionalEquality

⊢_ = Tm ε

id : ⊢ ∀' ⋆ (η vz ⇒ η vz)
id = Λ ƛ var vz

const : ⊢ ∀' ⋆ (∀' ⋆ (η (vs vz) ⇒ η vz ⇒ η (vs vz)))
const = Λ Λ ƛ ƛ var (vsₜ vz)

nat : ∀ {Γ} → Ty Γ ⋆
nat = ∀' ⋆ ((η vz ⇒ η vz) ⇒ η vz ⇒ η vz)

list : ∀ {Γ} → Ty Γ (⋆ ⇒ ⋆)
list = ƛ ∀' ⋆ ((η (vs vz) ⇒ η vz ⇒ η vz) ⇒ η vz ⇒ η vz)

zero : ⊢ nat
zero = Λ ƛ ƛ var vz

suc : ⊢ (nat ⇒ nat)
suc = ƛ Λ ƛ ƛ (var (vsₜ vz) ∙ (var (vsₜ vsₜ vsₖ vz) ∙ₜ η vz ∙ var (vsₜ vz) ∙ var vz))

one : ⊢ nat
one = suc ∙ zero

two : ⊢ nat
two = suc ∙ one

add : ⊢ (nat ⇒ nat ⇒ nat)
add = ƛ ƛ Λ ƛ ƛ (
  var (vsₜ vsₜ vsₖ vsₜ vz) ∙ₜ η vz ∙ var (vsₜ vz)
   ∙ (var (vsₜ vsₜ vsₖ vz) ∙ₜ η vz ∙ var (vsₜ vz) ∙ var vz)
  )

two' : Nf ε nat
two' = Λ (ƛ (ƛ ne ((vsₜ vz) , (ne ((vsₜ vz) , (ne (vz , ε) ∷ ε)) ∷ ε))))

test : nf two ≡ two'
test = refl

nil : ⊢ ∀' ⋆ (list ◇ (η vz ∷ ε))
nil = Λ (Λ (ƛ (ƛ var vz)))

cons : ⊢ ∀' ⋆ (η vz ⇒ (list ◇ (η vz ∷ ε)) ⇒ (list ◇ (η vz ∷ ε)))
cons = Λ ƛ ƛ Λ ƛ ƛ
  (var (vsₜ vz) ∙ var (vsₜ vsₜ vsₖ vsₜ vz)
  ∙ (var (vsₜ vsₜ vsₖ vz) ∙ₜ η vz ∙ var (vsₜ vz) ∙ var vz))

natList : ⊢ (list ◇ (nat ∷ ε))
natList =
  cons ∙ₜ nat ∙ one ∙
  (cons ∙ₜ nat ∙ two ∙
  (nil ∙ₜ nat))


