
{-
fundamental operations on dependent contexts:
  - drop v Γ : drops the elements up to and including var "v" from "Γ"
  - subst v t Γ : removes variable "v" from the context and substitutes "t" for
    "v"-s occurrences in the "v"-dependent prefix of the context.

Note : "drop" generalizes to order-preserving embeddings, but "subst"

non-dependent context sub is the same as plain old _-_ thinning/removal

think about:
  context zippers?
  context splitting into a tail and a telescope?
  modeling dependent sub using higher-order telescope types?
  
-}

open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])
open import Data.Sum
open import Data.Product
import Function as F

data Ty : Set where
  ⋆   : Ty
  _⇒_ : Ty → Ty → Ty
infixr 2 _⇒_

data Con : Set where
  ε   : Con
  _▷_ : Con → Ty → Con
infixl 4 _▷_

data Ix : Con → Set where
  iz  : ∀ {Γ A} → Ix (Γ ▷ A)
  is_ : ∀ {Γ A} → Ix Γ → Ix (Γ ▷ A)

_[_] : ∀ Γ → Ix Γ → Ty
(Γ ▷ A) [ iz   ] = A
(Γ ▷ A) [ is i ] = Γ [ i ]

_∈_ : Ty → Con → Set
A ∈ Γ = ∃ λ i → Γ [ i ] ≡ A

data Tm (Γ : Con) : Ty → Set where
  var : ∀ {A} → A ∈ Γ → Tm Γ A
  ƛ_  : ∀ {A B} → Tm (Γ ▷ A) B → Tm Γ (A ⇒ B)
  _∙_ : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

mutual
  data Nf (Γ : Con) : Ty → Set where
    ƛ_  : ∀ {A B} → Nf (Γ ▷ A) B → Nf Γ (A ⇒ B)
    ne  : Ne Γ ⋆ → Nf Γ ⋆

  data Ne Γ : Ty → Set where
    _,_ : ∀ {A B} → A ∈ Γ → Sp Γ A B → Ne Γ B

  data Sp Γ : Ty → Ty → Set where
    ε   : ∀ {A} → Sp Γ A A
    _∷_ : ∀ {A B C} → Nf Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C

data _⊆_ : Con → Con → Set where
  stop : ε ⊆ ε
  add  : ∀ {A Γ Δ} → Γ ⊆ Δ → Γ ⊆ (Δ ▷ A)
  keep : ∀ {A Γ Δ} → Γ ⊆ Δ → (Γ ▷ A) ⊆ (Δ ▷ A)

id : ∀ {Γ} → Γ ⊆ Γ
id {ε}     = stop
id {Γ ▷ _} = keep id

subᶜ : ∀ {Γ} → Ix Γ → Con
subᶜ {Γ ▷ _} iz     = Γ
subᶜ {_ ▷ A} (is i) = subᶜ i ▷ A

drop : ∀ {Γ} → Ix Γ → Con
drop {Γ ▷ _} iz     = Γ
drop         (is i) = drop i

drop-sub-⊆ : ∀ {Γ}(i : Ix Γ) → drop i ⊆ subᶜ i
drop-sub-⊆ iz     = id
drop-sub-⊆ (is i) = add (drop-sub-⊆ i)

ren-Ix : ∀ {Γ Δ} → Γ ⊆ Δ → Ix Γ → Ix Δ
ren-Ix stop ()
ren-Ix (add  o) i      = is ren-Ix o i
ren-Ix (keep o) iz     = iz
ren-Ix (keep o) (is i) = is ren-Ix o i

ren-Ix' : ∀ {Γ Δ}(o : Γ ⊆ Δ)(i : Ix Γ) →  Δ [ ren-Ix o i ] ≡ Γ [ i ]
ren-Ix' stop ()
ren-Ix' (add o)  i      = ren-Ix' o i
ren-Ix' (keep o) iz     = refl
ren-Ix' (keep o) (is i) = ren-Ix' o i

ren-∈ : ∀ {Γ Δ A} → Γ ⊆ Δ → A ∈ Γ → A ∈ Δ
ren-∈ o (i , refl) = ren-Ix o i , ren-Ix' o i

mutual
  ren : ∀ {Γ Δ A} → Γ ⊆ Δ → Nf Γ A → Nf Δ A
  ren o (ƛ t)         = ƛ ren (keep o) t
  ren o (ne (v , sp)) = ne (ren-∈ o v , renSp o sp)

  renSp : ∀ {Γ Δ A B} → Γ ⊆ Δ → Sp Γ A B → Sp Δ A B
  renSp o ε        = ε
  renSp o (x ∷ sp) = ren o x ∷ renSp o sp


