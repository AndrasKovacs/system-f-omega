
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

open import Relation.Binary.PropositionalEquality
open import Data.Sum
import Function as F

data Ty : Set where
  ⋆   : Ty
  _⇒_ : Ty → Ty → Ty
infixr 2 _⇒_

data Con : Set where
  ε   : Con
  _▷_ : Con → Ty → Con
infixl 4 _▷_

data _∈_ A : Con → Set where
  vz  : ∀ {Γ} → A ∈ (Γ ▷ A)
  vs_ : ∀ {B Γ} → A ∈ Γ → A ∈ (Γ ▷ B)

mutual
  data Tm Γ : Ty → Set where
    ƛ_ : ∀ {A B} → Tm (Γ ▷ A) B → Tm Γ (A ⇒ B)
    ne : Ne Γ ⋆ → Tm Γ ⋆

  data Ne Γ : Ty → Set where
    _,_ : ∀ {A B} → A ∈ Γ → Sp Γ A B → Ne Γ B

  data Sp Γ : Ty → Ty → Set where
    ε   : ∀ {A} → Sp Γ A A
    _∷_ : ∀ {A B C} → Tm Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C
  infixr 5 _∷_

data _⊆_ : Con → Con → Set where
  stop : ε ⊆ ε
  add  : ∀ {A Γ Δ} → Γ ⊆ Δ → Γ ⊆ (Δ ▷ A)
  keep : ∀ {A Γ Δ} → Γ ⊆ Δ → (Γ ▷ A) ⊆ (Δ ▷ A)

id : ∀ {Γ} → Γ ⊆ Γ
id {ε}     = stop
id {Γ ▷ _} = keep id

ren-∈ : ∀ {Γ Δ A} → Γ ⊆ Δ → A ∈ Γ → A ∈ Δ
ren-∈ stop ()
ren-∈ (add o)  v      = vs ren-∈ o v
ren-∈ (keep o) vz     = vz
ren-∈ (keep o) (vs v) = vs ren-∈ o v

mutual
  ren : ∀ {Γ Δ A} → Γ ⊆ Δ → Tm Γ A → Tm Δ A  
  ren o (ƛ t)         = ƛ (ren (keep o) t)
  ren o (ne (v , sp)) = ne ((ren-∈ o v) , renSp o sp)

  renSp : ∀ {Γ Δ A B} → Γ ⊆ Δ → Sp Γ A B → Sp Δ A B
  renSp o ε        = ε
  renSp o (x ∷ sp) = ren o x ∷ renSp o sp

drop : ∀ {Γ A} → A ∈ Γ → Con -- "drop Γ ⊆ Γ" always true
drop {Γ ▷ _} vz     = Γ
drop {Γ ▷ _} (vs v) = drop v

subᶜ : ∀ {Γ A} → A ∈ Γ → Con
subᶜ {Γ ▷ _} vz     = Γ
subᶜ {Γ ▷ A} (vs v) = subᶜ v ▷ A

drop-subᶜ-⊆ : ∀ {Γ A} (v : A ∈ Γ) → drop v ⊆ subᶜ v 
drop-subᶜ-⊆ vz     = id
drop-subᶜ-⊆ (vs v) = add (drop-subᶜ-⊆ v)

sub-∈ : ∀ {Γ A B}(v : A ∈ Γ)(v' : B ∈ Γ) → (A ≡ B) ⊎ (B ∈ subᶜ v)
sub-∈ vz     vz      = inj₁ refl
sub-∈ vz     (vs v') = inj₂ v'
sub-∈ (vs v) vz      = inj₂ vz
sub-∈ (vs v) (vs v') = map (λ z → z) vs_ (sub-∈ v v')

mutual
  sub : ∀ {Γ A B} → (v : A ∈ Γ) → Tm (drop v) A → Tm Γ B → Tm (subᶜ v) B
  sub v t' (ƛ t)  = ƛ sub (vs v) t' t
  sub v t' (ne (v' , sp)) with sub-∈ v v' | subSp v t' sp
  ... | inj₁ refl | sp' = ren (drop-subᶜ-⊆ v) t' ◇ sp'
  ... | inj₂ v''  | sp' = ne (v'' , sp')

  subSp : ∀ {Γ A B C} → (v : A ∈ Γ) → Tm (drop v) A → Sp Γ B C → Sp (subᶜ v) B C
  subSp v t' ε        = ε
  subSp v t' (t ∷ sp) = sub v t' t ∷ subSp v t' sp

  _◇_ : ∀ {Γ A B} → Tm Γ A → Sp Γ A B → Tm Γ B
  t     ◇ ε        = t
  (ƛ t) ◇ (x ∷ sp) = sub vz x t ◇ sp

extᵈ : ∀ {Γ Δ A}(v : A ∈ Γ) → drop v ⊆ Δ → Con
extᵈ {Γ ▷ A}{Δ} vz     o = Δ ▷ A
extᵈ {Γ ▷ A}    (vs v) o = extᵈ v o ▷ A

-- don't care yet
extᵈ-⊆ : ∀ {Γ Δ A}(v : A ∈ Γ)(o : drop v ⊆ Δ) → Γ ⊆ extᵈ v o
extᵈ-⊆ vz     o = keep o
extᵈ-⊆ (vs v) o = keep (extᵈ-⊆ v o)

extᶜ : ∀ {Γ Δ A}(v : A ∈ Γ) → drop v ⊆ Δ → Con
extᶜ {Γ ▷ _}{Δ} vz     o = Δ
extᶜ {Γ ▷ A}    (vs v) o = extᶜ v o ▷ A

extᶜ-⊆ : ∀ {Γ Δ A} (v : A ∈ Γ)(o : drop v ⊆ Δ) → subᶜ v ⊆ extᶜ v o
extᶜ-⊆ vz     o = o
extᶜ-⊆ (vs v) o = keep (extᶜ-⊆ v o)

mutual
  sub-ren :
    ∀ {Γ Δ A B}(v : A ∈ Γ)(o : drop v ⊆ Δ)(t' : Tm (drop v) A)(t : Tm Γ B)
    → ren (extᶜ-⊆ v o) (sub v t' t) ≡ {!sub (ren-∈ (extᵈ-⊆ v o) v) !}
  sub-ren = {!!}    
