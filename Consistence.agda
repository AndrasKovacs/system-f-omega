
module Consistence where

open import Term hiding (η)
open import Type hiding (∀'_)
open import Data.Empty

∀' = λ {Γ} A → Ty.∀'_ {Γ}{A}

consistence : Tm ε (∀' ⋆ (η vz)) → ⊥
consistence t with nf t
... | Λ ne ((vsₖ ()) , _)

