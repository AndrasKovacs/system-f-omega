
module Consistence where

open import Term hiding (η)
open import Type
open import Data.Empty

consistence : Tm ε (∀' ⋆ (η vz)) → ⊥
consistence t with nf t
... | Λ ne ((vsₖ ()) , _)

