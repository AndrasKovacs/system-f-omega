
module Consistence where

open import Term hiding (η)
open import Type
open import Data.Empty

-- Unfortunately, it's not very impressive without the termination proof
-- for nf
consistence : Tm ε (∀' ⋆ (η vz)) → ⊥
consistence t with nf t
... | Λ ne ((vsₖ ()) , _)

