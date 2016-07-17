module examples where

open import hsubst

-- λx.x
--
-- β-short and η-long
id○ : Tm ε (○ ⇒ ○)
id○ = Λ (var vz)

-- λx.λy.x y
--
-- β-short and η-long
id○⇒○ : Tm ε ((○ ⇒ ○) ⇒ (○ ⇒ ○))
id○⇒○ = Λ (Λ (app (var (vs vz)) (var vz)))

-- λx.x, different type
--
-- η-contraction of 'id○⇒○'
η-id○⇒○ : Tm ε ((○ ⇒ ○) ⇒ (○ ⇒ ○))
η-id○⇒○ = Λ (var vz)

-- (λx.x) (λx.x)
--
-- β-expansion of 'id○'
β-id○ : Tm ε (○ ⇒ ○)
β-id○ = app id○⇒○ id○

open import Relation.Binary.PropositionalEquality

-- Normalize into 'Tm', by normalizing into 'Nf' and then injecting
-- back into 'Tm'
n : forall {Γ τ} -> Tm Γ τ -> Tm Γ τ
n t = ⌈ nf t ⌉

-- 'β-id○' normalizes to 'id○'
eq1 : n β-id○ ≡ id○
eq1 = refl

-- ... and everything else normalizes to itself
eq2 : n id○ ≡ id○
eq2 = refl
eq3 : n id○⇒○ ≡ id○⇒○
eq3 = refl
-- Normal form is not η-long
eq4 : n η-id○⇒○ ≡ η-id○⇒○
eq4 = refl
